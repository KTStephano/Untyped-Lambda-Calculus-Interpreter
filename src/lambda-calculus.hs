-- @author: Justin Hall (ktstephano)

import qualified Parselib as Parser
import System.IO
import System.IO.Unsafe
import System.Environment

{-
Term is supposed to represent
    Terms,t ::=    x       variable
             |     \x.t    abstraction
             |     t t     application
-}
data Term = Variable {name :: String} | Abstraction {argument :: String, body :: Term} |
    Application Term Term deriving (Eq)

-- Allows it to format the lambda calculus expressions properly
instance Show Term where
    show (Variable n) = n
    show (Abstraction n b) = "(\\" ++ n ++ ". " ++ show b ++ ")"
    show (Application a b@(Application _ _)) = show a ++ " (" ++ show b ++ ")"
    show (Application a b) = show a ++ " " ++ show b

-- Convenience functions
var :: String -> Term
var x = Variable x

lambda :: String -> Term -> Term
lambda a b = Abstraction a b

apply :: Term -> Term -> Term
apply a b = Application a b

-- For variable renaming, see https://crypto.stanford.edu/~blynn/lambda/
findAvailVarName :: String -> Int -> Term -> (String, Int)
findAvailVarName v index var@(Variable x) =
    if x == (v ++ show index) then findAvailVarName v (index + 1) var
    else ((v ++ show index), index)
findAvailVarName v index abs@(Abstraction n b) =
    if n == (v ++ show index) then findAvailVarName v (index + 1) abs
    else findAvailVarName v index b
findAvailVarName v index app@(Application a b) =
    let (_, newIndex) = findAvailVarName v index a in
        findAvailVarName v newIndex b

rename :: String -> String -> Term -> Term
rename x y (Variable v) = if x == v then var y else var v
rename x y (Abstraction arg body) = 
    if x == arg then Abstraction y (rename x y body) else Abstraction arg (rename x y body)
rename x y (Application a b) =
    apply (rename x y a) (rename x y b)

{-
Capture-avoiding substitution
        The idea is that (\x. t2) t1 ==> [x->t1]t2
        [x->s]x       = s
        [x->s]y       = y           if x /= y
        [x->s](\y.t1) = \y.t1       if y = x
                      = \y.[x->s]t1 if y /= x
        [x->s](t1 t2) = ([x->s]t1) ([x->s]t2)
    See page 70 of the Types And Programming Languages (TAPL) book.
-}
-- Note: t1 t2 is for [x->t1]t2
subst :: String -> Term -> Term -> Term
subst x t1 t2@(Variable n) =
    if (x == n) then t1 else t2
subst x t1 t2@(Abstraction n t) =
    if (x == n) then t2 else
    case t1 of
        (Variable v) -> if (v == n) then let newVar = fst $ findAvailVarName n 1 t2 in
                                            Abstraction newVar (subst x t1 (rename n newVar t))
                        else Abstraction n (subst x t1 t)
        _ -> Abstraction n (subst x t1 t)
    --else Abstraction n (subst x t1 t)
subst x t1 (Application a b) =
    Application (subst x t1 a) (subst x t1 b)

{-
Checking if a Term is a value
    Values,v ::= \x.t       abstraction value
-}
isValue :: Term -> Bool
isValue (Abstraction _ _) = True
isValue _ = False

{-
Single-step reduction
Implements normal reduction (hopefully), where the leftmost/outermost
is reduced first, and inner-function is done last
-}

eval1Normal :: Term -> Maybe Term
eval1Normal (Application a b) =
    -- If it's a value, then apply the last rule (axiom)
    if isValue a then Just $ subst (argument a) b (body a) else
        -- Otherwise attempt to reduce the left branch
        case (eval1Normal a) of
            Just t -> Just $ Application t b
            -- Finally, if all else failed, attempt to reduce the right branch
            Nothing -> case (eval1Normal b) of
                Just t' -> Just $ Application a t'
                Nothing -> Nothing
-- If we're down to just a function, go ahead and try and reduce it internally
eval1Normal (Abstraction arg functionBody) =
    case (eval1Normal functionBody) of
        Just t -> Just $ Abstraction arg t
        Nothing -> Nothing
eval1Normal _ = Nothing
{-
eval1Normal :: Term -> Maybe Term
eval1Normal (Application n@(Abstraction arg body) b) =
    case (eval1Normal b) of
        Just t -> Just $ Application n t
        Nothing -> Just $ subst arg b body
eval1Normal (Application a b) =
    case (eval1Normal b) of
        Just t -> Just $ Application a t
        Nothing -> Nothing
eval1Normal (Abstraction arg body) =
    case (eval1Normal body) of
        Just t -> Just $ Abstraction arg t
        Nothing -> Nothing
eval1Normal _ = Nothing
-}
{-
Repeatedly calls evan1Normal in a loop until it fails
-}
evalNormal :: Term -> Term
evalNormal t =
    case (eval1Normal t) of
        Just t' -> evalNormal t'
        Nothing -> t

-- Used to print out each step of eval1Normal
evalNormalDebug :: Term -> IO ()
evalNormalDebug t = do
    case (eval1Normal t) of
        Just t' -> do
            putStrLn (show t)
            evalNormalDebug t'
        Nothing ->
            putStrLn (show t)

{-
Extended: Read, Eval, Print Loop (REPL)

CITATION: See https://tadeuzagallo.com/blog/writing-a-lambda-calculus-interpreter-in-javascript/
          for the language grammar specification + explanation.

Rules:
            term ::= application
                    | lambda name . term

            application ::= application atom
                            | atom

            atom ::= left-paren term right-paren
                    | name
-}

-- Attempts to parse a left paren, then parser p, then
-- right paren, and fails if any of these steps don't work
unwrapParens :: Parser.Parser Term -> Parser.Parser Term
unwrapParens p =
    do
        Parser.symb "("
        x <- p
        Parser.symb ")"
        return x
        
-- Accepts variable names in alphanumeric form
varName :: Parser.Parser String
varName = 
    (do
        x <- Parser.alphanum
        v <- varName
        return (x:v)) Parser.+++
    (do
        x <- Parser.alphanum
        return [x])

-- Implements atom rule from above (also see article citation)
atom :: Parser.Parser Term
atom = unwrapParens term Parser.+++ do {v <- Parser.token varName; return $ var v}

-- Special variant of application' :: if we just implement the rule from
-- above as is, we'll end up with a (b c) instead of (a b) c, for example
application' :: Term -> Parser.Parser Term
application' term =
    (do
        a1 <- atom
        a2 <- application' (apply term a1)
        return a2) Parser.+++
    (do
        return term)

-- Implements full application defined in terms of atom and application'
application :: Parser.Parser Term
application =
    (do
        a1 <- atom
        a2 <- application' a1
        return a2) Parser.+++ atom

-- Parses terms as they are described by the rules above
term :: Parser.Parser Term
term = (do
        Parser.symb "\\"
        arg <- varName
        Parser.symb "."
        t <- term
        return $ lambda arg t) Parser.+++ application

-- If called, it will attempt to fully parse the string and convert
-- it to a single Term
applyFullParse :: Parser.Parser Term
applyFullParse = term Parser.+++ application Parser.+++ atom

-- EnvEntry is a variable -> Term mapping, i.e. c0 = \s. \z. z,
-- where "c0" is the variable and "\s. \z. z" is the Term
newtype EnvEntry = EnvEntry (String, Term) deriving (Show, Eq)
-- Stores all variable -> Term mappings that we know about at any one time
type Environment = [EnvEntry]

-- Takes a String and an Environment and returns Just Term if that variable exists
-- in the environment and Nothing otherwise
find :: String -> Environment -> Maybe Term
find var [] = Nothing
find var ((EnvEntry (s, t)):es) = if var == s then Just t else find var es

-- Removes a variable -> Term mapping from the environment, if it exists
remove :: String -> Environment -> Environment
remove var [] = []
remove var (e@(EnvEntry (s, t)):es) = if var == s then remove var es else e:(remove var es)

-- Attempts to parse things like "c0=\s. \z. z" and fails if this pattern
-- is not matched
parseEnvEntry :: Parser.Parser EnvEntry
parseEnvEntry = do
    name <- Parser.token varName
    Parser.symb "="
    term <- applyFullParse
    return $ EnvEntry (name, term)

-- Takes a Term and breaks it down so that every variable can be replaced
-- with an entry from the environment if necessary. For example, say the environment
-- contains [("s", \s. s t)] and the Term is \x. s x, then after calling this function
-- it will be \x. (\s. s t) x
replaceVarsWithEnvEntries :: Term -> Environment -> Term
replaceVarsWithEnvEntries var@(Variable v) env = case (find v env) of
    -- This recursively calls replaceVarsWithEnvEntries with t so that we
    -- can resolve all its dependencies as well
    Just t -> (replaceVarsWithEnvEntries t env)
    Nothing -> var
replaceVarsWithEnvEntries (Abstraction n t) env = Abstraction n (replaceVarsWithEnvEntries t env)
replaceVarsWithEnvEntries (Application t1 t2) env = Application (replaceVarsWithEnvEntries t1 env) (replaceVarsWithEnvEntries t2 env)

-- read, eval, print loop
repl' :: Environment -> IO ()
repl' env = do
    putStr ">> "
    hFlush stdout
    expr <- getLine
    case (Parser.apply parseEnvEntry expr) of
        [] -> case (Parser.apply applyFullParse expr) of
            [] -> do
                putStrLn "Syntax error in input"
                repl' env
            (t:_) -> do
                -- First need to check if there is text still on the stream. If so,
                -- full parse did not succeed.
                if length (snd t) > 0 then putStrLn "Syntax error in input"
                else do
                    let reducedForm = evalNormal $ replaceVarsWithEnvEntries (fst t) env
                    putStrLn (show reducedForm)
                repl' env
        -- This case triggers if parseEnvEntry succeeded, meaning the input was of
        -- the form t1 = t2
        ((e@(EnvEntry (s, t)), rest):_) -> do
            -- If there is still text left on the stream, applying a full parse failed
            -- so we should print an error and recurse with an unmodified environment
            if length rest > 0 then do
                putStrLn "Syntax error in input"
                repl' env
            else do 
                let newEnv = [e] ++ (remove s env)
                repl' newEnv

repl :: Environment -> IO ()
repl env = do
    putStrLn "Welcome to the untyped lambda calculus interactive interpreter"
    repl' env

main :: IO ()
main = repl []