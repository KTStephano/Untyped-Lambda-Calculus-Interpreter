# Untyped-Lambda-Calculus-Interpreter
This project uses the rules defined in "Types and Programming Languages" by Benjamin C. Pierce. Along with this, it uses Parselib written by Graham Hutton and Erik Meijer to parse string input. The actual parsing rules were lifted from https://tadeuzagallo.com/blog/writing-a-lambda-calculus-interpreter-in-javascript/.


## Running the interpreter (requires GHC)
You can either compile it or run it inside of GHCI. For example, to compile you can type:
```
  ghc -O3 -o lambda lambda-calculus.hs
```

This creates an executable called lambda (lambda.exe on Windows) compiled with -O3 optimization.

Inside of GHCI you can type:
```
  :l lambda-calculus.hs
  main
 ```
This will run the main function which drops you into the interactive interpreter loop.

## Examples
This codebase provides a simple implementation for an interactive interpreter for the untyped lambda calculus. Here are a few examples of what you can do with it while it's running:

(create a binding named c0 that maps to a lambda calculus expression)
```
>> c0=\s. \z. z
>> c0
(\s. (\z. z))
>> c0=(((\s. \z. ((z)))))
>> c0
(\s. (\z. z))
(Notice you can add your own parenthesis but it gets rid of all the redundant ones)
```

(perform application)
```
>> tru=\t. \f. t
>> tru c0
(\f. (\s. (\z. z)))
>> tru c0 x
(\s. (\z. z))
```

It is also partially lazy, so you can define recursive functions that get evaluated later.
```
>> recursive= ... recursive lambda expression ...
>> recursive x
(might or might not finish depending on what you wrote)
```
