# An Experimental Haskell Debugger

This is an experiment to build a Haskell debuggger. It starts the compiled program in a new process. Every time when a new Haskell function is entered, the debugger gets notified. The closure for the function is decoded and sent to the debugger. The closure is represented by using the types in the ghc-heap package.


