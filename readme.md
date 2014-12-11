
Z3 - SML binding
================================================


This library provides Z3 library binding for StandardML implementations.


Support
--------------------------------

Currently, SML# 2.0.0 is only supported.
This library use Z3 functions of libz3.so throught C API.


Build
--------------------------------

Just type `make` in this directory.


How to Use
--------------------------------

+ add *\_require "z3.smi"* to your .smi file
  of your project which using this library.

    (* foo.smi *)
    \_require "z3.smi"
    
    (* foo.sml *)
    open Z3
    fun bar () = ...


+ build your project with the compiler switch _-I<path/to/dir/containts/z3.smi>_

    $ smlsharp -I/path/to/z3sml -o foo foo.sml


Supported Version
--------------------------------

*v4.3.2* is supported.


Link
--------------------------------

- [Z3](http://z3.codeplex.com/ "z3 official site")
- [Z3 C API](http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html "C API reference")
- [SML#](http://www.pllab.riec.tohoku.ac.jp/smlsharp/ "SML# project")


