
Z3 - StandardML binding
================================================


This library provides Z3 library binding for StandardML implementations.


Status
--------------------------------


- **Almost every C API** functions/variables are exported as SML functions/variables !
- Deprecated API is also exported. But using these API is not recommended.
- Only very thin SML wrapper is provided. So, you should use Z3 on very low layer like C.


Supported SML System
--------------------------------

Currently, SML# 2.0.0 is only supported.
This library use Z3 functions of libz3.so throught C API.


Supported Version
--------------------------------

Z3 *v4.3.2* is supported.


Build
--------------------------------

Just type `make` in the top directory of z3sml project.


How to Use
--------------------------------

+ install z3(libz3.so) to your system

+ add *\_require "z3.smi"* to your .smi file
  of your project which using this library.

    (* foo.smi \*)
    \_require "z3.smi"
    
    (* foo.sml \*)
    open Z3
    fun bar () = ...


+ build your project with the compiler switch _-I<path/to/dir/containts/z3.smi>_

    $ smlsharp -I/path/to/z3sml -o foo foo.sml


Sample
--------------------------------

Sample program using z3/sml# binding is provided as sample/sample.sml .
This sample code is written as much like the C example as possible.
Where the **C example** code is provided within z3 official distribution.


For building and running sample program:

    $ make sample



Link
--------------------------------

- [Z3](http://z3.codeplex.com/ "z3 official site")
- [Z3 C API](http://research.microsoft.com/en-us/um/redmond/projects/z3/code/group__capi.html "C API reference")
- [SML#](http://www.pllab.riec.tohoku.ac.jp/smlsharp/ "SML# project")


