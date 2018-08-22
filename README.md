# iditty

Tools for designing terminal UI applications in Idris. Exists because replWith isn't good enough for something like Rogue :)

## About

Probably gonna be a full-fledged library at some point. Right now it's just a bunch of trivial lemmas about rectangles...

## Introduction and design philosophy

There will be three components to this library:

* cross-platform terminal control and strongly-typed handling of terminfo databases
* cross-platform terminal emulation, supporting Linux (hopefully OSX as well), Windows 8, and Windows 10
* a small UI framework for terminal applications.

In Haskell-land, 1/2 would be vtty, the third is brick. Mine will be crappier, but dependendtly typed, sooo... :)

Since this is written in Idris, it is primarily a research project and should not be confused with production-level software. Even if I were a competent Idris developer.

### Benefits of strong typing in terminal applications

In my view, there are three common sticking points with applications that use text-based terminal UIs:

1) Gaps in cross-platform functionality cause e.g. an escape sequence to be sent to a stupid Windows 10 terminal that still has gaps and idiosyncracies in its implementation, or a 256-color function gets sent to a monochrome display and bugs out in unexpected ways. Generally cross-platform terminal control libraries in languages like C are simply confusing as hell. I am looking at you, ncurses.
   * By using dependent types and building to a Terminal interface, we can compile-time guarantee that the only terminal functions which are called are those which can be implemented on the corresponding terminal.

2) The developer has to do a lot of geometry in their head. Good constructors and good test coverage partially mitigates this, but it can be confusing to keep track of how GUI elements fit in a terminal window.
   * We introduce a Rectangle datatype, which allows a strongly-typed representation of rectangular tesselations of a "universe" rectangle. Among other things, these can be used to model non-overlapping textboxes and specified layers for things like drop-down menus. Separate GUI elements will never overlap due to a coordinate calculation error, text will never bleed over their textboxes, and in general we have much more security that any visual bugs are in the IO layer, not the GUI logic. At compile-time, you have protection against some classes of errors that, in ordinary languages, would be considered "visual" and hard to write even unit tests for.

3) A lack of flexibility in types means that often developers have to hack into things like ncurses or bearlibterminal to get what they want. Using a language like Idris - or indeed, Haskell, Lisp, etc - allows for substantially more generic code and substantially more flexible interoperation with your business logic.

## Plan of action

In the very near-term:

* finish UI framework with
  * RectangularAreas of text boxes
  * Images of ASCII graphics
* finish FFI work with C backend to winterm

In the medium term:

* start FFI work with SDL and JavaScript
* colors
* menus

Long term:

* Linux/MacOs
* curses???? [probably not :)]
* sample text editor and roguelike