# This is the README file for Proto-Quipper.

Prerequisites
=============

The following are required to compile Proto-Quipper:

* The GHC Haskell compiler (tested with version 7.4.2)

* Alex and Happy (lexer and parser for Haskell)

* The Haskell readline library.  Note: this is not required on the
  Windows operating system. On all other operating systems, it can be
  installed with:

  cabal install readline

Building
========

In the top-level directory, type "make".

Description
===========

Synopsis: ProtoQuipper [OPTION] .. [FILE] ..
  Types and interprets FILEs, or if no FILE is given, run the interactive mode.

-t, --type
    don't run the interpreter.

-r, --run
    run the interpret (default mode).

-f FORMAT, --format=FORMAT
    change the circuit output format. Implemented formats are
      * "visual": display the circuit on the standard output
      * "ir": print the Intermediate Representation of the circuit

-i DIR, --include=DIR
    include the directory

-h, --help
    display this help and exit

-V, --version
    output version and exit

-v [LVL], --verbose[=LVL]
    change the verbose level


Interactive Mode
================

The interactive mode accepts the commands:

:help              -- Show the list of commands
:exit              -- Quit the interactive mode
:path <dir>        -- Add a directory to the current module path
:type <exp>        -- Show the type of an expression
:fulltype <expr>   -- Show the type of an expression, along with the associated constraints
:context           -- List the variables of the current context
:display           -- Display the toplevel circuit
:value             -- Display the value of one or more variables

User guide
==========

For a tutorial introduction to Proto-Quipper, see Section 8,
"Proto-Quipper user guide", of the Proto-Quipper report.


Browsing the documentation and source code
==========================================

While it is possible the browse the source code of the Proto-Quipper
implementation in a text editor, it is much nicer to browse the
documented source by pointing your web browser to doc/frames.html in
this Proto-Quipper distribution. The documented source is fully
cross-referenced and indexed, with links to color-coded raw source
files.

The distribution also contains object code examples, written in
Proto-Quipper. These can be found in the directories qlib and bwt.


Building the documentation
==========================

If the programs "haddock" and "HsColour" are installed, the
documentation can be built with "make haddock".


Emacs mode
==========

A very basic emacs editing mode for Proto-Quipper files (file
extension .qp) is located in the emacs directory. It currently does
nothing but some syntax coloring.


Frequently asked questions
==========================

Q: Why do you use the acronym "QP" and not "PQ"?

A: Some of the Proto-Quipper implementors are from France, where "PQ"
apparently is a vulgar term for "toilet paper". (Among French speakers
in Canada, there are no such sensitivities, as PQ is the acronym for a
well-known political party here).


Contact
=======

For support, please contact Peter Selinger <selinger@mathstat.dal.ca>.
