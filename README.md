# Group Members
- Gavin Jaeger-Freeborn (V00849637)
- Ajiri Ogedegbe (V00882351)
- Ian Weber (V0092478)

# Files In This Repo
- smt2kenken.py
  - source code for converting the solutions produced by mathsat into
    a string of numbers to be inserted into the kenken puzzle
- kenken2smt.py
  - Source code for converting the text encoded kenken puzzle from
    `STDIN` into smt input for mathsat and printing it to `STDOUT`
- Makefile
  - Makefile used to convert the python files into executable without
    the .py prefix
  - Also contains additional scripts for running tests

# Building This Project
To build this project simply run `make` or `make target`

For examples of how to run this project look at the make targets for
`make test`
