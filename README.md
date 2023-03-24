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

- pp.py
  - Source code for the pretty print it takes a puzzle ID as an
    argument. If no ID is provided it will accept a puzzle on
    `STDIN`.
  - The puzzle text is then scanned for an for a PUZZLE ID in a
    comment on the first line. Similar to the format seen in the
    example puzzle files provided. If no comment indicating the
    puzzle's ID `pp` will simply print an error since no solution can
    be printed.
  - for example it could be ran like this
  ```bash
  ./pp 22597
  ```
  or it could be ran with the raw puzzle input as long as it contains
  a comment like this:
  ```
  #kenken www.kenkenpuzzle.com Puzzle 22597 7x7 Hard
  ```
  for example if we used the `hard-puz.txt` file we would run:
  ```bash
  ./pp < hard-puz.txt
  ```

- Makefile
  - Makefile used to convert the python files into executable without
    the .py prefix
  - Also contains additional scripts for running tests

# Building This Project
To build this project simply run `make` or `make target`

For examples of how to run this project look at the make targets for
`make test`
