SRCS = $(wildcard *.py)
all: $(SRCS:.py=)

target: all

# Copy python files
%:%.py
	cp $< $@

# Package this all up for submission
tar: clean
	mkdir -p v00849637
	cp sud2sat.py sud2sat2.py sud2sat3.py sat2sud.py p096_sudoku.txt top95 testinput.txt testharness.py Makefile README.md CSC_322_Project_1.pdf v00849637/
	tar cvzf v00849637.tar.gz v00849637
# Test project
test:
	./kenken2smt.py < hard-puz.txt  >puz.smt
	mathsat<puz.smt > model.smt
	./smt2kenken.py < model.smt > sol.txt
	diff sol.txt hard-sol.txt

clean:
	rm -f puz.smt model.smt sol.txt
