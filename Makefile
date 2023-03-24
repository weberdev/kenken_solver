SRCS = $(wildcard *.py)

all: $(SRCS:.py=)

target: all

# Copy python files for removing the .py from the file name
%:%.py
	cp $< $@

# Package this all up for submission
tar: clean
	mkdir -p v00849637
	cp *.py \
		hard-puz.txt hard-sol.txt\
		Makefile\
		README.md\
		CSC_322_Project_2.pdf\
		v00849637/
	tar cvzf v00849637.tar.gz v00849637

# Test project
test: smt2kenken kenken2smt
	./kenken2smt < hard-puz.txt | mathsat | ./smt2kenken > sol.txt
	diff sol.txt hard-sol.txt

# Test the pretty printer
testpp: pp
	diff <(./pp 22597) <(./pp < hard-puz.txt)

# Usage examples for the pretty printer
examplepp: pp
	./pp 22597
	./pp < hard-puz.txt

clean:
	rm -f pp kenken2smt smt2kenken
