all:
	./kenken2smt.py < hard-puz.txt  >puz.smt
	mathsat<puz.smt > model.smt
	./smt2kenken.py < model.smt > sol.txt
	diff sol.txt hard-sol.txt
clean:
	rm -f puz.smt model.smt sol.txt
