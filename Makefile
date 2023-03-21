all:
	./kenken2smt.py < hard-puz.txt  >puz.smt
	mathsat<puz.smt > model.smt
	./smt2kenken.py < model.smt
