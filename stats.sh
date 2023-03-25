#!/bin/sh

# # Testing
# for line in $(find ../7/ -name "*puzzle.txt"); do
#     cat $line | ./kenken2smt.py  >puz.smt
#     mathsat<puz.smt > model.smt
#     ./smt2kenken.py < model.smt > sol.txt
#     diff <(tail -n 1 $(echo $line | sed "s/puzzle/solution/")) sol.txt
# done

# Benchmarking
for line in $(find ../7/adms/easiest -name "*puzzle.txt"| shuf | sed 30q); do
    printf ":current-file %s\n" $line
    cat $line | ./kenken2smt.py | mathsat -stats | grep ":" | grep -v " 0"
done > easiest.txt

for line in $(find ../7/adms/easy/ -name "*puzzle.txt"| shuf | sed 30q); do
    printf ":current-file %s\n" $line
    cat $line | ./kenken2smt.py | mathsat -stats | grep ":" | grep -v " 0"
done > easy.txt

for line in $(find ../7/adms/medium/ -name "*puzzle.txt"| shuf | sed 30q); do
    printf ":current-file %s\n" $line
    cat $line | ./kenken2smt.py | mathsat -stats | grep ":" | grep -v " 0"
done > medium.txt

for line in $(find ../7/adms/hard/ -name "*puzzle.txt"| shuf | sed 30q); do
    printf ":current-file %s\n" $line
    cat $line | ./kenken2smt.py | mathsat -stats | grep ":" | grep -v " 0"
done > hard.txt

