#!/usr/bin/env python3

from itertools import count
from sys import stdin
from typing import Tuple, Union, List
import re
import operator

#I received this code in a dream:
#by which I mean I looked up how to do it: there's an operators library in python.
operators = {'+': operator.add, '-': operator.sub, '*': operator.mul, '/': operator.truediv}

class cage:
    def __init__(self, number, total, operator):
        self.number = number
        self.total = total
        self.operator = operator
        self.cellPositions = []
def makeNumberSet(puzzleSize):
    numberSet = set(range(1,puzzleSize+1))
    return numberSet
def getPuzzleSize(firstLine):
    puzzleSizeHolder = firstLine[4]
    #this is extremely ugly, but it should work to grab the size of the puzzle.
    puzzleSizeChar = puzzleSizeHolder[0]
    puzzleSize = int(puzzleSizeChar)
    return puzzleSize

class cell:
    def __init__(self, cageNumber, row, col):
        self.cage = cageNumber
        self.row = row
        self.column = col

def main():
    input = [line for line in stdin]
    lazySizeList = input[0].split(' ')
    #this is extremely ugly, but it should work to grab the size of the puzzle.
    puzzleSize = getPuzzleSize(lazySizeList)
    del input[0]
    numberSet = makeNumberSet(puzzleSize)
    cageList = []
    puzzleArray = [[0 for j in range(puzzleSize)] for i in range(puzzleSize)]
    puzzleSize = getPuzzleSize(lazySizeList)
    outputString = "(set-logic UFNIA)\n"
    outputString +="(set-option :produce-models true)\n"
    outputString +="(set-option :produce-assignments true)\n"
    numberOfCells = puzzleSize*puzzleSize
    for i in range(numberOfCells):
        outputString += f"(declare-const V{i} Int)\n"
        outputString += f"(assert (and (> V{i} 0) (< V{i} {puzzleSize+1})))\n"
    # check uniqueness of rows
    for r in range(puzzleSize):
        row_vars = [f"V[{r*puzzleSize + c}]" for c in range(puzzleSize)]
        outputString += f"(assert (distinct {' '.join(row_vars)}))\n"

    # check uniqueness of columns
    for c in range(puzzleSize):
        col_vars = [f"V[{r*puzzleSize + c}]" for r in range(puzzleSize)]
        outputString += f"(assert (distinct {' '.join(col_vars)}))\n"

    for m,line in enumerate(range(puzzleSize)):
        #COMMENT BELOW IS TO REMIND ME OF THE SYNTAX IN THE PUZZLE
        #r1.16+,r2.1-,r2,r3.5-,r3,r4.3/,r4,r5.13+,r5
        rowArray = input[line].split(',')
        #each cell is split on commas
        for i, token in enumerate(rowArray):
            tokenvals = token.split('.')
            #we split on periods, turn the value into a list.
            cellCage = tokenvals[0]
            cellCageNumber = int(cellCage[1:])
            if (len(tokenvals)>1):
                if (tokenvals[1][-1].isdigit() == False):
                    cageTotal = int(tokenvals[1][:-1])
                    cageOperator = tokenvals[1][-1]
                else:
                    cageTotal = int(tokenvals[1])
                    cageOperator = int(tokenvals[1])
                newCage = cage(cellCageNumber, cageTotal, cageOperator)
                newCage.cellPositions.append((m, i))
                cageList.append(newCage)
            else:
                cageList[cellCageNumber-1].cellPositions.append((m,i))

    #CURRENT STATUS:
        #at this point, we have populated the cellPositions lists of the cage objects
    
    #populate the equality constraints
    for m, currCage in enumerate(cageList):
        if currCage.operator in ("*", "+"):
            outputString += f"(assert (= {currCage.total} ({currCage.operator} "
            for position in currCage.cellPositions:
                row = position[0]
                col = position[1]
                singleValuePosition = (row*(puzzleSize))+col
                outputString += f"V{singleValuePosition} "
            outputString +=f"))) ; Cage {currCage.number} \n"
        elif currCage.operator in ("/", "-"):
            outputString += f"(assert (or (= {currCage.total} ({currCage.operator} "
            for position in currCage.cellPositions:
                row = position[0]
                col = position[1]
                singleValuePosition = row*(puzzleSize)+col
                outputString += f"V{singleValuePosition} "
            outputString += f")) (= {currCage.total} ({currCage.operator} "
            for position in reversed(currCage.cellPositions):
                row = position[0]
                col = position[1]
                singleValuePosition = row*(puzzleSize)+col
                outputString += f"V{singleValuePosition} "
            outputString += f")))) ; Cage{currCage.number} \n"
        else:
            outputString += f"(assert (= {currCage.total}( "
            for position in currCage.cellPositions:
                row = position[0]
                col = position[1]
                singleValuePosition = row*(puzzleSize)+col
                outputString += f"V{singleValuePosition} ))) ; Cage {currCage.number} \n"
    print(outputString)


def test():
    input = "#kenken www.kenkenpuzzle.com Puzzle 73491 9x9 Medium\nr1.16+,r2.1-,r2,r3.5-,r3,r4.3/,r4,r5.13+,r5\nr1,r6.4/,r6,r7.3-,r8.45*,r8,r9.22+,r9,r5\nr1,r10.3+,r10,r7,r11.2-,r11,r9,r12.2-,r12\nr13.3/,r14.1-,r15.8-,r16.120*,r16,r16,r17.20*,r18.2-,r19.2\nr13,r14,r15,r20.2-,r20,r17,r17,r18,r21.17+\nr22.9+,r23.63*,r24.1-,r25.5-,r24,r26.1-,r27.48*,r21,r21\nr22,r23,r24,r28.5-,r28,r26,r27,r29.4/,r29\nr30.3,r31.432*,r32.20+,r32,r33.18+,r34.3+,r34,r35.13+,r36.2-\nr31,r31,r32,r32,r33,r33,r33,r35,r36"
    testInputList = input.split('\n')
    lazySizeList = testInputList[0].split(' ')
    #this is extremely ugly, but it should work to grab the size of the puzzle.
    puzzleSize = getPuzzleSize(lazySizeList)
    del testInputList[0]
    numberSet = makeNumberSet(puzzleSize)
    cageList = []
    puzzleArray = [[0 for j in range(puzzleSize)] for i in range(puzzleSize)]
    puzzleSize = getPuzzleSize(lazySizeList)
    outputString = "(set-logic UFNIA)\n"
    outputString +="(set-option :produce-models true)\n"
    outputString +="(set-option :produce-assignments true)\n"
    numberOfCells = puzzleSize*puzzleSize
    for i in range(numberOfCells):
        outputString += f"(declare-const V{i} Int)\n"
        outputString += f"(assert (and (> V{i} 0) (< V{i} {puzzleSize+1})))\n"
    # check uniqueness of rows
    for r in range(puzzleSize):
        row_vars = [f"V[{r*puzzleSize + c}]" for c in range(puzzleSize)]
        outputString += f"(assert (distinct {' '.join(row_vars)}))\n"

    # check uniqueness of columns
    for c in range(puzzleSize):
        col_vars = [f"V[{r*puzzleSize + c}]" for r in range(puzzleSize)]
        outputString += f"(assert (distinct {' '.join(col_vars)}))\n"

    for m,line in enumerate(range(puzzleSize)):
        #COMMENT BELOW IS TO REMIND ME OF THE SYNTAX IN THE PUZZLE
        #r1.16+,r2.1-,r2,r3.5-,r3,r4.3/,r4,r5.13+,r5
        rowArray = testInputList[line].split(',')
        #each cell is split on commas
        for i, token in enumerate(rowArray):
            tokenvals = token.split('.')
            #we split on periods, turn the value into a list.
            cellCage = tokenvals[0]
            cellCageNumber = int(cellCage[1:])
            if (len(tokenvals)>1):
                if (tokenvals[1][-1].isdigit() == False):
                    cageTotal = int(tokenvals[1][:-1])
                    cageOperator = tokenvals[1][-1]
                else:
                    cageTotal = int(tokenvals[1])
                    cageOperator = int(tokenvals[1])
                newCage = cage(cellCageNumber, cageTotal, cageOperator)
                newCage.cellPositions.append((m, i))
                cageList.append(newCage)
            else:
                cageList[cellCageNumber-1].cellPositions.append((m,i))

    #CURRENT STATUS:
        #at this point, we have populated the cellPositions lists of the cage objects
    
    #populate the equality constraints
    for m, currCage in enumerate(cageList):
        if currCage.operator in ("*", "+"):
            outputString += f"(assert (= {currCage.total} ({currCage.operator} "
            for position in currCage.cellPositions:
                row = position[0]
                col = position[1]
                singleValuePosition = (row*(puzzleSize))+col
                outputString += f"V{singleValuePosition} "
            outputString +=f"))) ; Cage {currCage.number} \n"
        elif currCage.operator in ("/", "-"):
            outputString += f"(assert (or (= {currCage.total} ({currCage.operator} "
            for position in currCage.cellPositions:
                row = position[0]
                col = position[1]
                singleValuePosition = row*(puzzleSize)+col
                outputString += f"V{singleValuePosition} "
            outputString += f")) (= {currCage.total} ({currCage.operator} "
            for position in reversed(currCage.cellPositions):
                row = position[0]
                col = position[1]
                singleValuePosition = row*(puzzleSize)+col
                outputString += f"V{singleValuePosition} "
            outputString += f")))) ; Cage{currCage.number} \n"
        else:
            outputString += f"(assert (= {currCage.total}( "
            for position in currCage.cellPositions:
                row = position[0]
                col = position[1]
                singleValuePosition = row*(puzzleSize)+col
                outputString += f"V{singleValuePosition} ))) ; Cage {currCage.number} \n"
    print(outputString)

if __name__ == "__main__":
    main()