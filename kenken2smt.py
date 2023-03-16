#!/usr/bin/env python3

from itertools import count
from sys import stdin
from typing import Tuple, Union, List
import re
import operator

#I received this code in a dream:
#by which I mean I asked GPT if such a tool existed and it said I should do this
#sadly there is no built in char to op module in Python
operators = {'+': operator.add, '-': operator.sub, '*': operator.mul, '/': operator.truediv}

class cage:
    def __init__(self, number, total, operator):
        self.number = number
        self.total = total
        self.operator = operator

def getPuzzleSize(firstLine):
    puzzleSizeHolder = firstLine[4]
    #this is extremely ugly, but it should work to grab the size of the puzzle.
    puzzleSize = puzzleSizeHolder[0].int()
    return puzzleSize

class cell:
    def __init__(self, cageNumber):
        self.cage = cageNumber

def main():
    input = [line for line in stdin]
    lazySizeList = input[0].split(' ')
    #this is extremely ugly, but it should work to grab the size of the puzzle.
    puzzleSize = getPuzzleSize(lazySizeList)
    cageList = []
    puzzleArray = [[cell() for j in range(puzzleSize)] for i in range(puzzleSize)]
    for m,line in enumerate(range(1, puzzleSize)):
        rowArray = line.split(',')
        for i, token in enumerate(rowArray):
            #r1.16+,r2.1-,r2,r3.5-,r3,r4.3/,r4,r5.13+,r5
            tokenvals = token.split('.')
            cellCage = tokenvals[0]
            cellCageNumber = cellCage[1:]
            if (tokenvals[1]):
                if (tokenvals[1][-1].isdigit() == False):
                    cageTotal = tokenvals[1][:-1]
                    cageOperator = tokenvals[1][-1]
                else:
                    cageTotal = tokenvals[1]
                    cageOperator = tokenvals[1]
                newCage = cage(cellCageNumber, cageTotal, cageOperator)
                cageList.append(newCage)
            puzzleArray[m][i] = cell(cellCageNumber)