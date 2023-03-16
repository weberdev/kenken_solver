#!/usr/bin/env python3

from itertools import count
from sys import stdin
from typing import Tuple, Union, List
import re

class cage:
    def __init__(self, number, total, operator):
        self.number = number
        self.total = total
        self.operator = operator

class cell:
    def __init__(self, value, cage):
        self.value = value
        self.cage = cage

def main():
    input = [line for line in stdin]
    lazySizeList = input[0].split(' ')
    puzzleSizeHolder = lazySizeList[4]
    #this is extremely ugly, but it should work to grab the size of the puzzle.
    puzzleSize = puzzleSizeHolder[0].int()
    puzzleArray = [[cell() for j in range(puzzleSize)] for i in range(puzzleSize)]