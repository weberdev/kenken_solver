#!/usr/bin/env python3.8
from subprocess import run, PIPE
from functools import reduce
from itertools import takewhile, dropwhile
from typing import Union
import json
import sys


class bcolors:
    HEADER = "\033[95m"
    OKBLUE = "\033[94m"
    OKCYAN = "\033[96m"
    OKGREEN = "\033[92m"
    WARNING = "\033[93m"
    FAIL = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[95m"
    UNDERLINE = "\033[4m"


COLOR_ON = "\033[95m"
COLOR_OFF = "\033[0m"

if len(sys.argv) != 2:
    print("ERROR: expected a single command argument containing a Puzzle ID")
    print("For example")
    print("pp '22597'")

puzzle = sys.argv[1]
p = run(
    ["bash", "./fetch.sh", puzzle],
    stdout=PIPE,
    encoding="ascii",
)
if p.returncode != 0:
    print("Error script did not execute properly")
    exit(1)

info = json.loads(p.stdout.replace("\\r\\n", "\\n").replace("\\r", "\\n"))["data"]


def collectSection(puzzleInfo, startChar: str, endChar: Union[None, str] = None):
    start = dropwhile(lambda c: c != startChar, puzzleInfo)
    return "".join(
        [
            char
            for char in (takewhile(lambda x: x != endChar, start) if endChar else start)
        ][1:]
    ).strip()


vertical = collectSection(info, "V", "H")
# had to transpose
horazontal = list(
    list(x)
    for x in zip(
        *map(
            lambda line: [cell for cell in line.split()],
            [line for line in collectSection(info, "H").split("\n")],
        )
    )
)
print(vertical)
print()
print("\n".join(map(lambda a: " ".join(a), horazontal)))
print()


class Cell:
    target: Union[str, None]
    operator: Union[str, None]
    answer: str
    horazontal: bool
    vertical: bool

    def __init__(
        self, target: str, operator: str, answer: str, vertical: str, horazontal: str
    ):
        self.target = target if target != "0" else None
        self.operator = operator if target != "0" else None
        self.answer = answer
        self.horazontal = True if horazontal == "1" else False
        self.vertical = True if vertical == "1" else False

    def __repr__(self) -> str:
        return str(self.vertical)

    def targetStr(self) -> str:
        return f"{self.target}{self.operator if (self.operator != '1') else ' '}"


# pretty print answer
# pretty print target
target = collectSection(info, "T", "S")
symbols = collectSection(info, "S", "V")
answer = collectSection(info, "A", "T")
targetRows = list(
    map(
        lambda a, b, c, d, e: list(map(Cell, a, b, c, d, e)),
        [(line.strip().split()) for line in target.split("\n")],
        [(line.strip().split()) for line in symbols.split("\n")],
        [(line.strip().split()) for line in answer.split("\n")],
        [(line.strip().split() + ["1"]) for line in vertical.split("\n")],
        [line for line in horazontal + [horazontal[-1]]],
    ),
)

largestConstraint = reduce(
    lambda a, b: max(
        a,
        len((b.target + b.operator) if b.target and b.operator else " "),
    ),
    [i for l in targetRows for i in l],
    0,
)


def getHSeperator(c: Cell):
    return COLOR_ON + "|" if c.horazontal else COLOR_OFF + "|"


# print(target)
columnWidth = largestConstraint + 2
# Start of grid
print(vertical)
print(targetRows)
print(
    COLOR_ON
    + "|"
    + "+".join(["=" * columnWidth for _ in (enumerate(targetRows[0]))])
    + "|"
    + COLOR_OFF
)


def whiteSpaceFor(string: str) -> str:
    return " " * (columnWidth - len(string))


BOLDBAR = COLOR_ON + "|"
BOLDEQ = COLOR_ON + "="
for i, row in enumerate(targetRows):
    # Row with the target and symbol printed
    if i >= 1:
        print(
            BOLDBAR
            + "+".join(
                [
                    COLOR_OFF
                    + (
                        (
                            (
                                BOLDEQ
                                if (
                                    c.target
                                    # If the previous line was a horizontal row
                                    # then we also need to mark that
                                    or (
                                        targetRows[i - 1][j].horazontal
                                        if i >= 1
                                        else False
                                    )
                                )
                                else COLOR_OFF + "-"
                            )
                            * columnWidth
                        )
                        + (
                            COLOR_ON
                            if (
                                c.target
                                # If the previous line was a horizontal row
                                # then we also need to mark that
                                or (
                                    targetRows[i - 1][j].horazontal if i >= 1 else False
                                )
                                or c.vertical
                            )
                            else ""
                        )
                    )
                    for j, c in (enumerate(row))
                ]
            )
            + BOLDBAR
        )
    # Row with the answer printed
    print(
        BOLDBAR
        + "|".join(
            [
                COLOR_OFF
                + (
                    cell.targetStr() + whiteSpaceFor(cell.targetStr())
                    if cell.target
                    else " " * columnWidth
                )
                + (COLOR_ON if cell.vertical else "")
                for cell in row
            ]
        )
        + BOLDBAR
    )
    # End of row in grid
    print(
        BOLDBAR
        + "|".join(
            [
                COLOR_OFF
                + (whiteSpaceFor(cell.answer))
                + cell.answer
                + (COLOR_ON if cell.vertical else COLOR_OFF)
                for cell in row
            ]
        )
        + BOLDBAR
    )

# Finally the ending row of =, +, and | all colored since it's the outer edge
print(BOLDBAR + "+".join([BOLDEQ * columnWidth for _ in targetRows[-1]]) + BOLDBAR)
