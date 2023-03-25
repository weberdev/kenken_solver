#!/usr/bin/env python3.8
from subprocess import run, PIPE
from functools import reduce
from itertools import takewhile, dropwhile
from typing import Union
import json
import sys

# Coloring used at the commandline to make the grid visable
COLOR_ON = "\033[95m"
COLOR_OFF = "\033[0m"

# Constents just used for convinience when printing the grid
BOLDBAR = COLOR_ON + "|"
BOLDEQ = COLOR_ON + "="


def collectSection(puzzleInfo, startChar: str, endChar: Union[None, str] = None):
    """Takes the puzzleInfo string and splits it from one heading to
    another"""
    start = dropwhile(lambda c: c != startChar, puzzleInfo)
    return "".join(
        [
            char
            for char in (takewhile(lambda x: x != endChar, start) if endChar else start)
        ][1:]
    ).strip()


def transpose(l):
    "Transposes a list. Used for the horizontal matrix"
    return list(list(x) for x in zip(*l))


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

    def constraint(self) -> str:
        return f"{self.target}{self.operator if (self.operator != '1') else ' '}"


def topOrBottomLine(colwid, row):
    # Start of grid
    print(
        COLOR_ON
        + "+"
        + "=".join(["=" * colwid for _ in (enumerate(row))])
        + "+"
        + COLOR_OFF
    )


def createKenKen(puzzleString):
    target = collectSection(puzzleString, "T", "S")
    symbols = collectSection(puzzleString, "S", "V")
    answer = collectSection(puzzleString, "A", "T")
    vertical = collectSection(puzzleString, "V", "H")

    # had to transpose
    horazontal = transpose(
        map(
            lambda line: [cell for cell in line.split()],
            [line for line in collectSection(puzzleString, "H").split("\n")],
        )
    )

    return list(
        map(
            lambda a, b, c, d, e: list(map(Cell, a, b, c, d, e)),
            [(line.strip().split()) for line in target.split("\n")],
            [(line.strip().split()) for line in symbols.split("\n")],
            [(line.strip().split()) for line in answer.split("\n")],
            [(line.strip().split() + ["1"]) for line in vertical.split("\n")],
            [line for line in horazontal + [horazontal[-1]]],
        ),
    )


def getPuzzleId():
    try:
        # Ensure we got a puzzle passed to us
        if len(sys.argv) == 2:
            if sys.argv[1] == "-h" or (not sys.argv[1].isdigit()):
                print("pp: expects a single command argument containing a Puzzle ID")
                print("For example")
                print("pp '22597'")
                exit(0)
            return sys.argv[1]
        else:
            puzzledesc = [line for line in sys.stdin][0].split()
            # Get the puzzle id following the text Puzzle
            return puzzledesc[(puzzledesc.index("Puzzle") + 1)]

    except:
        print("ERROR: Failed to identify PUZZLE ID")
        exit(1)


def lookupPuzzle(id):
    try:
        # Run the provided script from the professor
        p = run(
            ["bash", "./fetch.sh", id],
            stdout=PIPE,
            encoding="ascii",
        )
        if p.returncode != 0:
            print("Error script did not execute properly")
            exit(1)
        return json.loads(p.stdout.replace("\\r\\n", "\\n").replace("\\r", "\\n"))[
            "data"
        ]
    except:
        print("Failed to find a puzzle with the ID" + id)


def main():
    puzzle: str = getPuzzleId()

    kenkenPuzzle = createKenKen(lookupPuzzle(puzzle))

    largestConstraint = reduce(
        lambda a, b: max(
            a,
            len(b.constraint() if b.target and b.operator else " "),
        ),
        [i for l in kenkenPuzzle for i in l],
        0,
    )

    # How wide a column should be. I added 2 extra space to make it look pretty
    columnPadding = 2
    columnWidth = largestConstraint + columnPadding

    # We now begin the grid
    topOrBottomLine(columnWidth, kenkenPuzzle[0])
    for rowNumber, row in enumerate(kenkenPuzzle):
        whiteSpaceFor = lambda s: " " * (columnWidth - len(s))
        # Row with the target and symbol printed
        if (
            rowNumber >= 1
        ):  # We have a dedicated print for just the first grid line alreadyg
            print(
                BOLDBAR
                + "+".join(
                    [
                        (
                            COLOR_OFF + (BOLDEQ * columnWidth)
                            if (
                                c.target
                                # If the previous line was a horizontal row
                                # then we also need to mark that
                                or (
                                    rowNumber >= 1
                                    and kenkenPuzzle[rowNumber - 1][j].horazontal
                                )
                            )
                            else COLOR_OFF + ("-" * columnWidth)
                        )
                        + (COLOR_ON if c.vertical else "")
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
                        cell.constraint() + whiteSpaceFor(cell.constraint())
                        if cell.target
                        else whiteSpaceFor("")
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
    topOrBottomLine(columnWidth, kenkenPuzzle[0])


if __name__ == "__main__":
    main()
