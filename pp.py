#!/usr/bin/env python3.8
from subprocess import run, PIPE
from functools import reduce
from itertools import takewhile, dropwhile
from typing import Union
import json

puzzle = "22597"
p = run(
    ["bash", "./fetch.sh", puzzle],
    stdout=PIPE,
    encoding="ascii",
)
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
horazontal = collectSection(info, "H")
# print(vertical)
# print()
# print(horazontal)
# pretty print answer
# pretty print target
target = collectSection(info, "T", "S")
symbols = collectSection(info, "S", "V")
answer = collectSection(info, "A", "T")
targetRows = list(
    map(
        lambda a, b, c: list(zip(a, b, c)),
        [(line.strip().split()) for line in target.split("\n")],
        [(line.strip().split()) for line in symbols.split("\n")],
        [(line.strip().split()) for line in answer.split("\n")],
    ),
)
largestConstraint = reduce(
    lambda a, b: max(a, len(b[0] + b[1] if b != "0" else b[0])),
    [i for l in targetRows for i in l],
    0,
)
# print(target)
columnWidth = largestConstraint + 2
print("|" + "-".join(["-" * columnWidth for _ in targetRows[0]]) + "|")
for row in targetRows:
    print(
        "|"
        + "|".join(
            [
                f"{cell[0]}{cell[1]}"
                + (" " * (columnWidth - len(f"{cell[0]}{cell[1]}")))
                if cell[0] != "0"
                else " " * columnWidth
                for cell in row
            ]
        )
        + "|"
    )
    print(
        "|"
        + "|".join([(" " * (columnWidth - len(cell[2]))) + cell[2] for cell in row])
        + "|"
    )
    print("|" + "+".join(["-" * columnWidth for cell in row]) + "|")
