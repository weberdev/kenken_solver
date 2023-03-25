#!/usr/bin/env python3.8

from itertools import count, permutations
from sys import stdin
from typing import TypeVar, Tuple, Union, List, Dict
import operator

# I received this code in a dream:
# by which I mean I looked up how to do it: there's an operators library in python.
operators = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "/": operator.truediv,
}


class cage:
    def __init__(self, number, total, operator):
        self.number = number
        self.total = total
        self.operator = operator
        self.cellPositions = []


def makeNumberSet(puzzleSize):
    numberSet = set(range(1, puzzleSize + 1))
    return numberSet


def getPuzzleSize(pz: str):
    return len(pz.split("\n")[1].split(","))


class cell:
    def __init__(self, cageNumber, row, col):
        self.cage = cageNumber
        self.row = row
        self.column = col


sdestinct = "distinct"
sassert = "assert"
set_logic = "set-logic"
set_option = "set-option"

Expr = TypeVar("Expr")


def V(i: int) -> Expr:
    return Expr(f"V{i}")


def And(e1: Expr, *e2: Expr) -> Expr:
    return Expr(f"(and {e1} {expandToArgs(e2)})")


def Or(*e2: Expr) -> Expr:
    return Expr(f"(or {expandToArgs(e2)})")


class Expr:
    val: str

    def __repr__(self) -> str:
        return self.val

    def __init__(self, content: Union[Expr, int, str]):
        if isinstance(content, Expr):
            self.val = str(content.val)
        elif isinstance(content, int):
            self.val = str(content)
        elif isinstance(content, str):
            self.val = content

    def __eq__(self, *__o: Expr) -> Expr:
        return Expr(f"(= {self.val} {expandToArgs(__o)})")

    def __or__(self, *__o: Expr) -> Expr:
        return Expr(f"(or {self.val} {expandToArgs(__o)})")

    def __and__(self, *__o: Expr) -> Expr:
        return Expr(f"(and {self.val} {expandToArgs(__o)})")

    def __add__(self, *__o: Expr) -> Expr:
        return Expr(f"(+ {self.val} {expandToArgs(__o)})")

    def __truediv__(self, *__o: Expr) -> Expr:
        return Expr(f"(/ {self.val} {expandToArgs(__o)})")

    def __ge__(self, *__o: Expr) -> Expr:
        return Expr(f"(>= {self.val} {expandToArgs(__o)})")

    def __le__(self, *__o: Expr) -> Expr:
        return Expr(f"(<= {self.val} {expandToArgs(__o)})")

    def __lt__(self, *__o: Expr) -> Expr:
        return Expr(f"(< {self.val} {expandToArgs(__o)})")

    def __gt__(self, *__o: Expr) -> Expr:
        return Expr(f"(> {self.val} {expandToArgs(__o)})")

    def __str__(self) -> str:
        return self.val


def expandToArgs(exps) -> str:
    return " ".join(map(lambda a: a.val, exps))


def Distinct(*e2: Expr) -> Expr:
    return Expr(f"(distinct {expandToArgs(e2)})")


def Assert(e1: Expr, *e2: Expr) -> Expr:
    return Expr(f"(assert {e1} {expandToArgs(e2)})")


def Const(e1: Expr, *e2: Expr) -> Expr:
    return Expr(f"(declare-const {e1} {expandToArgs(e2)})")


Int = Expr("Int")


def main():
    input = "".join(
        # Strip out any comments
        filter(lambda l: not l.startswith("#"), [line for line in stdin])
    ).strip()
    genFromInput(input)


def genFromInput(input):
    puzzleSize = getPuzzleSize(input)

    numberOfCells = puzzleSize * puzzleSize

    expressions = [
        Expr("(set-logic UFNIA)"),
        Expr("(set-option :produce-models true)"),
        Expr("(set-option :produce-assignments true)"),
    ]

    for i in range(numberOfCells):
        expressions.append(Const(V(i), Int))

        lower_bound = V(i) > Expr(0)
        upper_bound = V(i) < Expr(puzzleSize + 1)

        expressions.append(Assert(And(lower_bound, upper_bound)))

    # check uniqueness of rows
    for r in range(puzzleSize):
        expressions.append(
            Assert(Distinct(*[V(r * puzzleSize + c) for c in range(puzzleSize)]))
        )

    # check uniqueness of columns
    for c in range(puzzleSize):
        expressions.append(
            Assert(Distinct(*[V(r * puzzleSize + c) for r in range(puzzleSize)]))
        )

    # r#.constraint
    cages: Dict[
        str,
        Tuple[str, List[Expr]],
    ] = {}
    iter = count(0)
    for line in input.split("\n"):
        for cell in line.split(","):
            if "." in cell:
                cellAndConstraint = cell.split(".")
                # Using rNUM as the key in our dict store the current
                # constraint and cell
                cages[cellAndConstraint[0]] = (cellAndConstraint[1], [V(next(iter))])
            else:
                # Using rNUM as the key in our dict store the current
                # constraint and cell
                cages[cell] = (
                    cages[cell][0],
                    cages[cell][1] + [V(next(iter))],
                )

    # Construct the logic associated with each cage stored in cages
    for _, v in cages.items():
        constraint = v[0]
        equalTo = constraint[0:-1]
        op = constraint[-1]
        elements = v[1]
        if op.isdigit() and len(elements) == 1:
            expressions.append(Assert(Expr(op) == Expr(*elements)))
        elif op == "-" or op == "/":
            expressions.append(
                Assert(
                    Or(
                        *[
                            Expr(equalTo) == Expr(f"({op} {expandToArgs([*perm])})")
                            for perm in permutations(elements)
                        ]
                    )
                )
            )
        else:
            expressions.append(
                (Assert(Expr(equalTo) == Expr(f"({op} {expandToArgs(elements)})")))
            )

    expressions.append(Expr(f"(check-sat)"))
    expressions.append(
        Expr(f"(get-value ({expandToArgs([V(c) for c in range(numberOfCells)])}))")
    )
    expressions.append(Expr(f"(exit)"))
    range(numberOfCells)
    outputString = "\n".join(map(str, expressions))
    outputString += "\n"
    print(outputString)


if __name__ == "__main__":
    main()
