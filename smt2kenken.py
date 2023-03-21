#!/usr/bin/env python3.8

from sys import stdin

print(
    "".join(
        [
            res.split(" ")[1]  # Get the value for this variable
            for res in [
                line.split("(")[-1].split(")")[0]  # extract the contents of (V# VAL)
                for line in stdin
            ][
                1:
            ]  # drop first line containing "sat"
        ]
    )
)
