#!/usr/bin/env python3
"""Verify the exact correction-term obstruction for the determinant-245 partner."""
from fractions import Fraction
from functools import cache
from math import gcd

DETERMINANT = 245


def surgery_forms():
    """The even reduced forms from Owens's Theorem 1."""
    for first_weight in range(2, (DETERMINANT + 3) // 4 + 1, 2):
        for off_diagonal in range(first_weight):
            quotient, remainder = divmod(
                DETERMINANT + 4 * off_diagonal**2, 2 * first_weight - 1
            )
            if remainder == 0 and (quotient + 1) % 4 == 0:
                second_weight = (quotient + 1) // 2
                if second_weight >= first_weight:
                    yield first_weight, off_diagonal, second_weight


def surgery_matrix(first_weight, off_diagonal, second_weight):
    return (
        (first_weight, 1, off_diagonal, 0),
        (1, 2, 0, 0),
        (off_diagonal, 0, second_weight, 1),
        (0, 0, 1, 2),
    )


def solve(matrix, vector):
    """Solve a nonsingular linear system over the rationals."""
    rows = [[Fraction(entry) for entry in (*row, b)] for row, b in zip(matrix, vector)]
    for index in range(len(rows)):
        pivot = next(i for i in range(index, len(rows)) if rows[i][index])
        rows[index], rows[pivot] = rows[pivot], rows[index]
        divisor = rows[index][index]
        rows[index] = [entry / divisor for entry in rows[index]]
        for i, row in enumerate(rows):
            if i != index:
                coefficient = row[index]
                rows[i] = [x - coefficient * y for x, y in zip(row, rows[index])]
    return [row[-1] for row in rows]


@cache
def correction_term(p, q, label):
    """Ozsváth–Szabó recursion on -L(p,q)."""
    if (p, q) == (1, 0):
        return Fraction(0)
    return Fraction(p * q - (2 * label + 1 - p - q)**2, 4 * p * q) - correction_term(
        q, p % q, label % q
    )


def bound(weights, vector):
    inverse_times_vector = solve(surgery_matrix(*weights), vector)
    return sum(x * y for x, y in zip(vector, inverse_times_vector)) - 1


def congruent(value, correction):
    return (value - correction) % 2 == 0


def verify():
    all_forms = [(2, 1, 42), (4, 0, 18), (8, 5, 12), (14, 11, 14), (62, 61, 62)]
    assert list(surgery_forms()) == all_forms
    # For (4,0,18) the two cyclic blocks have orders 7 and 35.
    d_values = [
        correction_term(DETERMINANT, 141, (70 + label) % DETERMINANT)
        for label in range(DETERMINANT)
    ]
    assert (2 * 70 - (141 - 1)) % DETERMINANT == 0
    assert d_values[0] == -1
    for weights, vector, expected, minimum in (
        ((8, 5, 12), (-1, 0, 0, 0), Fraction(-199, 245), None),
        ((62, 61, 62), (-1, 0, 0, 0), Fraction(1, 245), None),
        ((14, 11, 14), (-1, 0, -1, 0), Fraction(-45, 49), Fraction(53, 49)),
    ):
        ceiling = bound(weights, vector)
        assert ceiling == expected
        matching = [d for d in d_values if congruent(ceiling, d)]
        assert min(matching, default=None) == minimum
        assert all(d > ceiling for d in matching)
    weights = (2, 1, 42)
    adjugate_row = [
        DETERMINANT * value for value in solve(surgery_matrix(*weights), (1, 0, 0, 0))
    ]
    assert adjugate_row == [166, -83, -4, 2]
    units = [unit for unit in range(DETERMINANT) if gcd(unit, DETERMINANT) == 1]
    surviving_sets = []
    for vector, expected_ceiling, expected_label, expected_units in (
        ((0, 0, -1, 0), Fraction(-239, 245), 4, {72, 173}),
        ((0, 0, -2, 0), Fraction(-221, 245), 8, {23, 222}),
    ):
        ceiling = bound(weights, vector)
        assert ceiling == expected_ceiling
        label = sum(x * y for x, y in zip(adjugate_row, vector))
        assert label == expected_label
        admissible = set()
        for unit in units:
            value = d_values[(int(label) * unit) % DETERMINANT]
            if congruent(ceiling, value) and value <= ceiling:
                admissible.add(unit)
        assert admissible == expected_units
        surviving_sets.append(admissible)
    assert surviving_sets[0].isdisjoint(surviving_sets[1])
    print("All five candidate Owens forms for determinant 245 are obstructed.")


if __name__ == "__main__":
    verify()
