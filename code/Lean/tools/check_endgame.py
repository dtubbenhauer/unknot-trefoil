#!/usr/bin/env python3
"""Independent numerical sampling of the plumbing and lens-space parameters."""
from fractions import Fraction
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[1]


def minus_fraction(weights):
    fraction = Fraction(weights[-1])
    for weight in reversed(weights[:-1]):
        fraction = weight - 1 / fraction
    return fraction


def sum_squares(m, x):
    adjacent = sum((u - v)**2 for u, v in zip(x, x[1:]))
    return adjacent + x[0]**2 + 2 * x[-1]**2 + 2 * x[m - 1]**2 + 4 * x[m]**2


def quadratic(weights, x):
    diagonal = sum(weight * value**2 for weight, value in zip(weights, x))
    return diagonal - 2 * sum(u * v for u, v in zip(x, x[1:]))


def main():
    rng_checks = 0
    for m in range(2, 202):
        p = 104 * m + 37
        weights = [2] * (m - 1) + [4, 6, 2, 2, 3]
        assert p % 2 == 1
        assert minus_fraction(weights).as_integer_ratio() == (p, p - 104)
        assert len(weights) + 4 == m + 8
        rng = random.Random(m)
        for _ in range(32):
            x = [rng.randint(-6, 6) for _ in weights]
            assert quadratic(weights, x) == sum_squares(m, x)
            if any(x):
                assert sum_squares(m, x) > 0
            rng_checks += 1
    report = {
        "status": "independent numerical sampling passed",
        "parameters_checked": 200,
        "quadratic_checks": rng_checks,
    }
    reports = ROOT / "reports"
    reports.mkdir(exist_ok=True)
    rendered = json.dumps(report, indent=2)
    (reports / "section3a-endgame-independent-check.json").write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
