#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fail if Criterion change estimates exceed a regression threshold."
    )
    parser.add_argument(
        "--criterion-dir",
        default="rust/target/criterion",
        help="Path to Criterion output directory.",
    )
    parser.add_argument(
        "--threshold",
        type=float,
        default=0.1,
        help="Allowed regression threshold as a fraction (0.1 = 10%%).",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = Path(args.criterion_dir)
    if not root.exists():
        print(f"Criterion directory not found: {root}", file=sys.stderr)
        return 1

    change_files = sorted(root.rglob("change/estimates.json"))
    if not change_files:
        print(
            "No change estimates found. Run `cargo bench ... -- --baseline <name>` first.",
            file=sys.stderr,
        )
        return 1

    regressions: list[tuple[str, float]] = []
    for path in change_files:
        with path.open(encoding="utf-8") as f:
            data = json.load(f)
        mean = data.get("mean", {})
        point = mean.get("point_estimate")
        if not isinstance(point, (int, float)):
            continue
        if point > args.threshold:
            bench_name = str(path.parents[1].relative_to(root))
            regressions.append((bench_name, point))

    if regressions:
        print("Performance regressions detected (mean change above threshold):", file=sys.stderr)
        for bench, point in regressions:
            print(f"- {bench}: {point * 100:.2f}%", file=sys.stderr)
        return 1

    print("No regressions above threshold.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
