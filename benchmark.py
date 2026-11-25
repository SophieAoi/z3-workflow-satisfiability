"""Run every method on every instance and save the results to
results/benchmark.csv.

Each instance is run 3 times per method and we keep the median time (only
once for 4-constraint-hard, since it's slow). For each run we save the
answer, whether it matches the reference answer, and whether the plan
passes check_plan.

Rows are also written to results/benchmark_partial.csv as we go, so if it
stops you can run it again and it carries on where it left off.

Usage:
    python benchmark.py                 # everything
    python benchmark.py --families 1-constraint-small --runs 1   # smoke test
    python benchmark.py --fresh         # discard the partial file
"""
from __future__ import annotations

import argparse
import csv
import re
import statistics
import sys
import time
from collections import defaultdict
from pathlib import Path

from wsp_solver import (
    UNIQUE, Solver, check_plan, read_instance,
)

ROOT = Path(__file__).parent
INSTANCES = ROOT / "instances"
RESULTS = ROOT / "results"
ALL_METHODS = ("cp-sat", "z3-bool", "z3-int", "portfolio", "cp-sat-users", "z3-cnf")
FIELDS = [
    "family", "instance", "method", "runs", "ms_median", "ms_all",
    "sat", "ref_sat", "agree_sat", "mul_sol", "ref_unique", "plan_ok",
    "other_ok", "method_used",
]


def families():
    return sorted((p for p in INSTANCES.iterdir() if p.is_dir()), key=lambda p: p.name)


def load_reference(family: str, stem: str, path: Path) -> tuple[str, str]:
    """Expected (sat, unique) for an instance, or '' if we don't know."""
    if family == "examples":
        exp = ROOT / "instances/examples/expected.csv"
        with open(exp, newline="") as f:
            for row in csv.DictReader(f):
                if row["instance"] == stem:
                    return ("sat" if row["sat"] == "1" else "unsat",
                            "1" if row["unique"] == "1" else "0")
        return "", ""
    ref = path.with_name(stem + "-solution.txt")
    if ref.exists():
        first = ref.read_text().split()[0] if ref.read_text().split() else ""
        return ("sat" if first == "sat" else "unsat", "")
    return "", ""


def load_partial(partial: Path) -> set[tuple[str, str, str]]:
    if not partial.exists():
        return set()
    with open(partial, newline="") as f:
        return {(r["family"], r["instance"], r["method"]) for r in csv.DictReader(f)}


def one_run(path: str, method: str, time_limit: float, workers: int) -> dict:
    d = Solver(path, method=method, time_limit=time_limit, workers=workers)
    ms = int(d["exe_time"].removesuffix("ms"))
    return {"sat": d["sat"], "mul_sol": d["mul_sol"], "plan": d["plan"],
            "other_plan": d["other_plan"], "ms": ms,
            "method_used": d.get("method_used", "")}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--families", nargs="*", default=None,
                    help="subset of instance folders (default: all)")
    ap.add_argument("--methods", nargs="*", default=list(ALL_METHODS))
    ap.add_argument("--runs", type=int, default=3, help="repetitions per cell")
    ap.add_argument("--hard-runs", type=int, default=1)
    ap.add_argument("--time-limit", type=float, default=30.0,
                    help="seconds per solver call, also applied to the "
                         "uniqueness re-solve")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--fresh", action="store_true", help="discard partial log")
    args = ap.parse_args()

    RESULTS.mkdir(exist_ok=True)
    partial = RESULTS / "benchmark_partial.csv"
    if args.fresh and partial.exists():
        partial.unlink()

    done = load_partial(partial)
    new_file = not partial.exists()
    out = open(partial, "a", newline="")
    writer = csv.DictWriter(out, fieldnames=FIELDS)
    if new_file:
        writer.writeheader()

    t0 = time.perf_counter()
    n_done = n_skip = 0
    for fam_dir in families():
        fam = fam_dir.name
        if args.families and fam not in args.families:
            continue
        # instance files are N.txt, or exampleN.txt in examples/
        stems = sorted((p.stem for p in fam_dir.glob("*.txt")
                        if re.fullmatch(r"(example)?\d+", p.stem)),
                       key=lambda st: int(re.sub(r"\D", "", st)))
        for method in args.methods:
            runs = args.hard_runs if "hard" in fam else args.runs
            for stem in stems:
                if (fam, stem, method) in done:
                    n_skip += 1
                    continue
                path = fam_dir / f"{stem}.txt"
                samples = [one_run(str(path), method, args.time_limit, args.workers)
                           for _ in range(runs)]
                inst = read_instance(path)
                last = samples[len(samples) // 2]
                ref_sat, ref_unique = load_reference(fam, stem, path)
                # unsat cells have no plan to check: leave the column blank
                def flag(plan):
                    if plan is None:
                        return ""
                    return int(not check_plan(inst, plan))
                plan_ok = flag(last["plan"])
                other_ok = flag(last["other_plan"]) if last["plan"] is not None else ""
                row = {
                    "family": fam, "instance": stem, "method": method,
                    "runs": runs,
                    "ms_median": round(statistics.median(s["ms"] for s in samples), 2),
                    "ms_all": ";".join(str(s["ms"]) for s in samples),
                    "sat": last["sat"], "ref_sat": ref_sat,
                    # leave blank if there's no reference answer or it timed out
                    # (a timeout isn't a wrong answer)
                    "agree_sat": ("" if not ref_sat or last["sat"] == "unknown" else
                                  ("1" if last["sat"] == ref_sat else "0")),
                    "mul_sol": last["mul_sol"],
                    # 1 = matches appendix uniqueness, 0 = disagrees, '' = n/a
                    "ref_unique": ("" if ref_unique == "" else
                                   "1" if (ref_unique == "1") == (
                                       last["mul_sol"] == UNIQUE) else "0"),
                    "plan_ok": plan_ok, "other_ok": other_ok,
                    "method_used": last["method_used"] or "",
                }
                writer.writerow(row)
                out.flush()
                n_done += 1
                warn = ("  <-- DISAGREES" if row["agree_sat"] == "0" else
                        "  (timeout)" if row["sat"] == "unknown" else "")
                print(f"{fam}/{stem} {method}: {row['sat']} {row['ms_median']}ms "
                      f"({n_done} done, {time.perf_counter()-t0:.0f}s){warn}", flush=True)

    out.close()

    # write the final csv, one row per (family, instance, method)
    rows = {}
    if partial.exists():
        with open(partial, newline="") as f:
            for r in csv.DictReader(f):
                rows[(r["family"], r["instance"], r["method"])] = r
    with open(RESULTS / "benchmark.csv", "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(rows.values())

    agg = defaultdict(lambda: [0, 0.0, 0, 0])
    for r in rows.values():
        a = agg[(r["family"], r["method"])]
        a[0] += 1
        a[1] += float(r["ms_median"])
        a[2] += int(r["agree_sat"] != "0") if r["agree_sat"] else 0
        a[3] += r["sat"] == "unknown"
    print(f"\n{len(rows)} cells in results/benchmark.csv "
          f"({n_done} new, {n_skip} reused, {time.perf_counter()-t0:.0f}s)")
    print(f"{'family':<22}{'method':<14}{'cells':>6}{'mean ms':>10}{'timeouts':>10}")
    for (fam, method), (n, ms, agree, to) in sorted(agg.items()):
        print(f"{fam:<22}{method:<14}{n:>6}{ms/n:>10.1f}{to:>10}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
