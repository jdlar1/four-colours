"""Run a release cap_probe in fresh processes and report full process wall time."""

from concurrent.futures import ThreadPoolExecutor
import subprocess
import sys
from time import perf_counter_ns

CASES = [
    ("33333", (2461, 530, 1220)),
    ("43343", (22144, 2332, 19058)),
    ("44443", (199291, 9580, 187363)),
]


def measure(case):
    pattern, expected = case
    start = perf_counter_ns()
    result = subprocess.run(
        [sys.argv[1], pattern], capture_output=True, check=True, text=True
    )
    elapsed = perf_counter_ns() - start
    fields = result.stdout.split()
    values = [
        fields[fields.index(k) + 1]
        for k in ("elapsed_s", "cpu_s", "peak_KiB", "classes", "direct", "survivors")
    ]
    assert tuple(map(int, values[3:])) == expected
    return elapsed, *values


def serial():
    print(
        "run\tpattern\tprocess_ns\tengine_s\tcpu_s\tpeak_KiB\tclasses\tdirect\tsurvivors"
    )
    for run in range(1, 8):
        for offset in range(3):
            case = CASES[(run - 1 + offset) % 3]
            print(run, case[0], *measure(case), sep="\t", flush=True)


def batch():
    print("run\tpattern\tjobs\tworkers\tbatch_ns\tmax_worker_KiB")
    with ThreadPoolExecutor(max_workers=16) as pool:
        for run in range(1, 6):
            for offset in range(3):
                case = CASES[(run - 1 + offset) % 3]
                start = perf_counter_ns()
                results = list(pool.map(measure, [case] * 64))
                elapsed = perf_counter_ns() - start
                print(
                    run,
                    case[0],
                    len(results),
                    16,
                    elapsed,
                    max(int(result[3]) for result in results),
                    sep="\t",
                    flush=True,
                )


if __name__ == "__main__":
    if sys.argv[2:] == ["--batch"]:
        batch()
    else:
        serial()
