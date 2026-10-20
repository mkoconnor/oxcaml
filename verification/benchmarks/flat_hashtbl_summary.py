#!/usr/bin/env python3
"""Check flat_hashtbl.py results and report medians, spread, ratios and load."""
import argparse
from collections import defaultdict
import csv
import json
import math
from pathlib import Path
import statistics

OPERATIONS = ('build', 'hit', 'miss', 'replace', 'churn', 'mixed')
PAYLOADS = ('int', 'string')
IMPLEMENTATIONS = ('simd', 'scalar', 'stdlib', 'base')
HEADER = ('repeat,implementation,payload,entries,operation,'
          'ns_per_op,bytes_per_op')


def read_results(source):
    metadata = None
    header = False
    records = {}
    loads = []
    for number, line in enumerate(source, 1):
        line = line.strip()
        try:
            if not line:
                continue
            if line.startswith('# {'):
                if metadata is not None:
                    raise ValueError('duplicate benchmark metadata')
                metadata = json.loads(line[2:])
                continue
            if line.startswith('# load,'):
                fields = line[len('# load,'):].split(',')
                if len(fields) != 6:
                    raise ValueError('invalid load reading')
                load = (float(fields[3]), float(fields[4].split()[0]),
                        float(fields[5].split()[0]))
                if any(not math.isfinite(x) or x < 0 for x in load):
                    raise ValueError('invalid load reading')
                loads.append(load)
                continue
            if line.startswith('#'):
                continue
            if line == HEADER:
                if header:
                    raise ValueError('duplicate CSV header')
                header = True
                continue
            if not header:
                raise ValueError('missing CSV header')
            repeat, impl, payload, n, op, a, b = next(csv.reader([line]))
            key = (int(repeat), impl, payload, int(n), op)
            if key in records:
                raise ValueError(f'duplicate result: {key}')
            if op == 'check':
                value = (int(a), int(b))
            else:
                value = (float(a), float(b))
                if any(not math.isfinite(x) or x < 0 for x in value):
                    raise ValueError(f'invalid measurement: {key}')
            records[key] = value
        except (ValueError, IndexError) as error:
            raise ValueError(f'line {number}: {error}') from error
    if not isinstance(metadata, dict):
        raise ValueError('missing benchmark metadata')
    implementations = metadata.get('implementations')
    sizes = metadata.get('sizes')
    repeats = metadata.get('repeats')
    if not isinstance(implementations, list) or not implementations or any(
            impl not in IMPLEMENTATIONS for impl in implementations):
        raise ValueError('metadata must list the selected implementations')
    if len(set(implementations)) != len(implementations):
        raise ValueError('metadata repeats an implementation')
    if not isinstance(sizes, list) or not sizes or any(
            type(n) is not int or n <= 0 for n in sizes):
        raise ValueError('metadata must list positive sizes')
    if len(set(sizes)) != len(sizes):
        raise ValueError('metadata repeats a size')
    if type(repeats) is not int or repeats < 1:
        raise ValueError('metadata must specify a positive repeat count')
    expected = {
        (repeat, impl, payload, n, op)
        for repeat in range(repeats) for impl in implementations
        for payload in PAYLOADS for n in sizes
        for op in (*OPERATIONS, 'check')
    }
    missing = expected - records.keys()
    extra = records.keys() - expected
    if missing:
        raise ValueError(f'missing {len(missing)} results; first: '
                         f'{min(missing)}')
    if extra:
        raise ValueError(f'unexpected result: {min(extra)}')
    for payload in PAYLOADS:
        for n in sizes:
            checks = {records[repeat, impl, payload, n, 'check']
                      for repeat in range(repeats) for impl in implementations}
            if len(checks) != 1:
                raise ValueError(f'checksum mismatch for {payload}, '
                                 f'{n} entries')
            if next(iter(checks))[0] != n:
                raise ValueError(f'incorrect entry count for {payload}, '
                                 f'{n} entries')
    rows = defaultdict(list)
    for (_, impl, payload, n, op), (time, _) in records.items():
        if op != 'check':
            rows[impl, payload, n, op].append(time)
    return implementations, sorted(sizes), repeats, rows, loads


def report(results):
    impls, sizes, repeats, rows, loads = results
    print(f'Checks passed for {len(PAYLOADS) * len(sizes)} '
          f'(payload, size) pairs, {repeats} repeats, '
          f'across {", ".join(impls)}.\n')
    ratio_impls = ([i for i in impls if i != 'stdlib']
                   if 'stdlib' in impls else [])
    columns = ['entries', 'op', *impls,
               *(f'stdlib/{i}' for i in ratio_impls)]
    for payload in PAYLOADS:
        print(f'## {payload} payload: median ns/op '
              '(min-max over repeats)\n')
        print('| ' + ' | '.join(columns) + ' |')
        print('|' + '---|' * len(columns))
        for n in sizes:
            for op in OPERATIONS:
                cells, med = [], {}
                for impl in impls:
                    xs = rows[impl, payload, n, op]
                    m = statistics.median(xs)
                    med[impl] = m
                    cells.append(f'{m:.2f} ({min(xs):.2f}-{max(xs):.2f})')
                ratios = [f'{med["stdlib"] / med[i]:.2f}' if med[i] > 0
                          else '' for i in ratio_impls]
                print(f'| {n} | {op} | ' +
                      ' | '.join([*cells, *ratios]) + ' |')
        print()
    if loads:
        busy, before, after = zip(*loads)
        print('## Load\n')
        print(f'{len(loads)} runs. Busy CPUs before each run: '
              f'median {statistics.median(busy):.2f}, max {max(busy):.2f}. '
              '1-minute load average before: '
              f'median {statistics.median(before):.2f}, '
              f'max {max(before):.2f}; after: '
              f'median {statistics.median(after):.2f}, '
              f'max {max(after):.2f}.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('results', type=Path)
    args = parser.parse_args()
    try:
        with args.results.open() as source:
            results = read_results(source)
    except (OSError, ValueError) as error:
        parser.exit(1, f'{args.results}: {error}\n')
    report(results)


if __name__ == '__main__':
    main()
