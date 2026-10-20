import argparse
import contextlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import flat_hashtbl
import flat_hashtbl_summary as summary


def fixture(implementations=('simd', 'stdlib')):
    metadata = {'implementations': implementations, 'sizes': [8], 'repeats': 2}
    lines = ['# ' + json.dumps(metadata), summary.HEADER]
    for repeat in range(2):
        for impl in implementations:
            for payload in ('int', 'string'):
                for op in ('build', 'hit', 'miss', 'replace', 'churn', 'mixed'):
                    lines.append(f'{repeat},{impl},{payload},8,{op},10.0,0.0')
                lines.append(f'{repeat},{impl},{payload},8,check,8,-123')
    return lines


class ResultsTest(unittest.TestCase):
    def test_complete_run(self):
        results = summary.read_results(fixture())
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            summary.report(results)
        self.assertIn('2 repeats, across simd, stdlib', output.getvalue())
        self.assertIn('stdlib/simd', output.getvalue())

    def test_selected_subset_without_stdlib(self):
        results = summary.read_results(fixture(('scalar',)))
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            summary.report(results)
        self.assertIn('| entries | op | scalar |', output.getvalue())
        self.assertNotIn('stdlib/', output.getvalue())

    def test_truncated_and_missing_runs(self):
        complete = fixture()
        variants = [
            complete[:-1],
            [line for line in complete if not line.startswith('1,stdlib,')],
            [line for line in complete if ',check,' not in line],
            complete[:2],
        ]
        for lines in variants:
            with self.subTest(lines=lines[-1:]):
                with self.assertRaisesRegex(ValueError, 'missing .* results'):
                    summary.read_results(lines)

    def test_duplicate_result(self):
        lines = fixture()
        with self.assertRaisesRegex(ValueError, 'duplicate result'):
            summary.read_results([*lines, lines[-1]])

    def test_mismatch_and_wrong_entry_count(self):
        lines = fixture()
        lines[-1] = lines[-1].replace('-123', '456')
        with self.assertRaisesRegex(ValueError, 'checksum mismatch'):
            summary.read_results(lines)
        lines = [line.replace(',check,8,', ',check,7,') for line in fixture()]
        with self.assertRaisesRegex(ValueError, 'incorrect entry count'):
            summary.read_results(lines)

    def test_metadata_and_nonfinite_measurement(self):
        with self.assertRaisesRegex(ValueError, 'missing benchmark metadata'):
            summary.read_results(fixture()[1:])
        lines = fixture()
        lines[2] = lines[2].replace('10.0', 'nan')
        with self.assertRaisesRegex(ValueError, 'invalid measurement'):
            summary.read_results(lines)

    def test_cli_rejects_incomplete_results(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'results.csv'
            path.write_text('\n'.join(fixture()[:-1]) + '\n')
            result = subprocess.run(
                [sys.executable, summary.__file__, str(path)],
                capture_output=True, text=True)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, '')
        self.assertIn('missing 1 results', result.stderr)


class OptionsTest(unittest.TestCase):
    def options(self, **changes):
        options = dict(work_factor=1, repeats=1, sizes=[8],
                       implementations=['simd'], base_build=None,
                       prepare_base=None, cpu=None, idle_cpus=None,
                       idle_timeout=10)
        options.update(changes)
        return argparse.Namespace(**options)

    def reject(self, **changes):
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                flat_hashtbl.validate_options(
                    argparse.ArgumentParser(), self.options(**changes))
        self.assertEqual(error.exception.code, 2)

    def test_non_linux_options(self):
        with patch.object(flat_hashtbl.platform, 'system',
                          return_value='Darwin'):
            self.reject(cpu='0')
            self.reject(idle_cpus=1)

    def test_invalid_thresholds_and_duplicates(self):
        with patch.object(flat_hashtbl.platform, 'system',
                          return_value='Linux'):
            for threshold in [0, -1, float('inf'), float('nan')]:
                self.reject(idle_cpus=threshold)
                self.reject(idle_timeout=threshold)
        self.reject(sizes=[8, 8])
        self.reject(implementations=['simd', 'simd'])

    def test_affinity(self):
        with patch.object(flat_hashtbl.platform, 'system',
                          return_value='Linux'), \
             patch.object(flat_hashtbl.shutil, 'which',
                          return_value='/taskset'), \
             patch.object(flat_hashtbl.os, 'sched_getaffinity',
                          return_value={2, 3, 4}, create=True):
            flat_hashtbl.validate_options(
                argparse.ArgumentParser(), self.options(cpu='2-3,4'))
            for cpu in ['', '3-2', '0', '2,5', 'two', '2-999999999']:
                self.reject(cpu=cpu)


if __name__ == '__main__':
    unittest.main()
