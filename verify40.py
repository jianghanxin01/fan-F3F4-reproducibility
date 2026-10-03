"""Replay the 34 counting and 6 finite-domain certificates using standard Python.

Default: python3 verify40.py
The check includes exact data hashes, case-index mapping, and seed binding.
It does not certify the other cases in the global 88,294,674-pair search.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def require(test, message):
    if not test:
        raise ValueError(message)


def run(data=None, cases=None, structural=None, csp_dir=None, verbose=True):
    began = time.perf_counter()
    data = Path(data) if data else HERE / 'data'
    cases = Path(cases) if cases else HERE / 'certificates/cases.json'
    structural = Path(structural) if structural else HERE / 'certificates/theory_34_certificate.json'
    csp_dir = Path(csp_dir) if csp_dir else HERE / 'certificates'
    binder = load_module('published_input_binding', HERE / 'tools/check_data.py')
    bound = binder.check_inputs(cases, data)
    rows = json.loads(cases.read_text(encoding='utf-8'))
    counting = load_module('published_counting_checker', HERE / 'tools/counting_verify.py')
    short = counting.verify(json.loads(structural.read_text(encoding='utf-8')), rows)
    short_ids = set(short['case_ids'])
    remaining = {c['case_id']: c for c in rows if c['case_id'] not in short_ids}
    require(len(remaining) == 6, 'Expected six remaining cases')
    checker = load_module('published_finite_domain_checker', HERE / 'tools/csp_verify.py')
    expected_files = {'csp_certificate_%d.json' % case_id for case_id in remaining}
    require({p.name for p in csp_dir.glob('csp_certificate_[0-9]*.json')} == expected_files,
            'Missing or unexpected finite-domain certificate')
    results = []
    for case_id, case in sorted(remaining.items()):
        cert = json.loads((csp_dir / ('csp_certificate_%d.json' % case_id)).read_text(encoding='utf-8'))
        result = checker.Checker(cert, case).run()
        results.append(result)
        if verbose:
            print('Verified case %d: %d nodes, %d fan witnesses.' %
                  (case_id, result['nodes'], result['fan_witnesses_checked']), flush=True)
    all_ids = short_ids | {r['case_id'] for r in results}
    require(all_ids == set(binder.EXPECTED_CASE_IDS), 'Certificate coverage is not exactly the published forty cases')
    return {'dataset': binder.DATASET, 'tail_cases': 40, 'structural_lemma_exclusions': 34,
            'replayed_csp_exclusions': 6, 'tail_certificate_verified': True,
            'tail_unknown_remaining': 0, 'full_search_verified': False,
            'scope': 'The fixed forty maximum-cut seed pairs; global enumeration completeness and other UNSAT outputs are outside this check.',
            'mathematical_premises': ['No red F3 or blue F4', 'Total red degree in [7,10]',
                'The 8+9 partition satisfies every maximum-red-cut swap inequality'],
            'excluded_case_ids': sorted(all_ids), 'input_bindings_checked': bound['case_seed_bindings_checked'],
            'counting_matching_witnesses': short['explicit_matching_witnesses_checked'],
            'six_case_nodes': sum(r['nodes'] for r in results),
            'six_case_fan_witnesses': sum(r['fan_witnesses_checked'] for r in results),
            'six_case_domain_deletions': sum(r['deletions'] for r in results),
            'six_case_reports': results, 'seconds': time.perf_counter() - began}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path)
    parser.add_argument('--cases', type=Path)
    parser.add_argument('--structural', type=Path)
    parser.add_argument('--csp-dir', type=Path)
    parser.add_argument('--report', type=Path, default=HERE / 'results/verified40.json')
    args = parser.parse_args()
    result = run(args.data, args.cases, args.structural, args.csp_dir)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print('PASS: all 40 fixed tail cases verified. Full-search verification remains false.')
    print('Report: ' + str(args.report))


if __name__ == '__main__':
    main()
