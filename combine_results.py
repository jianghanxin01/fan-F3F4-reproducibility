"""Check a complete fresh merged search and apply the forty checked exclusions.

Every checkpoint is inspected. No checkpoint or solver status is modified.
Completion here remains conditional on the bulk solver's UNSAT decisions.
"""
import argparse
import importlib.util
import json
import math
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
ENGINE = 'fan17-cpp-1'
DATASET = 'e38c0723b6a3be74'
SOURCE_ID = 'd5ad5bbd4b93f03e41cefb242c69f6f19db05d30b1729f607f84844430f1277c'
TOTAL = 88294674
CHUNK = 500
TASKS = (TOTAL + CHUNK - 1) // CHUNK


def require(test, message):
    if not test:
        raise ValueError(message)


def fnv(text):
    h = 14695981039346656037
    for byte in text.encode('ascii'):
        h = ((h ^ byte) * 1099511628211) & ((1 << 64) - 1)
    return '%016x' % h


def checkpoint(record, task):
    require(record['format'] == 'fan17-cpp-checkpoint-1' and record['engine'] == ENGINE
            and record['dataset'] == DATASET and record['source_manifest_id'] == SOURCE_ID,
            'Checkpoint identity mismatch')
    start, stop = CHUNK * task, min(CHUNK * (task + 1), TOTAL)
    require(type(record['task']) is int and record['task'] == task
            and record['start'] == start and record['stop'] == stop, 'Checkpoint interval mismatch')
    status = record['status']
    require(isinstance(status, str) and len(status) == stop - start and set(status) <= set('0123'),
            'Checkpoint status string invalid')
    counts = {name: status.count(code) for name, code in [('PENDING','0'),('UNSAT','1'),('UNKNOWN','2'),('SAT','3')]}
    require(record['counts'] == counts, 'Checkpoint counts mismatch')
    require(counts['PENDING'] == 0, 'Pending cases remain; resume the search')
    require(counts['SAT'] == 0 and record['witnesses'] == {}, 'SAT case or witness present; inspect and independently verify it')
    require(record['status_hash'] == fnv(status + '{}'), 'Checkpoint integrity hash mismatch')
    require(type(record['attempts']) is int and record['attempts'] >= len(status)
            and math.isfinite(record['work_seconds']) and record['work_seconds'] >= 0,
            'Checkpoint accounting invalid')
    return counts, [start + i for i, code in enumerate(status) if code == '2']


def combine(results):
    results = Path(results)
    require(results.is_dir(), 'Merged results directory does not exist')
    require(not (results / 'RUN.lock').exists(), 'Merge is still running or its lock remains')
    require(not (results / 'SAT_FOUND.json').exists(), 'SAT marker present; inspect its witness before making an exclusion claim')
    expected_names = {'task_%06d.json' % i for i in range(TASKS)}
    actual_names = {p.name for p in results.glob('task_*.json')}
    require(actual_names == expected_names, 'Need exactly all %d merged task checkpoint files' % TASKS)
    counts = {'PENDING':0,'SAT':0,'UNKNOWN':0,'UNSAT':0}
    unresolved = []
    for task in range(TASKS):
        record = json.loads((results / ('task_%06d.json' % task)).read_text(encoding='utf-8'))
        try:
            current, unknown = checkpoint(record, task)
        except (ValueError, KeyError, TypeError) as error:
            raise ValueError('Task %d: %s' % (task, error)) from error
        for key in counts:
            counts[key] += current[key]
        unresolved.extend(unknown)
    require(sum(counts.values()) == TOTAL, 'Checkpoint coverage total differs')
    summary = json.loads((results / 'summary.json').read_text(encoding='utf-8'))
    require(summary['engine'] == ENGINE and summary['dataset'] == DATASET and summary['total_pairs'] == TOTAL,
            'Merged summary identity mismatch')
    require(all(summary[key] == value for key,value in counts.items()), 'Merged summary differs from actual checkpoint counts')
    spec = importlib.util.spec_from_file_location('fresh_tail_verification', HERE / 'verify40.py')
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    checked = verifier.run(verbose=False)
    proved = set(checked['excluded_case_ids'])
    extra = sorted(set(unresolved) - proved)
    require(not extra, 'Unresolved cases outside the fixed forty remain; retry or analyze them: ' + ','.join(map(str,extra[:25])))
    return {'dataset':DATASET,'engine':ENGINE,'checkpoint_files_checked':TASKS,'total_pairs':TOTAL,
            'solver_reported_counts':counts,'unknown_case_ids_in_merged_results':unresolved,
            'unknown_cases_resolved_by_checked_certificates':len(unresolved),
            'combined_excluded_cases':TOTAL,'combined_unknown_remaining':0,
            'all_pairs_accounted_for_under_solver_and_coverage_assumptions':True,
            'tail_certificate_verified_in_this_invocation':True,
            'bulk_solver_proofs_independently_verified':False,'full_search_verified':False,
            'scope':'Every task interval/status hash checked; the original UNSAT decisions remain solver reports. '
                    'The fixed tail certificates were replayed in this invocation and cover every remaining UNKNOWN. '
                    'No original checkpoint was changed.',
            'tail_verification':checked}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    began=time.perf_counter()
    report=combine(args.results)
    report['seconds']=time.perf_counter()-began
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print('PASS: all 88,294,674 cases accounted for, conditional on bulk solver correctness and catalogue coverage.')
    print('Full independent verification of bulk UNSAT proofs: false.')


if __name__=='__main__':
    main()
