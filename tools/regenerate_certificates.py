"""Regenerate all tail certificates in a separate output directory.

Requires the compiled fan_tail_certify binary. Final verification is performed
by verify40.py, independently of the C++ generating program.
"""
import argparse
import importlib.util
import json
import math
from pathlib import Path
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--seconds',type=float,default=120)
    args=parser.parse_args()
    if not math.isfinite(args.seconds) or args.seconds <= 0:
        raise ValueError('--seconds must be finite and positive')
    binary=args.binary.resolve()
    if not binary.is_file():
        raise ValueError('Build fan_tail_certify first')
    output=args.output.resolve()
    if output.exists() and any(output.iterdir()):
        raise ValueError('Choose an empty output directory to preserve earlier certificates')
    output.mkdir(parents=True,exist_ok=True)
    cases=ROOT/'certificates/cases.json'
    binder=load('regeneration_input_binding',HERE/'check_data.py')
    binder.check_inputs(cases,ROOT/'data')
    rows=json.loads(cases.read_text(encoding='utf-8'))
    generator=load('counting_witness_generator',HERE/'counting_generator.py')
    short=generator.certify_34(rows)
    short_ids={r['case_id'] for r in short['conclusions']}
    remaining=[r for r in rows if r['case_id'] not in short_ids]
    if len(remaining)!=6:
        raise ValueError('Expected exactly six finite-domain cases')
    (output/'theory_34_certificate.json').write_text(json.dumps(short,indent=2)+'\n',encoding='utf-8')
    casefile=output/'six_cases.json'
    casefile.write_text(json.dumps(remaining,indent=2)+'\n',encoding='utf-8')
    # Relative ASCII file names also work with Windows narrow-argv runtimes
    # when the working-directory path itself contains non-ASCII characters.
    subprocess.run([str(binary),'six_cases.json','generation.json',str(args.seconds),'-1','off',
                    'csp_certificate'],check=True,cwd=str(output))
    subprocess.run([sys.executable,'-I','-B',str(ROOT/'verify40.py'),'--structural',str(output/'theory_34_certificate.json'),
                    '--csp-dir',str(output),'--report',str(output/'verified40.json')],check=True)


if __name__=='__main__':
    main()
