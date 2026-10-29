#!/usr/bin/env python3
"""Run a bounded priority batch at a completed-module boundary, then resume."""
import argparse,json,os,signal,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--worker-pid',type=int,required=True)
parser.add_argument('--after-module',required=True)
parser.add_argument('--module-list',type=Path,required=True)
parser.add_argument('--resume-list',type=Path,default=ROOT/'evidence/fft_stage_proposals/point_pipeline_modules.json')
args=parser.parse_args()
status=ROOT/'evidence/fft_stage_proposals/kernel_checks.json'
while True:
    try:
        record=json.loads(status.read_text())['modules'].get(args.after_module,{})
    except json.JSONDecodeError:
        time.sleep(.1)
        continue
    if record.get('exit_code')==0:break
    try:os.kill(args.worker_pid,0)
    except ProcessLookupError:raise SystemExit('Worker exited before the requested successful module.')
    time.sleep(2)
try:os.kill(args.worker_pid,signal.SIGUSR1)
except ProcessLookupError:pass
while True:
    try:os.kill(args.worker_pid,0)
    except ProcessLookupError:break
    time.sleep(.3)
cmd=['uv','run','check_fft_stage_proposals.py','--resume','--module-list']
try:
    r=subprocess.run(cmd+[str(args.module_list)],cwd=ROOT)
    print('PRIORITY_BATCH_FINISHED',r.returncode,flush=True)
finally:
    r=subprocess.run(cmd+[str(args.resume_list)],cwd=ROOT)
raise SystemExit(r.returncode)
