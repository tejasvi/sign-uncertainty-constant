#!/usr/bin/env python3
"""Memory-aware build of the kernel-checked shard modules.

Each shard module proves one `decide +kernel` certificate check; the heaviest need about 43 GB of memory each, and a
plain `lake build` starts one job per core, which can exhaust the memory. This script compiles the shards one module
per process, under a total memory cap.

Usage (the script works in the repository root, the parent of tools/):
    lake build SignUnc.LowK.Glue SUCert.UpperCfgK SUCert.DataGroups SignUnc.LowFinal SignUnc.UpperK SignUnc.APos SignUnc.Lower.ExtremizerProbe
    python3 tools/kbuild.py tools/kjobs.txt MEMCAP_GB MAXJOBS
    bash tools/kfinal.sh
The first command builds the modules that the shards and the final modules import; tools/kfinal.sh checks the shard
outputs, compiles the final modules and prints the axioms.

JOBS_FILE lines: `module est_s mem_gb` (module = path without .lean; est_s and mem_gb are the run time and the memory
of the module in an earlier build, used as estimates). Every job runs, under `ulimit -s unlimited` (and `/usr/bin/time
-v` when present),
    lake env lean --tstack=1000000 -DElab.async=false -o .lake/build/lib/lean/<module>.olean
        -i .lake/build/lib/lean/<module>.ilean <module>.lean
longest estimate first. Memory cap: the sum of mem_gb of the running jobs stays <= MEMCAP_GB, and at most MAXJOBS jobs
run at once. Watchdog: when MemAvailable falls below 12 GB, the most recently started job is killed and queued again
with twice its memory estimate (logged in logs/kbuild.tsv.kills). Results are appended to logs/kbuild.tsv: `module rc
elapsed_s maxrss_kb est_s` (rc 99: exit code 0 but an error message in the log); a rerun skips the modules with rc 0
there. Logs of the jobs: logs/kb/; TMPDIR: tmp/."""
import os, sys, time, subprocess, signal, re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
jobs_file, memcap, maxjobs = os.path.abspath(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
os.chdir(ROOT)
os.makedirs('logs/kb', exist_ok=True)
os.makedirs('tmp', exist_ok=True)
tsv = 'logs/kbuild.tsv'
done = set()
if os.path.exists(tsv):
    for l in open(tsv):
        p = l.split()
        if len(p) >= 2 and p[1] == '0':
            done.add(p[0])
queue = []
for l in open(jobs_file):
    p = l.split()
    if p and p[0] not in done:
        queue.append([p[0], float(p[1]), float(p[2])])
queue.sort(key=lambda q: -q[1])
env = dict(os.environ, TMPDIR=os.path.join(ROOT, 'tmp'))
timev = '/usr/bin/time -v ' if os.path.exists('/usr/bin/time') else ''
running = {}

def memavail_gb():
    for l in open('/proc/meminfo'):
        if l.startswith('MemAvailable:'):
            return int(l.split()[1]) / 1e6
    return 0.0

def start(job):
    m = job[0]
    out = f'.lake/build/lib/lean/{m}'
    os.makedirs(os.path.dirname(out), exist_ok=True)
    log = 'logs/kb/' + m.replace('/', '_') + '.log'
    cmd = (f'ulimit -s unlimited; exec {timev}lake env lean --tstack=1000000 -DElab.async=false '
           f'-o {out}.olean -i {out}.ilean {m}.lean > {log} 2>&1')
    p = subprocess.Popen(['bash', '-c', cmd], env=env, start_new_session=True)
    running[p.pid] = (job, p, time.time())

def finish(job, p, t0):
    m = job[0]
    log = open('logs/kb/' + m.replace('/', '_') + '.log').read()
    mm = re.search(r'Maximum resident set size \(kbytes\): (\d+)', log)
    rss = int(mm.group(1)) if mm else -1
    rc = p.returncode
    if rc == 0 and ('error' in log.lower().split('command being timed')[0]):
        rc = 99
    with open(tsv, 'a') as f:
        f.write(f'{m} {rc} {time.time() - t0:.1f} {rss} {job[1]:.0f}\n')

t_start = time.time()
while queue or running:
    for pid, (job, p, t0) in list(running.items()):
        if p.poll() is not None:
            finish(job, p, t0)
            del running[pid]
    if memavail_gb() < 12 and running:
        pid = max(running, key=lambda q: running[q][2])
        job, p, t0 = running.pop(pid)
        os.killpg(pid, signal.SIGKILL)
        p.wait()
        job[2] *= 2
        queue.append(job)
        with open(tsv + '.kills', 'a') as f:
            f.write(f'{job[0]} killed at {time.time() - t_start:.0f}s new_est_gb {job[2]:.1f}\n')
    used = sum(r[0][2] for r in running.values())
    while queue and len(running) < maxjobs:
        k = next((idx for idx, q in enumerate(queue) if used + q[2] <= memcap), None)
        if k is None:
            if not running:
                k = 0
            else:
                break
        job = queue.pop(k)
        start(job)
        used += job[2]
    time.sleep(2)
print(f'ALL DONE {time.time() - t_start:.0f}s', flush=True)
