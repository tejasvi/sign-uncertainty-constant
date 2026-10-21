#!/usr/bin/env python3
"""Generate SUCert/LowSegs.lean (the y-segments of the lower check) from data/low_gen/*.txt.

Each file has one line `id lo M N k1,k2,kF,hz;... w:c,w:c ... (more fields)`, the fields parsed by GenLow's `lcheck`.
Usage: python3 -I tools/gen_lowsegs.py DATA_DIR OUT_FILE
"""
import sys, os, hashlib

def main():
    ddir, out = sys.argv[1], sys.argv[2]
    segs = []
    for fn in sorted(os.listdir(ddir)):
        if not fn.endswith('.txt'):
            continue
        lines = [l for l in open(os.path.join(ddir, fn)).read().split('\n')
                 if l and not l.startswith('FAIL') and not l.startswith('stuck')]
        assert len(lines) == 1, (fn, len(lines))
        f = lines[0].split(' ')
        assert len(f) >= 11, fn
        lo, M, N = int(f[1]), int(f[2]), int(f[3])
        sps = []
        for t in f[4].split(';'):
            q = t.split(',')
            assert len(q) == 4 and q[3] in ('0', '1'), (fn, t)
            sps.append((int(q[0]), int(q[1]), int(q[2]), q[3] == '1'))
        ws = []
        for t in f[5].split(','):
            q = t.split(':')
            assert len(q) == 2, (fn, t)
            ws.append((int(q[0]), int(q[1])))
        segs.append((lo, M, N, sps, ws, f[0], fn))
    segs.sort(key=lambda s: s[0])
    # contiguity checks (the checker re-checks this)
    P = 128
    start = 2751 * 2 ** P // 5000
    assert segs[0][0] == start, (segs[0][0], start)
    pos = start
    npieces = 0
    for s in segs:
        assert s[0] == pos, (s[6], s[0], pos)
        assert all(w > 0 and c > 0 for w, c in s[4]), s[6]
        pos += sum(w * c for w, c in s[4])
        npieces += sum(c for w, c in s[4])
    assert pos == 300 * 2 ** P, (pos, 300 * 2 ** P)
    L = []
    L.append('import SUCert.Low\n')
    L.append('/-! The %d segments in `y` of the lower check (%d pieces), generated from data/low_gen/*.txt by\n'
             '`tools/gen_lowsegs.py` (sorted by `lo`; contiguous from `⌊2751·2^128/5000⌋` to `300·2^128`). -/\n'
             % (len(segs), npieces))
    L.append('namespace SignUnc.LowData\nopen SignUnc.Chk\n')
    for i, (lo, M, N, sps, ws, sid, fn) in enumerate(segs):
        spstr = ', '.join('⟨%d, %d, %d, %s⟩' % (a, b, c, 'true' if h else 'false') for a, b, c, h in sps)
        wstr = ', '.join('(%d, %d)' % (w, c) for w, c in ws)
        L.append('/-- segment %s (%s) -/\ndef lseg%d : LSeg := ⟨(%d : Int), %d, %d, [%s], [%s]⟩\n'
                 % (sid, fn, i, lo, M, N, spstr, wstr))
    L.append('def lowSegs : List LSeg := [%s]\n' % ', '.join('lseg%d' % i for i in range(len(segs))))
    L.append('end SignUnc.LowData\n')
    open(out, 'w').write('\n'.join(L))
    print('segments', len(segs), 'pieces', npieces, 'out', out,
          'sha256', hashlib.sha256(open(out, 'rb').read()).hexdigest())
    # summary for sharding: per segment M, N, pieces
    for i, s in enumerate(segs):
        print('seg', i, s[6], 'M', s[1], 'N', s[2], 'pieces', sum(c for w, c in s[4]), 'runs', len(s[4]))

main()
