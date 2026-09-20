#!/usr/bin/env python3
"""全项目语句保真度比对器（lead 维护）。
用法：python3 proofs/probes/marcus-fidelity.py [--verbose]
退出码：0 = 全部一致；1 = 存在差异（打印差异明细）。
"""
import re, sys, glob, os
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SKEL = os.path.join(ROOT, 'proofs/probes/marcus-statement-skeleton.lean')

def signatures(path, only_named=None):
    """抽取 name -> 规范化签名（去空白，到第一个 := 之前）。"""
    src = open(path).read()
    out = {}
    for m in re.finditer(r'^(?:noncomputable\s+)?(?:theorem|def|inductive)\s+([A-Za-z_][\w\']*)(.*?)(?=:=\s*by|:=\s*$|:=|\n\n)',
                         src, re.M | re.S):
        name = m.group(1)
        sig = re.sub(r'\s+', ' ', (m.group(2) or '')).strip()
        out[name] = sig
    return out

skel = signatures(SKEL)
diff, same, extra = [], 0, []
for f in sorted(glob.glob(os.path.join(ROOT, 'PhotoLean/Marcus/*.lean'))):
    got = signatures(f)
    for name, sig in got.items():
        if name not in skel:
            extra.append(f"{os.path.basename(f)}::{name}")
            continue
        a = re.sub(r'\s+', ' ', skel[name]).strip()
        if a == sig:
            same += 1
        else:
            diff.append((os.path.basename(f), name, a, sig))

print(f"权威语句数: {len(skel)}")
print(f"逐字一致: {same}")
print(f"交付文件中不在权威内的辅助声明: {len(extra)}（不算差异）")
print(f"差异: {len(diff)}")
if diff:
    for f, n, a, b in diff:
        print(f"\n✗ {f}::{n}\n  skeleton: {a[:160]}\n  delivered: {b[:160]}")
if '--verbose' in sys.argv:
    for e in extra: print("  (extra)", e)
sys.exit(1 if diff else 0)
