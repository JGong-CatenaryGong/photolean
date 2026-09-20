#!/usr/bin/env python3
"""全项目语句保真度比对器（lead 维护）。
用法：python3 theories/Marcus/probes/marcus-fidelity.py [--verbose]
退出码：0 = 全部一致；1 = 存在差异（打印差异明细）。
"""
import re, sys, glob, os
def _repo_root():
    """向上查找仓库根（含 proofs/ENGINE.yml 的那一层）—— 不依赖本文件所在的相对层级，
    因此本脚本随理论目录一起移动时无需改动。"""
    d = os.path.dirname(os.path.abspath(__file__))
    while d != os.path.dirname(d):
        if os.path.exists(os.path.join(d, 'proofs', 'ENGINE.yml')):
            return d
        d = os.path.dirname(d)
    return os.getcwd()


ROOT = _repo_root()
SKEL = os.path.join(ROOT, 'theories/Marcus/probes/marcus-statement-skeleton.lean')

def strip_comments(src):
    """去掉 Lean 注释（支持嵌套块注释 /- -/ 与行注释 --），避免注释里的文字
    （例如英文翻译里以 'theorem' 开头的行）被误当成声明 —— 2026-09-20 修。"""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i)
            if j == -1:
                break
            i = j
            continue
        if src.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        out.append(src[i])
        i += 1
    return ''.join(out)


def signatures(path, only_named=None):
    """抽取 name -> 规范化签名（**先剥注释**，去空白，到第一个 := 之前）。"""
    src = strip_comments(open(path).read())
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
