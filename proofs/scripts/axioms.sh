#!/usr/bin/env bash
# 打印某定理实际依赖的公理，并拦截 sorryAx / 自定义 axiom。
# English: Print the axioms that a given theorem actually depends on, and block the sentinel axiom of unfinished proofs / custom axioms.
#
# 用法：proofs/scripts/axioms.sh <Module.Name> <fully.qualified.theorem>
# English: Usage: proofs/scripts/axioms.sh <Module.Name> <fully.qualified.theorem>
#   e.g. proofs/scripts/axioms.sh PhotoLean.Smoke PhotoLean.smoke_ring
#
# 注意：定理名必须**带命名空间** —— 命名空间内的定理用短名会报 unknown constant。
# English: Note: the theorem name must be **namespace-qualified** — a theorem inside a namespace referenced by its short name reports unknown constant.
#
# 通过标准：输出只含 proofs/ENGINE.yml 的 $ALLOWED_AXIOMS 所列基础设施公理。
# 出现 sorryAx 或任何不在允许清单里的公理名即 FAIL（exit 1）。
# English: Pass criterion: the output contains only the infrastructure axioms listed by $ALLOWED_AXIOMS in proofs/ENGINE.yml.
# English: The presence of an unfinished-proof sentinel axiom, or of any axiom name not on the allow-list, is a FAIL (exit 1).
set -uo pipefail

if [ "$#" -ne 2 ]; then
  echo "usage: $0 <Module.Name> <fully.qualified.theorem>" >&2
  exit 2
fi
MODULE="$1"
THM="$2"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LAKE="$ROOT/proofs/scripts/lake"

CONF="proofs/ENGINE.yml"
[ -f "$CONF" ] && . "./$CONF"
ALLOWED_AXIOMS="${ALLOWED_AXIOMS:-propext Classical.choice Quot.sound}"

# 探针文件名必须**每次唯一**：并发调用（多个 prover/verifier 同时跑验收门）若共用一个固定名，
# 会互相覆盖，产生"问 A 答 B"的假证据（2026-09-20 prover_b 实测报障，已记入 EXPERIENCE.md）。
# English: The probe file name must be **unique on every run**: if concurrent invocations (multiple provers/verifiers running the acceptance gate at the same time) share one fixed name,
# English: they overwrite each other, producing false evidence of the "ask A, answer B" kind (an actual failure reported by prover_b on 2026-09-20, recorded in EXPERIENCE.md).
PROBE=".lake/tmp/AxiomsProbe.$$.$RANDOM.lean"
mkdir -p .lake/tmp
trap 'rm -f "$PROBE"' EXIT
{
  echo "import $MODULE"
  echo "#print axioms $THM"
} > "$PROBE"

echo "==> #print axioms $THM (importing $MODULE)"
OUT="$("$LAKE" env lean "$PROBE" 2>&1)"
RC=$?
echo "$OUT"
echo "----"

if [ "$RC" -ne 0 ]; then
  echo "verdict: FAIL (probe did not compile)"
  echo "hint: 定理名需带命名空间；模块需已构建（先跑 proofs/scripts/lake build）。"
  exit 1
fi

# #print axioms 的输出形如：
# English: The output of #print axioms looks like this:
#   '<thm>' depends on axioms: [propext, Classical.choice, Quot.sound]
# 取出方括号内的列表，按逗号切分并 trim。
# English: Extract the list inside the square brackets, split it on commas and trim.
LIST="$(printf '%s' "$OUT" | sed -n 's/.*\[\(.*\)\].*/\1/p' | head -1)"
if [ -z "$LIST" ]; then
  # 无公理依赖时 Lean 输出 "does not depend on any axioms"。
  # English: When there are no axiom dependencies, Lean prints "does not depend on any axioms".
  case "$OUT" in
    *"does not depend on any axioms"*) echo "verdict: PASS (no axiom dependencies at all)"; exit 0 ;;
  esac
  echo "verdict: FAIL (could not parse axiom list from output)"
  exit 1
fi

BAD=""
for n in $(printf '%s' "$LIST" | tr ',' ' '); do
  n="$(printf '%s' "$n" | tr -d '[:space:]')"
  [ -z "$n" ] && continue
  ALLOW=0
  for a in $ALLOWED_AXIOMS; do
    [ "$n" = "$a" ] && ALLOW=1
  done
  if [ "$ALLOW" = 0 ]; then
    BAD="$BAD $n"
  fi
done

if [ -n "${BAD// /}" ]; then
  echo "verdict: FAIL (disallowed axiom(s):$BAD)"
  echo "         sorryAx 与自定义 axiom 一律禁止（no-sorry / axiom 纪律）。"
  exit 1
fi

echo "verdict: PASS (only mathlib infrastructure axioms)"
echo "allowed: $ALLOWED_AXIOMS"
exit 0
