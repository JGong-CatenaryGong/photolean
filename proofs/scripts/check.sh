#!/usr/bin/env bash
# 通用验收门（引擎调用）。项目无关：所有判据从 proofs/ENGINE.yml 读取。
# English: Generic acceptance gate (invoked by the engine). Project-agnostic: all criteria are read from proofs/ENGINE.yml.
#
# 用法：
# English: Usage:
#   proofs/scripts/check.sh                    # 构建全部 + 扫描（不因命中而失败）
                                               # English: build everything + scan (does not fail on hits)
#   proofs/scripts/check.sh PhotoLean.Main     # 只构建指定模块
                                               # English: build only the named module
#   proofs/scripts/check.sh --strict [模块]    # 交付前：任何 sorry/自定义 axiom 命中即 FAIL
                                               # English: before delivery: FAIL as soon as any unproved placeholder or custom axiom is hit
#
# Exit 0 = PASS；1 = 构建失败或（--strict 下）扫描命中；2 = 契约缺失。
# English: Exit 0 = PASS; 1 = build failure or (under --strict) a scan hit; 2 = a missing contract.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT" || exit 2
LAKE="$ROOT/proofs/scripts/lake"

# ── 读契约 ──────────────────────────────────────────────────────────────────
# English: ── Read the contract ──
CONF="proofs/ENGINE.yml"
if [ ! -f "$CONF" ]; then
  echo "!! missing $CONF — 本仓库未声明形式化引擎契约" >&2
  exit 2
fi
# shellcheck disable=SC1090
. "./$CONF"

STRICT=0
TARGETS=()
for arg in "$@"; do
  case "$arg" in
    --strict) STRICT=1 ;;
    *) TARGETS+=("$arg") ;;
  esac
done

# ── 叶子数据面完整性 ────────────────────────────────────────────────────────
# English: ── Leaf data plane integrity ──
echo "==> [$PROJECT_NAME] leaf data plane"
LEAF_FAIL=0
for leaf in "$TASKS" "$EXPERIENCE" "$API_NOTES" "$LITERATURE"; do
  if [ ! -e "$leaf" ]; then
    echo "   MISSING $leaf"
    LEAF_FAIL=1
  fi
done
if [ ! -e "$PLAN" ]; then echo "   MISSING $PLAN"; LEAF_FAIL=1; fi
if [ "$LEAF_FAIL" = 1 ]; then
  echo "   (引擎按契约要求这些文件存在；补齐后重跑)"
  [ "$STRICT" = 1 ] && { echo "==> verdict: FAIL (missing leaf data plane)"; exit 1; }
fi

# ── 构建 ────────────────────────────────────────────────────────────────────
# English: ── Build ──
echo "==> lake build ${TARGETS[*]:-all}"
BUILD_OK=0
if [ ${#TARGETS[@]} -eq 0 ]; then
  "$LAKE" build || BUILD_OK=1
else
  for t in "${TARGETS[@]}"; do
    "$LAKE" build "$t" || BUILD_OK=1
  done
fi

# ── 纪律扫描 ────────────────────────────────────────────────────────────────
# English: ── Discipline scan ──
echo "==> sorry / custom axiom scan (${SOURCE_DIRS}/**/*.lean)"
SRC_ARGS=()
for d in $SOURCE_DIRS; do
  [ -d "$d" ] && SRC_ARGS+=("$d")
done
HITS=""
if [ ${#SRC_ARGS[@]} -gt 0 ]; then
  # 匹配：任意位置的 sorry，或行首的 axiom 声明。
  # English: Matching: an unproved placeholder anywhere, or an axiom declaration at the start of a line.
  # 行内 `--` 注释不参与扫描 —— 否则无法在文档/注释里讨论这两个关键字。
  # English: Inline `--` comments are not scanned — otherwise these two keywords could not be discussed in docs or comments.
  # 已知取舍：块注释 `/- ... -/` 内的关键字仍会被命中，由 verifier 人工复核
  # English: Known trade-off: keywords inside block comments `/- ... -/` are still hit, and are reviewed manually by the verifier
  # （误报比漏报安全：宁可让人确认一次，不可放过真的 sorry）。
  # English: (a false positive is safer than a miss: better to have a human confirm once than to let a genuine hit through).
  HITS="$(grep -rn --include='*.lean' -E 'sorry|^[[:space:]]*axiom([[:space:]]|$)' "${SRC_ARGS[@]}" 2>/dev/null \
    | grep -vE ':[0-9]+:[[:space:]]*--' || true)"
fi
if [ -n "$HITS" ]; then
  echo "$HITS"
  echo "!! found sorry/axiom occurrences (strict=${STRICT} => fail on hits)"
  if [ "$STRICT" = 1 ] && { [ "$FORBID_SORRY" = 1 ] || [ "$FORBID_CUSTOM_AXIOM" = 1 ]; }; then
    echo "==> verdict: FAIL (strict)"
    exit 1
  fi
else
  echo "clean"
fi

# ── 结论 ────────────────────────────────────────────────────────────────────
# English: ── Conclusion ──
echo "==> summary"
if [ "$BUILD_OK" = 0 ]; then
  echo "build: OK"
  echo "allowed axioms: $ALLOWED_AXIOMS"
  [ "$STRICT" = 1 ] && echo "verdict: PASS"
  exit 0
else
  echo "build: FAILED"
  echo "verdict: FAIL"
  exit 1
fi
