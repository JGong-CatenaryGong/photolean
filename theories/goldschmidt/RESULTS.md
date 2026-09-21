# theories/goldschmidt/RESULTS.md — the Goldschmidt tolerance factor and Goldschmidt's rules, formalized

> The single bilingual deliverable of this theory: every section carries the English original
> followed immediately by its Chinese rendering. Status: **delivered** —
> `PhotoLean/Goldschmidt/` (6 modules, 139 public declarations, all word-for-word against the
> authority, no unproved placeholder, no custom axiomatic declaration).
> How the three parts of the request map onto modules: **①** description layer `Basic.lean` +
> rules layer `Rules.lean`; **②** law layer `Criterion.lean` + sharp conditions `Sharp.lean`;
> **③** rational decision layer `RatModel.lean` + instance verdicts `Instances.lean`.

---

## 1. The question, and the answer in one page / 问题与一页回答

**English.** The request was to turn the Goldschmidt tolerance factor and Goldschmidt's rules into a
theory that Lean can either *prove* or *verify*, in three parts: ① an explicit formal description,
② a proof of the theory together with its exact conditions of validity, and ③ the kernel-decided
verdicts of concrete instances. All three are delivered, and the sharpest single sentence is this:

> For an `ABO₃` perovskite with radii `rA`, `rB`, `rO` the tolerance factor is
> `t = (rA + rO) / (√2 * (rB + rO))`, and the band verdict `lo ≤ t ≤ hi` is **exactly equivalent**
> to an explicit window on the A-site radius,
> `(lo * √2 * (rB + rO) - rO) ≤ rA ≤ (hi * √2 * (rB + rO) - rO)` — for *every* pair of band edges,
> with no nonemptiness hypothesis — and equivalently to a `√2`-free criterion in which only squares
> of rationals are compared.

**中文。** 任务是把 Goldschmidt 容忍因子与 Goldschmidt 规则变成一个 Lean **可证或可验**的理论，分三部分：
① 显式形式化描述；② 证明该理论并给出其**成立条件**；③ 具体实例的内核判决。三部分均已交付，而最锋利的一句
话是：

> 对半径 `rA, rB, rO` 的 `ABO₃` 钙钛矿，容忍因子为 `t = (rA + rO) / (√2 * (rB + rO))`；带判决
> `lo ≤ t ≤ hi` **恰好等价于** A 位半径上的显式窗口
> `(lo * √2 * (rB + rO) - rO) ≤ rA ≤ (hi * √2 * (rB + rO) - rO)`——对**任意**一对带边界成立、无需
> 带非空前提——也等价于一个**不含 `√2`** 的判据（只比较有理数的平方）。

The theory is *conditional on declared modelling premises* (the ideal cubic packing of §6), and it is
honest about that: what is proved is the exact geometry of the ratio, the exact conditions under which
a band verdict holds, and the exact transfer from Goldschmidt's radius rule to a bound on the
tolerance factor. What is *declared* — and therefore explicitly a modelling choice, not a theorem — is
that a band on `t` is the right empirical criterion, and the shape of the three substitution rules.

**中文。** 本理论**以声明的建模前提为条件**（§6 的理想立方堆积），并且对此诚实：被证明的是该比值的精确
几何、带判决成立的**精确条件**、以及从 Goldschmidt 半径规则到容忍因子偏移量的**精确传递**；而被**声明**
（因而是建模选择而非定理）的是「`t` 上的带是合适的经验判据」以及三条取代规则的形状。

---

## 2. Part ① — the formal description / 第一部分：形式化描述

**English.** Three groups of objects, all in `PhotoLean/Goldschmidt/Basic.lean` (description) and
`Rules.lean` (rules), every one of them a *definition*, with every physical premise an explicit
hypothesis of the theorems that use it:

| object | formalization | reading |
|---|---|---|
| tolerance factor | `tolFac rA rB rO = (rA + rO) / (√2 * (rB + rO))` | the A–O contact distance in units of the ideal cuboctahedral distance `√2 * (rB + rO)` (with `latticeOf rB rO = 2 * (rB + rO)` the lattice parameter fixed by the B–O contact) |
| ideal packing | `idealAO rB rO = √2 * (rB + rO)`, `idealA rB rO = idealAO rB rO - rO`, `gapA` | `t = 1` ⟺ both contacts hold simultaneously ⟺ `rA = idealA rB rO` |
| band verdict | `InBand lo hi t := lo ≤ t ∧ t ≤ hi`, `GoldschmidtConforms lo hi rA rB rO := InBand lo hi (tolFac rA rB rO)` | the band edges `lo`, `hi` are **parameters** — the literature's several conventions are instances, never hard-coded constants |
| three-way classifier | `inductive GoldschmidtZone` (`tooSmall`/`ideal`/`tooLarge`), `goldschmidtZone lo hi t` | an `if`-cascade testing `t < lo` first, then `t ≤ hi` |
| radius rule | `RadiusMatch tau r r' := |r - r'| ≤ tau * r`, `tauGoldschmidt = 3/20` | Goldschmidt's "15 %" rule; the *reference-radius* convention is visible in the definition (see §6) |
| charge rule | `ChargeBalanced dz := ∑ i, dz i = 0` over a finite substitution set, `isovalent dz := dz = 0` | the integer charge increments of a substitution set must sum to zero; single-site balance is exactly the isovalent case |
| chemical rule | `chiTol tol0 k chi chi' = tol0 - k * |chi - chi'|`, `Substitutable .. := RadiusMatch (chiTol ..) r r'` | the electronegativity-dressed tolerance; its *linear shape* is a declared modelling choice, only its monotonicity in `|Δχ|` is a theorem |

**中文。** 三组对象，分别在 `Basic.lean`（描述）与 `Rules.lean`（规则）中，全部是**定义**；每条物理前提都
是使用它的定理的**显式假设**：容忍因子（A–O 接触距离除以理想十二面体距离 `√2(rB+rO)`）、理想堆积
（`t = 1` ⟺ 两个接触同时成立 ⟺ `rA = idealA rB rO`）、带判决与三分类器（带边界**是参数**，文献的多套
约定都只是它的实例，绝不硬编码）、半径规则（`|r - r'| ≤ τ r`，`τ = 3/20` 即 15%；定义本身就暴露了
「以哪个半径为参照」的约定，见 §6）、电荷规则（取代集合的整数电荷增量之和为零；单点平衡恰好就是等价
取代）、化学规则（电负性修饰的容差；线性形状是声明的建模选择，只有对 `|Δχ|` 的单调性是定理）。

---

## 3. Part ② — the theory, and its exact conditions / 第二部分：理论及其成立条件

**English.** The law layer (`Criterion.lean`) proves the ratio's geometry; the sharp layer
(`Sharp.lean`) proves where it fails and how the substitution rules propagate. The headline rows, with
their delivered signatures verbatim:

```lean
theorem conforms_iff_radius_window {lo hi rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms lo hi rA rB rO ↔ rAMin lo rB rO ≤ rA ∧ rA ≤ rAMax hi rB rO

theorem conforms_iff_sq {lo hi rA rB rO : ℝ} (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (h : 0 < rB + rO)
    (hA : 0 ≤ rA + rO) : GoldschmidtConforms lo hi rA rB rO ↔
      2 * lo ^ 2 * (rB + rO) ^ 2 ≤ (rA + rO) ^ 2 ∧
        (rA + rO) ^ 2 ≤ 2 * hi ^ 2 * (rB + rO) ^ 2

theorem conforms_iff_ideal_packing {rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms 1 1 rA rB rO ↔ rA + rO = idealAO rB rO

theorem conforms_symmetric_band_iff {delta rA rB rO : ℝ} (h : 0 < rB + rO) :
    GoldschmidtConforms (1 - delta) (1 + delta) rA rB rO ↔
      |rA - idealA rB rO| ≤ delta * idealAO rB rO

theorem tolFac_eq_invSqrtTwo_iff {rA rB rO : ℝ} (h : 0 < rB + rO) :
    tolFac rA rB rO = 1 / Real.sqrt 2 ↔ rA = rB

theorem tolFacFifteen_le {rA rA' rB rO : ℝ} (h : 0 < rB + rO)
    (hm : RadiusMatch tauGoldschmidt rA rA') : |tolFac rA' rB rO - tolFac rA rB rO| ≤
      tauGoldschmidt * rA / (Real.sqrt 2 * (rB + rO))

theorem conforms_of_radiusMatch_window {lo hi tau rA rA' rB rO : ℝ} (h : 0 < rB + rO)
    (hm : RadiusMatch tau rA rA') (hlo : rAMin lo rB rO ≤ (1 - tau) * rA)
    (hhi : (1 + tau) * rA ≤ rAMax hi rB rO) : GoldschmidtConforms lo hi rA' rB rO
```

What these say, in words: the band verdict is a **window on the A-site radius**
(`conforms_iff_radius_window`, exact for every `lo`, `hi`, including inverted and degenerate bands);
the same verdict is decidable by comparing **squares of rationals** (`conforms_iff_sq`, which is what
the `ℚ` layer uses, because `t` itself is irrational at rational radii — `tolFac_irrational`); a
*point* band at `t = 1` is exactly the simultaneous-contact condition (`conforms_iff_ideal_packing`);
a symmetric band `1 ± δ` is exactly the absolute-deviation bound `|rA - idealA| ≤ δ * idealAO`
(`conforms_symmetric_band_iff`, true for every `δ`); the factor is monotone in `rA` and antitone in
`rB` with an exact affine shift law (`tolFac_shift`, `tolFac_abs_shift_eq`), invariant under scaling
(`tolFac_scale_invariance`), and its dependence on `rO` is a **trichotomy**: increasing exactly for
`rA < rB`, decreasing for `rB < rA`, and constant — equal to `1/√2` — exactly for `rA = rB`
(`tolFac_mono_rO_of_lt`, `tolFac_anti_rO_of_lt`, `tolFac_rO_const_iff`, `tolFac_eq_invSqrtTwo_iff`).
Goldschmidt's radius rule propagates to the factor: a 15 % radius substitution moves `t` by at most
`tau * rA / (√2 * (rB + rO))` (`tolFacFifteen_le`), and if the whole substitution interval lies inside
the band window, the substituted perovskite still conforms (`conforms_of_radiusMatch_window`) — this is
the quantitative bridge between the *rules* and the *factor*. On the rule side, the charge rule is
exact: the two-site pairing (`chargeBalanced_pair_iff`) and the **compensating-partner theorem** — a
heterovalent substitution must be accompanied by a site of opposite charge increment
(`exists_compensating_partner`); the chemical rule is monotone: nearer electronegativity never loses a
substitution (`substitutable_mono_chi`, built on the antitone `chiTol_anti`).

**中文。** 定律层（`Criterion.lean`）证明这个比值的几何；锐利层（`Sharp.lean`）证明它在何处失效、以及
取代规则如何传递。上面逐字引用了七条主力行：带判决等价于 A 位半径窗口（对任意 `lo, hi` 精确，含倒置带与
退化带）；同一判决可用**有理数平方**判定（`ℚ` 层就靠它，因为有理半径下 `t` 本身无理——`tolFac_irrational`）；
`t = 1` 的**点带**恰好是两接触同时成立；对称带 `1 ± δ` 恰好是绝对偏差界（对任意 `δ` 成立）；因子对 `rA`
单调增、对 `rB` 单调减，且有精确的仿射位移律；对 `rO` 的依赖是**三分**（`rA < rB` 时增、`rB < rA` 时减、
`rA = rB` 时恒为 `1/√2`）。Goldschmidt 半径规则向因子传递：15% 的半径替换使 `t` 变动不超过
`τ·rA/(√2(rB+rO))`；若整个替换区间落在带窗口内，替换后的钙钛矿仍符合判据——这是**规则与因子之间的定量
桥**。规则侧同样精确：电荷规则给出两点配对与**补偿伙伴定理**（异价取代必伴随一个反号电荷增量的格点）；
化学规则给出单调性（电负性越近绝不丢失取代，建立在反调的 `chiTol_anti` 之上）。

---

## 4. Part ③ — instances and their kernel verdicts / 第三部分：实例及其内核判决

**English.** The instance layer is decided **exactly, in `ℚ`, without `Real.sqrt`** (the `ℚ` layer's
correctness theorem is `inBandQ_cast`, which transfers the squared criterion to the real verdict;
`zoneQ_eq_zone` transfers the computable classifier). The six literature rows use Shannon's printed
radii (A site 12-coordinate, B site 6-coordinate, `rO = 1.40 Å`), and every number below is reproduced
by three independent computations — the kernel (`norm_num` on the squared criterion), the lead's
exact-rational script `theories/goldschmidt/probes/goldschmidt-instance-check.py`, and the verifier's
own recomputation — with 0 mismatches:

| compound | `rA + rO` | `rB + rO` | `t²` | `t` | classic `[4/5, 1]` | `[1, 11/10]` | `1 ± 1/50` |
|---|---|---|---|---|---|---|---|
| `SrTiO₃` | `71/25` | `401/200` | `161312/160801` | ≈ 1.00159 | **no** (just above 1) | yes | **yes** |
| `CaTiO₃` | `137/50` | `401/200` | `150152/160801` | ≈ 0.96632 | **yes** | no | no |
| `BaTiO₃` | `301/100` | `401/200` | `181202/160801` | ≈ 1.06154 | **no** | **yes** (tetragonal) | no |
| `LaMnO₃` | `69/25` | `409/200` | `152352/167281` | ≈ 0.95434 | **yes** | no | no |
| `NaNbO₃` | `279/100` | `51/25` | `8649/9248` | ≈ 0.96707 | **yes** | no | no |
| `BaNiO₃` | `301/100` | `47/25` | `90601/70688` | ≈ 1.13212 | no | **no** (hexagonal in the literature) | no |

Two rows are the honest headlines. **`SrTiO₃`** — the archetypal cubic perovskite — lands *just above*
`t = 1` with Shannon's own printed radii, so it **fails** the classic `0.8 ≤ t ≤ 1` band while
conforming to the symmetric `1 ± 0.02` band; the two verdicts are separate kernel facts
(`inst_SrTiO3_tooLarge_classic`, `inst_SrTiO3_conforms_symmetric`) plus `conforms_of_conforms_window_le`
(the monotonicity that says widening a band cannot lose a conforming candidate). **`BaTiO₃`** is the
band-flip row (`inst_BaTiO3_band_flip`): it does **not** lie in `[4/5, 1]` and **does** lie in
`[1, 11/10]`, which matches the experimentally tetragonal (ferroelectric) structure — the band
convention is a parameter of the theory, and the flip is a theorem rather than a footnote.
**`BaNiO₃`** is the negative row: it is outside even the tetragonal band
(`inst_BaNiO3_not_tetragonal`), which agrees with the literature's own hexagonal assignment — one
source prints `t = 1.13` from exactly the radii used here, and the exact value `90601/70688` sits
`0.032` below the `1.1` edge, a comfortable margin rather than a borderline pass. One
printed-versus-derived fact is the sharpest in the record: with **our** radius triple `SrTiO₃`'s exact
`t = 1.00159` is just above `1`, the literature's rounded reading of the *same* triple prints `t = 1.00`
(inside the band), and the primary text's own radii give a value below `1` — the verdict of `SrTiO₃`
flips with the radius compilation. That is why `inst_SrTiO3_tooLarge_classic` and
`inst_SrTiO3_conforms_symmetric` are two kernel facts about *one named triple*, and why every instance
docstring names its radii. The rule
rows decide: `Sr²⁺`/`Ca²⁺` and `Sr²⁺`/`Ba²⁺` are radius-rule admissible while `Ca²⁺`/`Ba²⁺` is not
(`inst_radius_Sr_Ca`, `inst_radius_Sr_Ba`, `inst_radius_Ca_Ba_fails`); the *reference-radius*
convention is visible in `inst_radius_convention_Ba_Cs` (`Cs⁺`/`Ba²⁺` is admissible with `Cs⁺` as the
reference and refused with `Ba²⁺`); a substitution can satisfy the radius rule while the band verdict
is lost (`inst_radius_ok_but_band_lost`, `Ca²⁺ → Sr²⁺` in `CaTiO₃`), which is the kernel-checked
statement that the *rule* and the *band criterion* are independent; the coupled pair
`Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺` is charge-balanced while a lone `Na⁺ → Ca²⁺` is not
(`inst_charge_coupled`, `inst_charge_single_fails`, `inst_charge_compensating_partner`); and the
electronegativity term is load-bearing rather than decorative (`inst_chi_load_bearing`: the same radius
difference is admissible at `Δχ = 0` and refused once the tolerance is dressed with `k = 1/10`,
`Δχ = 3/2`).

**中文。** 实例层在 **`ℚ` 中精确判决、完全不出现 `Real.sqrt`**（`ℚ` 层的正确性定理是 `inBandQ_cast`，把
平方判据搬运为实数判决；`zoneQ_eq_zone` 搬运可计算分类器）。六个文献行用 Shannon 的印刷半径（A 位
12 配位、B 位 6 配位、`rO = 1.40 Å`），上表每个数字都由三条独立路径复现——内核（平方判据上的 `norm_num`）、
lead 的精确有理脚本 `goldschmidt-instance-check.py`、以及 verifier 自己的重算——**0 处不一致**。

两条判决是诚实的头条：**`SrTiO₃`**（最典型的立方钙钛矿）用 Shannon 自己的印刷半径**刚好落在 `t = 1` 之
上**，因此**不满足**经典 `0.8 ≤ t ≤ 1` 带，却满足对称带 `1 ± 0.02`；两个判决是两条独立的内核事实，外加
`conforms_of_conforms_window_le`（加宽带不会丢失符合者）。**`BaTiO₃`** 是**带翻转**行：不在 `[4/5, 1]`、
在 `[1, 11/10]`——与实验上的四方（铁电）结构一致：带约定是理论的参数，翻转是**定理**而非脚注。
**`BaNiO₃`** 是负向行：连四方带都在外，与文献自己的六方相归属一致。规则行判决：`Sr²⁺`/`Ca²⁺` 与
`Sr²⁺`/`Ba²⁺` 半径规则允许，`Ca²⁺`/`Ba²⁺` 不允许；**参照半径约定**在 `Ba²⁺`/`Cs⁺` 行可见（以 `Cs⁺` 为
参照允许、以 `Ba²⁺` 为参照拒绝）；一个取代可以满足半径规则却丢掉带判决（`Ca²⁺ → Sr²⁺`），即**规则与带
判据彼此独立**；耦合对 `Na⁺ + Nb⁵⁺ ↔ Ca²⁺ + Ti⁴⁺` 电荷平衡而孤立的 `Na⁺ → Ca²⁺` 不平衡；电负性项是
**真正承载**的（同一半径差在 `Δχ = 0` 时允许，一经 `k = 1/10, Δχ = 3/2` 修饰即被拒绝）。

---

## 5. How to check it / 如何复核

```bash
proofs/scripts/check.sh --strict                      # whole tree: build + scan (measured: verdict PASS)
proofs/scripts/axioms.sh PhotoLean.Goldschmidt.Criterion \
    PhotoLean.Goldschmidt.conforms_iff_radius_window   # per-theorem axiom check
python3 theories/BEP/probes/bep-fidelity.py --theory goldschmidt       # 139/139, 0 differences
python3 theories/goldschmidt/probes/goldschmidt-instance-check.py      # exact-rational instance check
```

**English.** Measured verdicts: the bare whole-tree gate prints `build: OK`, `clean` (no unproved
placeholder, no custom axiomatic declaration) and `verdict: PASS`; every one of the theory's 98 public
theorems was put through `axioms.sh` and reported `verdict: PASS (only mathlib infrastructure axioms)`
(axiom list `[propext, Classical.choice, Quot.sound]`); the fidelity checker reports
`delivered, word-for-word: 139`, `not delivered yet: 0`, `signature differences: 0`; the off-kernel
instance script exits 0 with 0 mismatches. The statement authority is
`theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean` (139 declarations, 0 error), and the
plan of record with the full correction log is `theories/goldschmidt/plan.md`.

**中文。** 实测判决：裸跑全树门打印 `build: OK`、`clean`（无占位证明、无自定义公理）与 `verdict: PASS`；
本理论 **98 条公开定理**逐条经 `axioms.sh`，全部报告 `verdict: PASS (only mathlib infrastructure
axioms)`（公理表 `[propext, Classical.choice, Quot.sound]`）；保真检查器报告 `delivered, word-for-word:
139`、`not delivered yet: 0`、`signature differences: 0`；off-kernel 实例脚本 exit 0、0 处不一致。语句
权威是 `theories/goldschmidt/probes/goldschmidt-statement-skeleton.lean`（139 条、0 error），完整语句
修正日志在 `theories/goldschmidt/plan.md`。

---

## 6. Honest boundaries / 诚实边界

**English.** (i) **Premises, not theorems.** That an `ABO₃` perovskite is described by three radii,
that the ideal cubic geometry is `rB + rO = a/2` with A–O distance `a/√2`, and that a **band on `t`** is
the right empirical criterion are *declared modelling premises*; every statement is conditional on
them (plan §12). (ii) **The band is a parameter, deliberately** — and the record now says exactly which part of it is
attested: the primary source (retrieved and read in round 1) prints `0,8 ≤ t ≤ 1` verbatim, so
`classicLo = 4/5` and `classicHi = 1` are a *transcription* of Goldschmidt's own text, while
`tetragonalHi = 11/10` is a **declared** edge with no printed band behind it (the literature prints the
half-open motif `t > 1` with a contested distortion name; 19 printed band conventions are enumerated in
`LITERATURE.md` §T1 with sources, and the nearest printed `1.1` threshold states *formation*, not
tetragonal distortion). No band is hard-coded: `lo` and `hi` are hypotheses everywhere.
(iii) **The reference radius of the 15 % rule is a literature fact, not a free convention.** The
primary text prints "um nicht mehr als etwa 15 % (in Prozenten des kleinsten Radius)" — relative to the
**smaller** radius — so the delivered `radiusMatch_min_iff` (`↔ |r - r'| ≤ τ * min r r'`) *is* the
attested rule, and `RadiusMatch tau r r'` is this theory's **parameterized spelling** of it. The modern
literature varies between the larger and the smaller reference, which is why the parameterization is
kept; and `inst_radius_convention_Ba_Cs` shows the distinction is not cosmetic (a real pair whose
verdict flips with the reference ion). Every printed `t` is quoted with its radius triple, because the
record carries three different oxygen radii (`1.40 Å`, `1.35 Å`, and the primary text's own `1.32 Å`).
(iv) **Nothing is claimed about materials.** The printed radii enter as numbers with
provenance; the verdicts are statements about those numbers, not about measured structures. (v) **Not
formalized** (deliberate scope limits, plan §1.4): no energy model or formation-energy prediction, no
octahedral tilting (`a⁻a⁻a⁻` Glazer systems), no tolerance-factor refinement (Bartel's `τ`), no
octahedral factor `μ = rB/rO`, no temperature or pressure dependence, no coordination-number or
spin-state modelling beyond the choice of the printed radius. (vi) **The 15 % figure itself** sharpens the printed "etwa 15 %" into the declared
`tauGoldschmidt = 3/20`; what is proved is the window form, the *ratchet* (two chained 15 % steps drift
by `(1 + τ)² - 1 = 129/400`, `radiusMatch_comp_ratchet`), and the transfer to `Δt`. (vii) **The charge
rule is a declared systematization, not Goldschmidt's own criterion**: his text requires *stoichiometric
matching* and explicitly folds valence into the apparent radii, so `∑ dz = 0` is a later reading
(documented coupled substitutions with printed increment arithmetic are cited in `LITERATURE.md`
§S3.2.1, and the delivered ±1 instance pair is labelled a model instance there). (viii) **The chemical
rule's linearity has no source** (`chiTol = tol0 - k * |Δχ|` is a declared shape; the sources are
qualitative "field effects" or threshold statements), so only monotonicity in `|Δχ|` is proved. (ix)
**One printed radius is unverified**: `Mn³⁺(VI, high spin) = 0.645 Å` could not be confirmed from a
retrievable source in round 1, so the `LaMnO₃` row names the spin state in its docstring and the value
carries a round-2 to-do in the record — the row's arithmetic is kernel-checked *for the value used*.

---

## 7. The process, and what it found / 过程，以及它发现了什么

**English.** The engine's discipline is statement-first, and it paid off five times: **five authority
rows were FALSE as first drafted, and every one of them was caught by the kernel before delivery** —
either by the milestone prover's own work or by the lead's hand-derivation (§3.1 of the plan records
each with its counterexample):

| row | why it was false | fix |
|---|---|---|
| `goldschmidtZone_eq_tooLarge_iff` | the cascade tests `t < lo` first, so on an inverted band (`hi < lo`) a small `t` is `tooSmall` — witness `lo = 1, hi = 0, t = 1/2` | exact form `↔ lo ≤ t ∧ hi < t`, plus the `lo ≤ hi` corollary |
| `tolFac_mono_rO_of_lt` / `tolFac_anti_rO_of_lt` | `0 < rO` does not exclude the pole `rO = -rB`, where `t` jumps — witness `rA = -2, rB = -1, rO = 1/2, rO' = 2` | premise `0 < rB + rO` |
| `tolFac_rO_const_iff` | the quantifier ranges over positive `rO'` that can still hit the pole — witness `rA = rB = -1, rO = 1, rO' = 2` | premise `0 ≤ rB` added |
| `chiTol_anti` | its hypothesis was stated the wrong way round for an *antitone* dressed tolerance — witness `k = 1, χ = 0, χ' = 10, χ'' = 0` | hypothesis direction corrected (name kept) |
| `radiusMatch_refl` (draft) | `|r - r| = 0 ≤ τ * r` needs `0 ≤ r` | premise added |

Four more rows had **hypotheses that the kernel never consumes** and were therefore removed rather than
kept behind a lint suppression (`conforms_symmetric_band_iff`, `zoneQ_ideal_iff`,
`conforms_point_band_iff`, `inBandQ_ideal_iff`). Two lessons are now in `proofs/EXPERIENCE.md`: **a
claimed counterexample counts only once the kernel has checked both halves** (that the instance
satisfies every hypothesis *and* that the negated conclusion holds — one reported "false row" was
refuted this way), and **an artifact's "0 error" is a claim that must be measured after the last edit**
(the Sprint-0 risk probe was cited as kernel evidence before it had ever compiled; the rows it was
supposed to protect were caught by the milestone provers instead, and the record says so — the probe
now compiles and closes 105 of the 139 authority rows, the rest placeholders, which is what it is:
a risk probe, not the acceptance artifact). What the process did *not* need: any weakening of a
delivered row. Verification is independent: the verifier runs the gate itself and writes its own
adversarial probes — batch 1 (G1 + the Sprint-0 artifacts) returned **PASS with 0 HIGH findings**,
including a 1000-point exact-rational search over the four classifier rows (450 inverted bands, 100
degenerate bands) with 0 violations, and an independent recomputation of all six instance values.

**Verification history (independent verifier runs, each read-only and writing its own probes).**
Run 1 (milestone G1 + the Sprint-0 artifacts): **PASS, 0 HIGH / 6 MEDIUM / 9 LOW**, all findings in
the record layer; the run re-ran the four gates itself, reverse-engineered the six instance values,
and searched the four classifier rows over 1000 exact-rational triples (450 inverted bands, 100
degenerate ones) with 0 violations. Run 2 (milestones G2 + G3): **PASS**, with one HIGH that was again
*record-layer but inside a delivered file* — `Criterion.lean`'s docstrings repeated the sentence
"at `δ > 1` the band is empty", which the same verifier refuted in the kernel — and one genuine
defect: `radiusMatch_comp_ratchet` carried two hypotheses (`0 < r1`, `τ ≤ 1`) that the row does not
need (the triangle-inequality proof closes it with `0 ≤ τ` alone). Both were fixed the same round
(the row now has the weakest premise, plan §3.1 item 11); that run also re-proved the eight `private`
helpers of `Criterion.lean` independently — the blind spot of the fidelity checker. Run 3 (milestones
G4–G6 + the documentation plane) returned **INCOMPLETE with no HIGH**: the code face was measured green
(three modules build, the bare gate `PASS`, fidelity 139/139, `axioms.sh` 47/47), but it declined a
verdict because it had not reached the instance recomputation, the adversarial round or the document
audit; its two MEDIUM findings (the tree moved under it; the Sprint-0 probe sits outside the gate's
scan range by design) are disposed, and a bounded follow-up for the three un-checked items is running.
The honest summary: **every delivered declaration has passed an independent gate, and the only
findings that ever touched a delivered artifact were a false docstring and an over-strong hypothesis
— both caught by verification, not by luck.**

**中文（验收历史）。** 三个独立 verifier run（均只读、各写自己的探针）：run 1（G1 + Sprint-0 制品）**PASS，
0 HIGH / 6 MEDIUM / 9 LOW**，全部落在记录层，并自跑四门、反推六个实例值、对四条分类器行做 1000 点精确有理
搜索（450 倒置带、100 退化带）零违例；run 2（G2+G3）**PASS**，其中一条 HIGH 仍在**交付文件内部**——
`Criterion.lean` 的 docstring 重复了「δ > 1 时带为空」这句被同一 verifier 内核否证的话——另有一条**真缺陷**：
`radiusMatch_comp_ratchet` 带了两条该行不需要的前提（三角不等式路径只需 `0 ≤ τ`）；两者都已当轮修复（该行
现在用最弱前提，plan §3.1 item 11），且该 run 还**独立重证了 `Criterion.lean` 的 8 条 `private` 辅助引理**
（保真度检查器的盲区）。run 3（G4–G6 + 文档平面）返回 **INCOMPLETE、无 HIGH**：代码面实测全绿（三模块可 build、
裸门 PASS、139/139、`axioms.sh` 47/47），但因未走到实例重算、对抗轮与文档审计而拒绝给判决；它的两条 MEDIUM
（验收期间树在移动；Sprint-0 探针按设计位于门的扫描范围之外）已处置，三项未查的受限 follow-up 正在跑。诚实
总结：**每一条交付声明都过了独立验收门，而历史上唯一触及交付制品的发现是一句假 docstring 和一条过强的前提
——两者都是被验收抓到的，不是靠运气。**

**中文。** 引擎的纪律是 statement-first，它五次回本：**五条权威语句初稿为假，而全部在交付前被内核抓住**
（可能来自里程碑工人的自证，也可能来自 lead 的手推；plan §3.1 逐条记录反例）：分类器 `tooLarge` 行（级联
先测 `t < lo`，倒置带下小 `t` 被判 `tooSmall`，反例 `lo=1, hi=0, t=1/2`）；两条 `rO` 单调行（`0 < rO`
挡不住极点 `rO = -rB`）；`rO` 常数行（量词仍可命中极点）；`chiTol_anti`（对**反调**的修饰容差，假设方向
写反）；以及 `radiusMatch_refl`（缺 `0 ≤ r`）。另有四条带**内核从不消费的前提**的行，按纪律**删除**而不是
用 lint 抑制保住。经验库现有两条教训：**反例只有在内核同时验证两半之后才算反例**（有一条被这么驳倒的
「假行」报告）；以及**制品的「0 error」必须在最后一次编辑之后测量**（Sprint-0 风险探针在被引用为内核证据
时其实从未编译过，而它本应保护的行是里程碑工人在内核里抓到的，记录如实写明；该探针现已编译并闭合 139 条
权威行中的 105 条、其余为占位——它本来就只是风险探针，不是验收制品）。这个过程**从未需要削弱任何一条已交付
语句**。验收是独立的：verifier 自己跑门并写自己的对抗探针——批 1（G1 + Sprint-0 制品）返回 **PASS，0 条
HIGH**，其中包括对四条分类器行的 1000 点精确有理搜索（450 个倒置带、100 个退化带）零违例，以及六个实例值
的独立重算。

---

## 8. Inventory / 清单

**English.** `PhotoLean/Goldschmidt/` — 6 modules, **139 public declarations** (G1 `Basic.lean` 29 =
15 definitions + 14 theorems; G2 `Rules.lean` 18 = 5 + 13; G3 `Criterion.lean` 24 + 8 `private`
helpers; G4 `Sharp.lean` 12; G5 `RatModel.lean` 22 = 10 + 12; G6 `Instances.lean` 34 = 11 + 23), all
word-for-word against the authority; 98 public theorems, each through `axioms.sh`; zero unproved
placeholders, zero custom axiomatic declarations. Leaves:
`theories/goldschmidt/{plan.md,TASKS.md,LITERATURE.md,RESULTS.md,probes/}` plus
`theories/goldschmidt/literature/INSTANCE-DATA.md`; probes: the statement authority, the Sprint-0 risk
probe, seven API-calibration probes and the off-kernel instance cross-check. The theory enters the
repository's relation graph through the **no-edge registry** (`PhotoLean/Relations.lean` §10,
`theories/RELATIONS.md` §2.5) with the shape look-alike N4 recorded against Sabatier.

**中文。** `PhotoLean/Goldschmidt/`——6 个模块、**139 条公开声明**（G1 29 = 15 定义 + 14 定理；G2 18 =
5 + 13；G3 24 条另加 8 条 `private` 辅助；G4 12；G5 22 = 10 + 12；G6 34 = 11 + 23），全部与权威逐字一致；
98 条公开定理逐条过 `axioms.sh`；零占位证明、零自定义公理。叶子：
`theories/goldschmidt/{plan,TASKS,LITERATURE,RESULTS}.md` + `probes/` + `literature/INSTANCE-DATA.md`；
探针包括语句权威、Sprint-0 风险探针、7 个 API 校准探针与 off-kernel 实例交叉检查。该理论经**无边登记**
接入仓库关系图（`PhotoLean/Relations.lean` §10、`theories/RELATIONS.md` §2.5），并记有对 Sabatier 的
N4 形状相似登记。
