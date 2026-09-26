# PhotoLean 全面审查报告（六理论 · 关系图 · 引擎）——第二轮外部审查

> 审查对象：工作区根目录（即任务说明中的 `new_lean2/`）全部交付源码与文档面。
> 审查基准日：`git` HEAD `cddad0f`，工作树 clean（实测 `git status --porcelain` 为空）。
> 审查方式：全部结论以**一手实测**为准——本环境工具链符号链接可解析，因此与任务说明 §3.3
> 的预设不同，本审查**实际执行了**完整构建、三层验收门、16 条公理探针、6 个保真脚本、
> 实例交叉检查与全部可数声称的独立复数。另有一个只读委托代理对三个较新理论
> （Kasha/Sabatier/Goldschmidt，18 文件约 6,200 行）做了全文通读扫描，其最重要发现（F1）
> 已由本审查者**亲自在内核中复核确认**。本报告仅在 `review/` 下新增本文件，未修改任何
> 仓库文件，未做任何 git 提交。

---

## 0. 证据等级自报（按任务说明 §3.3 要求）

**等级：实测复现**（任务说明预设的"无法本地构建"在本环境不成立）。

实际执行并留痕的验证（全部在仓库根目录）：

| 命令 | 结果 |
|---|---|
| `proofs/scripts/lake build` | exit 0，"Build completed successfully." |
| `proofs/scripts/check.sh --strict` | 叶数据面 6 理论 5/5、build OK、扫描 clean、**verdict: PASS** |
| `proofs/scripts/axioms.sh` × 16 条关键定理（Relations 8 条 + Marcus/Goldschmidt/Kasha/Sabatier 主定理 8 条） | 16/16 **PASS**，足迹恰为 `[propext, Classical.choice, Quot.sound]` |
| 6 个保真脚本（marcus / bep / hammond / kasha / Sabatier / goldschmidt） | 51/191/102/150/132/139 逐字一致，**全部 0 签名差异** |
| `python3 theories/goldschmidt/probes/goldschmidt-instance-check.py` | exit 0，"every asserted number reproduced exactly (0 mismatches)" |
| 声明计数（自带块注释剥离的解析器，方法学与 `bep-fidelity.py` 一致） | 与文档**逐项精确吻合**（见附录 B） |
| `/tmp/f1_probe.lean`（内核探针） | 证实 F1（见第三部分 M1） |

**残余信任根**（如实声明）：① mathlib 以缓存 olean 链接，未从源码重建 mathlib 本身
（标准假设，非本审查能覆盖的范围）；② 验收脚本是仓库自产物——我逐行读了 `check.sh` 的
扫描正则与 `axioms.sh` 的判定逻辑，其失效方向是安全的（假 FAIL 而非假 PASS），且历史上
三个门 bug 全部朝"误报"方向出错并被修复（EXPERIENCE.md:801-814 等）。

**不可用材料**：任务说明提到的辅助材料 `rewrite/lit/`（文献研究）与
`rewrite/formalize/new_lean2_review.md`（上一轮静态审查）**不在本文件系统**（全盘 find 无果）。
涉及它们的结论只能基于仓库内部证据。

**路径映射**：任务说明中的 `new_lean2/README.md` 等路径对应本工作区根目录下的同名文件
（`README.md`、`theories/RELATIONS.md`、`proofs/*`、`review/*`、`PhotoLean/`），下文一律用
仓库实际路径。

---

## 第二部分 · 假设评估（H1–H5）

### H1（假等价普遍存在）——判定：**尚未验证**；"普遍性"提法应放弃，"存在性"有一条现成的跨越路径

**同意自评，并补充三点。**

1. **仓库里没有一条严格意义的假等价裁决。** 逐条核对：E1-E6 是真等价（文献把它们当
   等价，内核也判等价——这是"真等价"裁决）；E7 是复合；O1-O3 是单向蕴含（其中 O3 诚实
   注明逻辑通道只是正性合取项，Relations.lean:159-168）；N1-N4 是形似实异——但**没有任何
   一条 N 配着"文献/社群把这两条当等价"的引证**。形似实异 ≠ 假等价：前者说"像但不同"，
   后者要求"被当作相同、实为不同"。
2. **最近的原材料已经在仓库里，只差形式化一步。** `proofs/EXPERIENCE.md:1150-1181`
   （BEP round-1g）记录了文献中被**静默等同**的三个 α 对象：(i) 电化学可观测转移系数
   （IUPAC Recommendations 2014 eq.(1)，printed p.259）；(ii) 模型的 BEP 斜率
   `transfer = 1/2 − x/(2λ)`；(iii) Butler–Volmer 对称因子 β。同一记录载明：IUPAC TR
   （printed pp.255-256）预言两力常数不等时"large deviations of β from 0.5"，即 β=α 的
   等同**需要额外前提**；且文献的互补律是 `αc + αa = n/ν`（IUPAC TR p.257），模型定理
   `transfer + reverseTransfer = 1` 只是其单电子特例。这就是"社群把两个对象当同一个、
   而机器可以判定何时不成立"的**有文献记录的实例**。跨越路径：把 β 与 α 形式化为共享
   签名下的两个不同谓词，在双抛物面模型里证明力常数不等时二者不等价，引 IUPAC TR
   pp.255-256 作为"被当作等价"的文献记录。这在现有模板能力域内（代数基质、一个
   milestone 的量级），且天然落在 BEP 模块的既有词汇里。
3. **"普遍现象而非个案"这半个提法站不住，应修正。** 六个理论永远给不出"普遍性"——
   那需要语料库级统计（对某个领域的命题对做系统抽样与裁决），是另一个数量级的工程。
   建议把 H1 改写为可检验的存在性命题：**"存在文献记录中被当作等价/可互换的命题对，
   形式化后被内核判定为不等价（并给出反例或前提差）"**——上面第 2 点表明这个存在性
   命题距离被证实只差一个 milestone；"普遍性"移入 future work。

**门槛是否必需？跨不过会削弱到什么程度？**（任务说明 §2 的直接提问）
- 对论文核心主张（关系演算存在且可机器检查、引擎能可靠建成它）：**不必需**。E/O/N/组合/
  无边五类登记已是完整的能力演示。
- 对动机叙事的最强版本（"假等价是普遍的病，我们没有工具诊断"）：**必需**。跨不过时，
  论证从"诊断并治疗一种普遍病"降为"提供诊断工具 + 一组形似病例系列（N1-N4）"。这仍然
  这仍然站得住，但权威引证只能支持"命名混乱存在"（IUPAC 自认），不能支持"等价误判
  普遍"——动机段从核心问题退为应用场景之一，冲突性标题（"Same Physics, Many Names"）
  失去支点。
- 结论：这不是生死门槛，是**天花板门槛**。鉴于跨越成本只有一个 milestone 且原材料
  已在仓库内，不跨越就缺少一个能把主张钉住的实例。

### H2（关系可被机械判定）——判定：**部分证实；"机械判定"措辞过强，应改为"机械可验证且可反驳"**

- **已证实的部分**（我全部复跑）：每条登记的边有内核证书（16/16 探针 PASS）；定义同一性
  真正可判定（`rfl` 证书 = 编译期判定，且"证书失败即回归报警"的设计写进了
  Relations.lean:8-12 头注与 RELATIONS.md §2.3）；**非**蕴含由显式反例反驳（N2 的
  A=lam=−1 见证，Relations.lean:275-284；perLevel 的 rad≡ic≡1 见证泄漏 6/7；BEP I11 四族
  二阶差分为负，Instances.lean:357-363）。
- **未证实/不成立的部分**：(a) 关系候选的**发现**不是机械的——每条边都是人/agent 猜想后
  由内核验证的；(b) 无边登记是 prose + import 结构事实（Relations.lean:510 自己标注
  "documentation, not theorems"）；(c) 对任意实数算术命题对，蕴含/独立一般**不可判定**——
  工程演示的是半可判定（证明搜索）+ 可反驳（反例搜索），不是判定过程。
- **修正后的提法**："在共享签名下，关系候选为真时可被机器验证、为假时可被机器反驳
  （显式见证），非关系连同建模理由被登记"——这与交付完全一致，且不需要弱化任何已证
  内容。
- **附带发现（措辞过强）**：RELATIONS.md:370-375（§5(i)）称 Σ "由**类型**与内核级证书
  固定，而不再靠命名纪律"——"由类型"无对应物：仓库里不存在签名 structure（上轮 REVIEW
  的 S1 建议未实现），证书是 **opt-in** 的（第四个理论若不写自己的证书，没有任何机制
  强迫它）。对已交付理论，钉合是机械的；对未来理论，机制仍是纪律。这句话应改为
  "由内核级证书固定（对已登记者机械，对未来理论仍需登记动作）"。

### H3（引擎可靠、终止判据可信）——判定：**部分证实；数学层的终止判据经受了独立复跑，记录层是复发性薄弱点**

- **数学层：证实（在本域内）。** 三层门在我手里全部通过；门本身被审计过且修过三个真
  bug（`axioms.sh` 长名假 FAIL、保真器漏 `structure` 只覆盖 143/144、`check.sh` 正则漏
  `admit`/`private axiom`——后两者我确认已修：check.sh:144 现行正则含 `admit` 与
  `(private|protected)?(axiom|constant)`）。verifier 独立性有真实咬合力：Kasha run-3 的
  HIGH finding 是"验收记录声称存在的 run-2 板上记录不存在"（TASKS.md:317-338）；
  Goldschmidt 对抗轮**反驳了 prover 自己 docstring 里"三前提均承载"的声称**并迫使以更弱
  前提重新交付（EXPERIENCE.md:3387-3423）——系统纠正了自己的过度声称，这是"可靠"的
  最强形态证据。
- **记录层：反复失守，且失守模式已被工程化补丁。** 实测事故清单（全部有自登记）：
  未编译的探针被先行引用为 Sprint-0 证据（EXPERIENCE.md:3206-3215，"an artifact may not
  be cited as evidence before its gate command has been run"）；两份 verifier 报告因
  abort 丢失（3361-3385）；commit message 过度声称 README 已同步而实际未动（3463-3468）；
  文档面在 Kasha run-3/run-4 连续两轮 FAIL（11 findings → 修 7 漏 4）。AGENTS.md 铁律 8③
  与 METHOD.md §6.5 是这些事故的补丁——补丁本身又漏过一次（本次审查仍找到 7 处文档
  漂移，见第三部分）。
- **"终止判据可信"的精确表述**：对数学，可信来源是"内核 + 扫描 + 公理探针"三层**联合**
  （裸 `lake build` 会被 sorry 骗过——README:62-63 自己写明）。ENGINE.md:24 的
  "`lake build` 通过即真"按字面**不成立**，应改为"三层门通过即真"。对文档，终止判据
  历史上四次失守，当前靠铁律 8③ 的同步清单维持——这是流程补丁，不是机械门，本次审查
  仍能找到漏网（M6-M9）。
- **外部验证现状**：上一轮 REVIEW（三理论）+ 本轮（全仓）。两轮模式一致：数学层干净、
  文档层漂移。"缺乏外部验证"的自评可以更新为"已有两轮外部验证，结论模式稳定"。

### H4（可复用模板）——判定：**部分证实；比上一轮审查时的证据强一档，但边界声明必须原样保留**

- **新增证据**：基质从 1 种扩到 4 种（双抛物面 / 有限速率级联 / 描述符优化 / 纯几何），
  稳定核四槽（Basic/Sharp/RatModel/Instances）6/6 保持；中间槽变异被**记录且可预测**
  （METHOD.md §1 表：Marcus 拆 Barrier+Rate，Goldschmidt 无 Compose 而有 Rules）；四种
  基质各有一条"刻意避开的路"（测度论 / 微分 / Shannon 表函数化，METHOD.md §3）——负结果
  登记是模板成熟度的标志而非缺陷。
- **"过拟合个案"质疑的当前答案**：不是刚性抽象，是**带记录变异点的良好默认**。判据：
  变异发生在哪是系统性的（中间槽），不变的是什么是可陈述的（五件套），且第五、六个
  理论确实按预测变异（Goldschmidt 换了槽位类型）。
- **必须保留的边界**（METHOD.md §7 自己写了，论文不得丢）：四种基质全部是初等实代数 +
  有限和 + 一个 `exp`。未在分析（ODE/谱）、测度论、概率语义上受压；K4b 是最近的一次
  边界实测（命题 types 但 ~100 行测度论证明超预算，EXPERIENCE.md:1968-1973）。
- **提法修正**：任务说明 §2 的"6 槽模板被 5 个理论复用"字面不成立——6 槽是三理论时代
  的旧貌（上轮 REVIEW §7.1 已判"字面上已不成立"），现状是"4 稳定槽 + 理论特异中间槽"，
  且是 6 个理论。论文若沿用旧提法会被 METHOD.md 自己的表格反驳。

### H5（对化学的实际价值）——判定：**部分证实；"暴露隐含前提"有硬证据，"推向可推导"目前是能力演示而非基础设施**

硬证据（全部可复跑，我逐条核过语句）：
- **SrTiO₃ 判决随半径汇编与带约定翻转**：同一组 Shannon 印刷半径，经典带 0.8≤t≤1 判
  **出带**（t² = 161312/160801 > 1，我手算复核了该分数），对称带 1±1/50 判**符合**；
  文献的四舍五入读法给 t=1.00（带内），而一手来源自己的另一组半径三元组给 <1。两个
  判决作为**两条内核事实**交付而非注释（Goldschmidt/Instances.lean:104-127）。这是
  "教科书判决依赖隐含约定"的可检查证明。
- **直觉判据不充分**：逐层 `k_IC ≥ k_rad` 型条件不保证 Kasha 纯度——见证 rad≡ic≡1 在
  N=2 泄漏份额 6/7（Sharp.lean:341-344；委托代理用内核探针确认 KashaWithin 恰在
  tol=6/7 成立、5/6 失败）。
- **一手文献族被模型证伪**：四个 BEP 族仿射斜率符合但二阶差分为负（如 F1 族
  −9/52），等曲率双抛物模型被内核级否定（BEP/Instances.lean:357-363）；RESULTS 如实
  报告"希望至少一族 conforming 的愿望未满足、也不假装满足"。
- **精确规则的读法远强于教科书口语**：`KashaRule ↔ 最低态以上全部无辐射`
  （Criterion.lean:252-253），且"规则不是模型定理"被 `not_kasha_universal` 钉住——
  可用形式是容差版，这个区分教科书不做。
- **前提考古**：15% 规则的参照离子基准（较小离子）是文献事实而非定理、`0.732` 不是
  Pauling 冠名（Hüttig 1920/Magnus 1922）、电荷和不能区分取代族（负结果登记）——
  EXPERIENCE.md:3449-3458。

**限制（同样硬）**：全部价值在**声明的模型内部**；实例层判决的是印刷数字不是材料性质
（三个理论的 Instances 头注都自带免责声明，委托代理逐条核对）；没有任何化学社群 uptake
的证据。"把唯象理论推向可推导"目前的准确时态是"证明了能推"（六例），不是"已被推"
（无人使用）。论文若不在 Discussion 里自己说清这一点，读者会替你说。

---

## 第三部分 · 工程审查（六条标准，分级）

**总判**：阻断性 **0**；严重 **0**；轻微 **11**（M1-M11）。上一轮 REVIEW 的 F1-F6
六项**全部已处置**（逐项复核见 §3.7）。数学层在我能构造的全部造假面扫描下阴性。

### 3.1 标准①：名实相符 —— **通过（有保留项）**

抽查的主定理全部真实表达对应化学命题，无循环、无结论塞假设：
- `descriptor_sharp`（Marcus/Sharp.lean，探针 PASS）、`hammond_sharp`、
  `volcano_descriptor_iff`（Sabatier/Sharp.lean:288-291：`VolcanoDescriptor` 独立定义为
  **唯一全局最小点**，Basic.lean:64-65，两个合取项均有承载——plateau 见证恰好杀死
  唯一性合取项）、`conforms_iff_radius_window`（Goldschmidt/Criterion.lean:278-289，
  对**每个**带精确、无带非空前提，我核了倒置带两侧同假的论证）、
  `kashaRule_iff_rad_zero`（Criterion.lean:252，归纳证明，非定义展开）。
- 委托代理对 18 个文件的正则扫描：所有名字含 "iff" 的定理语句都含 `↔`（0 违例）；
  全部 headline 为真双条件，单向的行都以 `_of_` 命名。

**保留项（全部轻微，见清单）**：M1（Kasha 非空洞行语句平凡）、M2/M3（两条 docstring
强于语句）、M4（一行定理名强于语句，方向由伴生行钉住）、M5（Sabatier 区间见证按构造
平凡，docstring 已诚实框定）。

### 3.2 标准②：关系判定严格性 —— **通过（两处措辞问题：M9、M10）**

- **无 `Iff.rfl` 伪造等价**。全仓 `:= rfl / Iff.rfl / by rfl` 实测 14 处 + 2 条
  unfold-后-rfl（`kernel_marcusIC`、`marcus_rate_eq_activity`）：全部是 Eq 级证书或
  **自身定义**的展开，且全部带 definitional/certificate 标注。实质性同一性被**刻意做成
  非定义的**：`BEP.transfer` 取线性响应体 `1/2 − x/(2λ)`（BEP/Basic.lean:59），迫使
  `transfer_eq_tsCoord_bridge` 走 `field_simp` 证明并携带 `lam ≠ 0`——反伪造设计的直接
  证据。唯一的 `Iff.rfl`（Marcus/RatModel.lean:91）在两条实质重写之后闭合定义展开，
  与上轮审查结论一致。
- **条件性边随带前提**：`kashaWithin_one_marcus` 的建模同一性 `hic : ic 1 = marcusIC …`
  是签名里的显式假设（Relations.lean:308-315；Kasha/Compose.lean 头注明确"conditional"
  并引 Jortner energy-gap law 作为模型外的真实机制）。
- **共享签名 Σ**：对已交付理论由 8 条 `rfl` 证书机械钉合（回归报警语义明确）；但无
  签名类型、证书 opt-in——见 M10。
- **无边登记的依赖事实复核吻合**：Goldschmidt 树 import 实测 = §10 声称（Basic/Rules ←
  Mathlib；Sharp ← Basic+Rules+Criterion；Instances ← 四模块、不 import Sharp）；
  Kasha/Compose 只 import Kasha.Basic + Marcus.Basic；Sabatier 只消费 BEP.Basic。
  15 个理论对逐一清点，§2.5 覆盖无遗漏。

### 3.3 标准③：非平凡性 —— **通过（一处语句级弱点：M1）**

六理论全部有**具名**模型与非模型定理（非注释声称）：Marcus `inst_I4_*`/`inst_I7_*`；
Hammond `inst_I4_family_descriptor`/`inst_I8_nonphysical_fails_*`；BEP `inst_nonvacuous`
（Instances.lean:570，四向合取）+ I11 证伪族；Kasha `kashaThreshold_attained`
（Sharp.lean:319-321，达到性 ∧ 不可改进性）/`not_kasha_universal`（Criterion.lean:389-390）/
`vavilov_premise_necessary`；Sabatier `not_descriptor_flat/plateau/mixedSign` +
`antiVolcano_monotone`（三见证恰好穷尽 αA·αB ≤ 0 的符号形态，与 iff 互补）；Goldschmidt
`exists_conforming`（**紧性**见证：打到 t=lo）/`exists_tooSmall`/`exists_tooLarge`
（Criterion.lean:399/412/421，后两条无条件）+ `witness_band_flip`。
唯一语句级弱点是 M1（`kashaDescriptor_nonvacuous` 按语句平凡——但该理论的真非平凡性由
上列兄弟行承载，故降为轻微）。

### 3.4 标准④：零 sorry / 零自定义公理可信度 —— **通过（本审查置信度最高的一项，因为全链条复跑）**

| 检查面 | 实测结果 |
|---|---|
| `sorry`/`admit` in `PhotoLean/` | **0**（裸 grep 与注释剥离解析双确认） |
| 自定义 `axiom`/`constant` | **0**（含 private/protected 变体） |
| `native_decide` | **0 使用**（仅 2 处禁用说明注释，BEP/RatModel.lean:16、BEP/Instances.lean:16）；16+18 条探针足迹中无 `Lean.ofReduceBool` |
| `opaque`/`unsafe`/`partial def`/`@extern`/`@implemented_by`/`macro_rules` | **0** |
| `#eval`/`#print`/`#check`/`#guard_msgs` 命令 | **0**（仅 docstring 提及）；实例判决全部是 `norm_num`/`decide` **证明项** |
| `maxHeartbeats`/`maxRecDepth`/`warningAsError` 放宽 | **0** |
| `set_option` 清单 | 仅 `linter.unusedVariables false`（逐声明 `in` 作用域）与 `autoImplicit false`（更严格，Kasha/Sabatier/Goldschmidt 全模块）——无其他 |
| `.choose` | 全仓 1 处（BEP/Sharp.lean:162），从存在性**前提**解包见证，合法；反例全部显式构造（−1、rad≡ic≡1、apex (1/2) 0 (1/2) 1 等），无以 choice 造反例 |
| `open Classical` | Kasha 5 文件、Sabatier 6 文件（新理论；上轮"0 处显式 Classical"仅对旧三理论成立）——仅开命名空间，公理足迹经探针确认仍在允许集内 |
| 公理探针 | 本审查 16 条 + 委托代理 18 条 = **34 条全部** `[propext, Classical.choice, Quot.sound]` |
| probes 目录的 646 处 `sorry` | 全部在 `theories/*/probes/*`（语句骨架，故意占位）；`SOURCE_DIRS="PhotoLean"` 使交付扫描不覆盖——**两个说法都对、含义不同**，与任务说明 §3.3 一致 |

### 3.5 标准⑤：文档-代码一致性 —— **通过（7 处轻微漂移：M2、M4、M6-M9、M11 + 记账枚举一处不含）**

**先说吻合的（这部分是仓库的强项，全部经我独立复数）**：六理论声明数 82/102/191/150/
134/139 与 README、各 RESULTS.md **逐项精确吻合**；总数两种口径都对（852 = 六理论 +
Kernel 8 + Relations 46，不含 Smoke；854/677 = 含 Smoke 的 2 条，即任务说明口径；
大纲笔记口径为 852/675）；Relations 46 条的**两批记账逐条吻合**（28+18、
10 复用 + 2 证书 + 6 本证、真新数学 4 行）；Sabatier 107 定理 + 27 定义级 + 36 private、
Goldschmidt 98 公开定理 + 8 private、Kasha 150（110 定理 + 37 def + 2 inductive +
1 structure）——全部实测吻合；`defaultTargets` 41/41 覆盖全模块（"扫描覆盖、构建不覆盖"
的洞不存在）；azulene 三路线数字（20.6/40.3/23.0）与 I11t 容差翻转在 RESULTS.md:242-252
与 Instances.lean 一致；任务板无真未勾行（Marcus/kasha 各 1 处 `[ ]` 是表头**行格式
示例**，非任务）；无 "[x]+todo"、无 "is running"/"in review" 残留（铁律 8③ 的同步在
当前状态下是干净的）。

**发现的漂移（全部轻微，给修法）**：见下方清单 M2、M4、M6-M9、M11。另有一处
**记账枚举缺项**：RELATIONS.md:408-412（§5(ix)）说第二批"10 条逐字 re-export
（K1–K3, S1–S4）"——该枚举按声明数只有 9 条（K1-K3 = 3，S1-S4 = 6，因 S2/S4 各含两条），
第 10 条是 `marcusIC_pos`（Relations.lean:343-346，代码里标注 "supporting row"），未列入
枚举也未列入 §2.4 的表。**总数 10 是对的**（我逐条数过），只是枚举漏了名字。修法：
枚举补 `marcusIC_pos`。一个以记账诚实为招牌的文档，记账枚举本身要经得起逐条点名。

### 3.6 标准⑥：模板可复用性 —— **部分成立**（见 H4；文档面补充一条）

METHOD.md 是合格的模板文档：每条声称点名证据文件、边界自认（§7）、坑清单实测（§6）。
问题不在 METHOD.md 而在**流通口径**：任务说明与论文侧仍在说"6 槽模板"，METHOD.md §1
自己已是"4 稳定槽 + 变异中间槽"。修法：论文 §3.3 直接以 METHOD.md 表格为准。

### 3.7 轻微问题清单（M1-M11，全部附文件 + 行号 + 修法）

| # | 级别 | 问题 | 位置 | 修法 / 验证方式 |
|---|---|---|---|---|
| M1 | 轻微（发现类中最实质） | `kashaDescriptor_nonvacuous : ∃ rad ic, KashaDescriptor rad ic` **按语句平凡**：`KashaDescriptor := ∃ N, KashaRule · N`，而 `KashaRule · · 0 ↔ upperYield · · 0 = 0` 无条件成立（`upperYield_zero`），故**任意**阶梯都满足描述——我在 `/tmp` 探针里一行证明 `∀ rad ic, KashaDescriptor rad ic`（exit 0）。证明体构造的 N=1 见证是真的，但语句没钉住 N≥1/RateData。这正是仓库自己在 Hammond Sprint-0 抓过的失败类（"三分类重言式刻画不了任何东西"，EXPERIENCE.md:785-787）——这次漏网是因为理论级非空洞性由兄弟行承载 | PhotoLean/Kasha/Basic.lean:135、Criterion.lean:402；对照 Basic.lean:261,288 | 语句改为 `∃ rad ic, RateData rad ic 1 ∧ KashaRule rad ic 1`（已交付见证原样满足；按铁律 3 属"最弱前提/最强结论"修订，记入 plan §3.1）；验证：改后重跑 `bep-fidelity.py --theory kasha` 应报该行为 signature difference 并被登记 |
| M2 | 轻微 | I7 docstring 声称 "6/7 > 1/2" 与逐层 ic≥rad，但其语句只证 `upperYieldQ … = 3/4`；6/7 由 I6+I7 合成、ic≥rad 在 ℝ 侧 Sharp 行 | PhotoLean/Kasha/Instances.lean:121-123 | docstring 改为"与 I6 合成得 6/7"，或补一条把份额钉成单定理的行（委托代理已内核确认 6/7 数值本身无误） |
| M3 | 轻微 | `perLevel_criterion_insufficient` 形式化的逐层条件是混合式 `rad i * decay (i-1) ≤ ic i * decay i`，非字面 `ic i ≥ rad i`；两读法一般不等价（本见证 rad≡ic≡1 对两读法都以等号成立，结论稳健），但仓库没有以字面读法为假设的反驳定理 | PhotoLean/Kasha/Sharp.lean:341-344 | 补一行以 `∀ i, rad i ≤ ic i` 为假设的同型反例（同一见证即可），或在 docstring 明示两种读法之别 |
| M4 | 轻微 | `inst_SrTiO3_tooLarge_classic` 语句只是 `¬ inBandQ …`（出带，方向未指明）；"tooLarge" 由伴生行 `inst_SrTiO3_zone_tooLarge`（:134-135）钉住 | PhotoLean/Goldschmidt/Instances.lean:115-116 | 名字改 `not_inBand` 或在 docstring 首句点名伴生行（现 docstring 已有解释，属打磨项） |
| M5 | 轻微 | Sabatier `exists_optimal/tooWeak/tooStrong/nearOptimal` 按构造平凡（`Optimal apexD dE := dE = apexD`，见证 `⟨apexD, rfl⟩`）；且 Instances 无具名正面 `VolcanoDescriptor` 实例行（正面由全称定律 `volcano_descriptor_of_physical` 覆盖）。docstring 已诚实框定为"判决词汇的非空洞性" | PhotoLean/Sabatier/Criterion.lean:337-353、Basic.lean:88-98 | 保持现状可接受；若要更强，补一条具体参数的正面 descriptor 行 |
| M6 | 轻微 | README Goldschmidt 构成"（含 15 条定义与 1 个归纳类型…）"与实测不符：实际 98 定理 + 40 def + 1 inductive = 139。"15"只是 G1 Basic.lean 的定义级计数（RESULTS.md §8 的 "G1 29 = 15 定义 + 14 定理"），被误挂到全理论上。README 是自称的"交付状态单一真源"，此项优先级最高 | README.md:34；对照 theories/goldschmidt/RESULTS.md:406-409 | 改为"（98 定理 + 40 定义 + 1 归纳类型；另有 8 条 private）" |
| M7 | 轻微 | 大纲笔记的 "12,773 行 Lean"与同一 HEAD 实测 12,812 不符（前一提交 12,804——不匹配任何近期状态，疑为更早草稿数）；且同句口径混用：41 模块**含** Smoke，852/675 **不含** Smoke（含 Smoke 应为 854/677，即任务说明口径） | 大纲笔记:3（已移出仓库） | 重跑 `find PhotoLean -name '*.lean' \| xargs cat \| wc -l` 更新；声明 Smoke 口径（建议：论文报 854/677/41，注明含冒烟模块） |
| M8 | 轻微 | RELATIONS.md §7 复核块列 6 条保真命令，中文半段说"六个保真探针…139"，英文半段说 "the **five** fidelity probes …(51, 191, 102, 150, 132)"——英文半段陈旧（Goldschmidt 登记是"comment-only extension"时漏更的又一处） | theories/RELATIONS.md:511-513 vs 518-519 | 英文补 sixth/139 |
| M9 | 轻微 | Relations.lean 头注 "The **five** delivered theories share one mathematical substrate"双重失准：现为六理论；且按 RELATIONS.md §1，Kasha/Sabatier 本就不是双抛物面对象的读法（经组合边与形似簇接入） | PhotoLean/Relations.lean:4 | 改为 "The delivered theories are pinned to one shared kernel through certificates, compositions and a no-edge registry" 一类；这是仓库自己命名的"状态翻转接缝"**第五例**——第六理论登记只改了 §10，头注漏改 |
| M10 | 轻微 | "Σ 由**类型**与内核级证书固定，不再靠命名纪律"——仓库无签名 structure（上轮 S1 未实现），证书 opt-in：未来理论不写证书就没人拦得住它复用 `lam` 名字赋异义 | theories/RELATIONS.md:370-375（§5(i)）| 措辞降半格（"对已登记理论机械、对未来理论仍需登记动作"），或实现 S1 |
| M11 | 轻微 | ENGINE.md "Lean 内核不可 hack：`lake build` 通过即真"按字面不成立（sorry 也过 build；README:62-63 是正确口径"返回 0 不是验收，必须三层齐备"）——契约文档与 README 口径不一致 | proofs/ENGINE.md:24 | 改为"三层门通过即真" |

**仓库外文档的陈旧数字**（不属仓库缺陷，但论文/提示词侧应更新，避免带病继承）：
- 任务说明 §3.1 称 EXPERIENCE.md "42 条经验"——实测 **79** 条带日期条目
  （`grep -c "^## 2026"`），含 FAIL/LESSON/事故类的失败素材远多于"4 条 FAIL 路径"。
- 任务说明 §2 H4 "6 槽模板被 5 个理论复用"——见 H4 修正。

### 3.8 上一轮 F1-F6 处置状态复核（全部已处置）

| 上轮项 | 现状 |
|---|---|
| F1 check.sh 正则漏 admit/private axiom | **已修**：check.sh:144 现行正则含 `admit` 与 `(private\|protected)?(axiom\|constant)` |
| F2 Barrier.lean 文件级 linter 关闭 | **已修**：Barrier.lean:79,112 均为 `… in` 逐声明作用域，头注注明 "per declaration" |
| F3 `lamTotal_pos` 笔误 | **已修**：RESULTS.md:174 与 RESULTS.en.md:169 均作 `lam_total_pos` |
| F4 hammond 任务板属主矛盾 | **已修**：H4 节头与行体均为 prover_a（TASKS.md:97-102），偏离备注保留（:173） |
| F5 README 现状/镜像节 | **已修**：现状节含六理论；镜像节改为"历史镜像（冻结）"并登记三次漂移实证 |
| F6 Marcus 时代语言例外 | **已登记**：README.md:109-110 如实登记既有例外 |

---

## 第五部分 · 风险与缺口（高 → 低）

**1.（中）文档漂移是慢性病。**
两次外部审查 + 本次 7 处新漂移（M2/M4/M6-M9/M11）+ 历史四次接缝 + 三次镜像漂移——
模式稳定：**数学层不漂、记录层必漂**。缓解：数字声称集中在一个可再生成的附录，并由脚本复算。

**2.（低）技术信任残余。**
mathlib olean 缓存信任根（标准）；门脚本为仓库自产物（我读过，失效方向安全）；
Classical.choice 足迹（允许集内，34 条探针确认）。无阻断项。

## 附录 A · 本审查实际执行的命令

```bash
proofs/scripts/lake build                                    # exit 0
proofs/scripts/check.sh --strict                             # verdict: PASS
proofs/scripts/axioms.sh PhotoLean.Relations <8 条定理>       # 8/8 PASS
proofs/scripts/axioms.sh PhotoLean.{Marcus.Sharp,Kasha.Criterion,Kasha.Sharp,
  Kasha.Compose,Sabatier.Sharp,Goldschmidt.Criterion,Goldschmidt.Rules} <8 条>  # 8/8 PASS
python3 theories/Marcus/probes/marcus-fidelity.py             # 51/51, 0 差异
python3 theories/BEP/probes/bep-fidelity.py [--theory kasha|Sabatier|goldschmidt]  # 191/150/132/139, 0 差异
python3 theories/hammond/probes/hammond-fidelity.py           # 102/102, 0 差异
python3 theories/goldschmidt/probes/goldschmidt-instance-check.py  # exit 0, 0 mismatches
# 注释剥离声明计数（方法学同 bep-fidelity.py）：82/102/191/150/134/139 + Kernel 8 + Relations 46 + Smoke 2
# 造假面扫描：sorry/admit/axiom/constant/native_decide/opaque/unsafe/partial/@extern/
#   @implemented_by/macro_rules/#eval/#print/#check/#guard_msgs/maxHeartbeats → 全 0（交付目录）
/tmp/f1_probe.lean                                            # F1 内核确认（exit 0）
```

## 附录 B · 数字声称对照表（文档值 vs 本审查实测）

| 声称 | 出处 | 实测 | 判决 |
|---|---|---|---|
| 41 模块 | README / 大纲笔记 | 41 | ✅ |
| 82/102/191/150/134/139 | README:15-35 | 逐项同 | ✅ |
| 852 声明 / 675 定理 | 大纲笔记:3 | 852/675（不含 Smoke） | ✅（口径注明后） |
| 854 声明 / 677 定理 | 任务说明 | 854/677（含 Smoke 2 条） | ✅ |
| Relations 46 条、两批记账 | RELATIONS.md:9,407-412 | 46；28+18 构成逐条吻合（枚举漏 `marcusIC_pos` 一名，总数对） | ✅（枚举补名） |
| Kernel 6 定义 + 2 定理 | RELATIONS.md:11 | 同 | ✅ |
| 保真 51/191/102/150/132/139，0 差异 | README / RELATIONS §7 | 六脚本全过 0 差异 | ✅ |
| Goldschmidt 98 公开定理、8 private | RESULTS.md §8 | 同 | ✅ |
| Sabatier 107+27 公开、36 private | README:28 | 同 | ✅ |
| 12,773 行 Lean | 大纲笔记:3 | **12,812**（HEAD）/12,804（前一提交） | ❌ M7 |
| README Goldschmidt "15 条定义与 1 个归纳类型" | README:34 | 98 定理+40 def+1 ind | ❌ M6 |
| "five fidelity probes (…132)" | RELATIONS.md:511 | 六命令/中文半段六个 | ❌ M8 |
| "five delivered theories" | Relations.lean:4 | 六理论 | ❌ M9 |
| EXPERIENCE "42 条"（任务说明） | 任务说明 §3.1 | 79 条 | ❌（仓库外） |
| probes 数百处 sorry | 任务说明 §3.3 | 646 处，全在 probes | ✅ 两说法都对 |
| defaultTargets 全覆盖 | ENGINE.md:62-63 预警 | 41/41 | ✅ |
| 任务板 0 未勾真任务 | 各 TASKS.md | 0（2 处 `[ ]` 为行格式示例） | ✅ |

——审查完毕。本报告仅新增 `review/FULL-REVIEW-2026-09-21.md`，未修改任何既有文件。
