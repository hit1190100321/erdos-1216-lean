# Erdős 第 1216 题的 Lean 形式化

本项目完整形式化了 Erdős–Moser 等式猜想的否定结论，对应孙宇晨奖题库 **JSP-001021**。
数学结论早由 Reid 和 Parker 于 1970 年得到；本项目贡献是形式化，数学发现权属于原作者。

设 `f(n)` 是每个 `n` 点竞赛图都保证包含的最大传递子图阶数。原猜想为：

\[
\forall n\geq1,\qquad f(n)=\lfloor\log_2 n\rfloor+1.
\]

项目证明 **任意十五点竞赛图都有五点传递子图**，因此 `f(15) ≥ 5 > 4 = floor(log₂ 15) + 1`，
完整否定上述全称猜想。这一反例并未给出所有 `f(n)` 的精确值；原题的等式猜想不要求完成该额外任务。

主要定理位于 [SunPrize/Erdos1216.lean](SunPrize/Erdos1216.lean)：

```lean
theorem erdos_1216_disproved :
  ¬ (∀ n : Nat, 0 < n → guaranteedOrder n = Nat.log2 n + 1)
```

`guaranteedOrder_spec` 同时证明定义的确是所有竞赛图共同保证的最大阶数。
所有证明均由普通 Lean 内核检查，最终定理仅依赖 `propext`、`Classical.choice`、`Quot.sound`。
没有占位证明、自定义公理或依赖本地代码执行结果的可信判定步骤。

## 构建与检查

要求 Python 3.10 或更新版本，以及能够运行固定工具链的 Lean / Lake。
`lean-toolchain` 固定 Lean **4.33.0**；`lake-manifest.json` 固定所有依赖，
mathlib 提交为 `db584cd6d46c92f209a44c0f1c829460d327499d`。

在项目根目录运行：

```text
lake exe cache get Mathlib.Tactic Mathlib.Logic.Equiv.Fintype Mathlib.Data.Fintype.Sum Mathlib.Data.Fin.VecNotation Mathlib.Data.Finset.Lattice.Fold
python scripts/verify.py
```

检查脚本依次完成工程构建、六个关键定理的公理审计，以及每个证明模块的 `leanchecker` 声明重放。
完整报告输出到 `.research-cache/verification.json`。`leanchecker` 使用同一个 Lean 内核，
这项检查不等于第三方数学评审，也不等于奖项主办方的官方核验。

普通复核只需上述命令，**不需要 SAT 求解器或重新搜索**。两个体积较大的 `.lean` 文件是需要审查的证明源文件，
已经纳入版本控制；编译产物、依赖、下载文件和运行缓存均被忽略。

如需重建计算证书，可使用 Lean 发行版附带的 CaDiCaL：

```text
python scripts/generate_certificates.py --lean /完整路径/lean
```

Windows 对应路径以 `lean.exe` 结尾。生成器将 SAT 的 RUP 推理转换成普通命题逻辑证明；
生成器和求解器不在逻辑信任基础中，即使它们有错误，输出也必须通过 Lean 检查。
不同求解器版本可能生成不同但同样可核验的证明；复核固定版本时应使用仓库内的源文件。

## 证明结构

1. 在十五点竞赛图中，固定顶点至少有七个出邻居或七个入邻居；后一种情况把所有边反向。
2. 若选出的七个出邻居含四点传递子图，加入源点就得到五点传递子图。
3. 否则，七点竞赛图分类证书证明它必须同构于七点佩利竞赛图。
4. 将源点和这七个邻居重新编号，并把此编号扩展为十五个顶点的置换。
5. 第二个证书证明：固定这八个顶点之间的方向后，不存在缺少五点传递子图的十五点竞赛图。
6. 因而所有十五点竞赛图均含五点传递子图，代入原猜想即可反证。

相关源码：

| 文件 | 内容 |
| --- | --- |
| `Basic.lean`、`Graph.lean` | 布尔边关系、竞赛图、传递子图和有向三角形 |
| `Obstruction.lean` | 从不存在传递子图推出 SAT 使用的三角形条件 |
| `Tables.lean`、`Classification.lean` | 240 个佩利编号及七点分类与真实图之间的对应 |
| `Extension.lean`、`Main.lean` | 邻域选点、置换扩展及十五点结论 |
| `Certificates/` | 两个逐步可核验的命题逻辑证书 |
| `Erdos1216.lean` | 极值函数的定义、最大性和原猜想的完整否定 |

## 作者、来源与申请范围

形式化项目由 GitHub 账号 **hit1190100321** 提交，使用 Codex 辅助研究、编程和验证。
这是一项人类与 AI 协作完成的形式化，不主张纯人工编写，也不主张新发现了数学结论。
自然人收款身份尚未在本项目公开确认，奖项记录可使用 `RECIPIENT-JSP001021-A` 占位符。

- 原题：[Erdős Problems #1216](https://www.erdosproblems.com/1216)。
- 原始问题：P. Erdős 与 L. Moser，*On the representation of directed graphs as unions of orderings*，1964，125–132 页，问题见 127 页。
- 原始否定结论：K. B. Reid 与 E. T. Parker，*Disproof of a conjecture of Erdős and Moser on tournaments*，1970，225–238 页；[书目记录](https://www.erdosproblems.com/bibs/RePa70)。
- 对应目录：[JSP-001021](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-1001-1022.md#JSP-001021)。
- SAT 证书转换的实现思路也参考了 [JSP-000746 的公开提交讨论](https://github.com/TheJustinSunPrize/awards/issues/18)；本项目另行实现生成器，没有复制该附件中无许可证的源文件。
- Lean 与 mathlib 分别由其上游项目开发，本仓库不复制其实现；依赖许可证以各自上游为准。

本次申请限于完整否定结论的形式化贡献，**没有既定奖金金额，也没有已获奖或保证付款的结论**。
是否符合奖项标准及最终金额，由主办方依据公开证据评审。
提交时保留数学原作者归属，不主张数学解题者的奖金份额。

## 提交前发现的先前形式化

2026 年 9 月 17 日，在本项目首次公开提交前，复查官方 [PR #699](https://github.com/TheJustinSunPrize/awards/pull/699)
发现了 `plby/lean-proofs` 已公开的更强结果。我们随后检查了其
[固定版本源码](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1216.lean)：
文件包含十四点结论、`f_fourteen_eq_five` 和 `not_erdos_1216`，数学作者列为 Reid、Parker，
形式化作者列为 Codex / GPT-5.6 Sol。本项目未重放其全部依赖，不将源码阅读表述为对它的独立核验。

该源码在本项目公开前已经可访问。**本项目不主张首次形式化、优先权或获奖权利**，
提交目的是提供另一份完整的 Lean 形式化供审查，并明确披露先前成果。
本项目的证明源码和生成器在发现这一先前工作之前已经完成，没有从该先前证明复制实现。
