# 验证记录

本记录包含 2026-10-04 完成的 Part B 与 Part C 版本，以及 2026-10-11 完成的两尺度上界主速率定理和此前检查点。

## 2026-10-11：统一上界主速率定理完成

最终入口是 [`paper_upper_bound`](../formalization/CausalLowerbound/UpperBound/PaperUpperBound.lean)。
它给出原始 `n` 个 iid 样本上的同一可测估计量，并在全部合法实值响应模型及闭立方体目标点上，
统一证明低光滑度的 `C n^(-ρ_TS)` 与高光滑度／临界点的 `C n^(-γ/(2γ+d))` 平均绝对误差界。
估计量、常数 `C>0` 和样本量阈值 `N` 均先于模型和目标点选定。
最终定理没有保留带宽合法性、总体偏差、矩阵下界、经验矩或估计量可测性作为输入。

上界目录现有 76 个模块、515 条显式定理和 130 个 `def`／`abbrev` 声明。
本阶段完成了 Taylor 向量和余项、实际总体残差、矩阵分解与扰动、
保留完整元组依赖的加权 Gram 下界、向量／算子二阶矩、截断逆可测性、
`floor(n/M)` 角色分组及其原始样本乘积测度、有限样本风险归约、
多项式带宽合法性和两种最终速率。
`PaperSmoothness.lean` 严格实现 `q=ceil(a)-1`，包括整数光滑度的 Lipschitz 约定。

模型假设采用 `RealOutcomeModel` 与 `PaperRegularity`：可测设计密度的上下界，
二元治疗、实值响应、CATE 的条件一阶矩恒等式，以及固定开邻域上的 Hölder 扩张。
论文的按治疗组条件二阶矩假设蕴含所用的 `E[Y²|X]≤M₂`；证明无需四阶矩。
模板采用固定张量多项式空间，节点数与论文不同，但全部投影和常数控制已证明其保持相同速率。
没有声称匹配下界，也没有声称逐字复刻论文的总次数节点构造。
有限样本主界的显式数值条件可在 `FiniteSampleRisk.lean` 查看；
`BandwidthAdmissibility.lean` 与 `RateChoice.lean` 在最终主定理中消去了这些条件。

锁定工具链下依次执行：

```powershell
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' build
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' env lean Audit.lean
```

两个命令退出码均为 0：

```text
Build completed successfully.
Axiom audit passed for 6194 theorem/definition roots. Only propext, Classical.choice, and Quot.sound are allowed.
```

本地原始日志为 `formalization/.tools/upper-complete-full-build.log` 和
`formalization/.tools/upper-complete-full-audit.log`。
新增 41 个关键定义已加入审计；上界目录全部显式 `def`／`abbrev` 均在列表中。
源码扫描未发现 `sorry`、`admit`、`native_decide` 或自定义公理。
`git diff --check` 通过（Git 另有行尾规范提示）。

以下记录保留各历史检查点的当时状态，不代表当前仍有相应缺口。

## 2026-10-11：实际经验统计量与两项方差界

该历史检查点包含 45 个上界模块、332 条显式定理和 89 个 `def`／`abbrev` 声明，
均已通过统一入口接入整库。本次新增 10 个模块，完成了：

- 任意非空共享节点集合的补全体积界，包括锚点与近邻点是否共享的四种情形。
- 在真实观测分布下，利用协变量边际和可测密度上界得到补全概率界，继而控制条件投影的二阶矩。
- 对所有非空重叠模式求和；当各组样本数倒数不超过 `η`、且 `η` 不超过粗尺度单元体积的固定倍数时，固定张量角色数仅影响方差常数。
- 定义真实向量核和非对称矩阵核，证明可测性及 L²；响应仍可无界，仅用条件二阶矩。
- 利用条件元组分布证明实际核的二阶矩为接受体积阶，保留小概率接受事件的因子。
- 构造可测的 `empiricalStencilResponse`、`empiricalStencilMatrix`，得到实际统计量的坐标方差界。

`EmpiricalStatistics.lean` 中的 `empiricalStencilResponse_variance_le` 与
`empiricalStencilMatrix_variance_le` 给出
`C q₀² [η/(h/4)^d + η²/((h/4)^d ℓ^d)]` 的界。
这里 `q₀ = stencilMass` 是已证明等于接受集合 Lebesgue 体积的量；
常数只依赖固定角色数、密度和二阶矩界、粗尺度比较常数。
这一步尚未构造原始 `n` 个 iid 样本中的具体分组，不能直接视为最终 `n` 速率定理。

使用锁定的便携工具链依次执行：

```powershell
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' build
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' env lean Audit.lean
```

退出码均为 0：

```text
Build completed successfully.
Axiom audit passed for 5900 theorem/definition roots. Only propext, Classical.choice, and Quot.sound are allowed.
```

日志保留于本地 `formalization/.tools/upper-variance-full-build.log` 和
`formalization/.tools/upper-variance-full-audit.log`。16 个新增关键定义已加入公理审计列表；
上界源码扫描没有发现 `sorry`、`admit`、`native_decide` 或自定义公理。

**统一上界主定理仍未完成。** 还需 Taylor 系数向量、总体偏差与总体矩阵扰动、
坐标方差到向量／算子二阶矩的转换、原始样本分组、截断逆估计量可测性，
以及完整模型上的统一风险和最终两种光滑度区间的速率组装。

## 2026-10-11：两尺度几何、实值响应模型与条件元组分布

该检查点的 `CausalLowerbound/UpperBound/` 包含 35 个模块、260 条显式定理和 73 个 `def`／`abbrev` 声明，
全部通过 `CausalLowerbound/UpperBound.lean` 接入整库构建。本次检查覆盖：

- 正张量网格上的统一插值可逆性、归一化权重和多维 Taylor 多项式消去。
- 闭立方体边界上的向内反射，以及仅使用固定开邻域正则性的 Hölder 对比界。
- 实际观测权重与接受事件的可测性、精确接受体积、可测设计密度给出的概率上下界。
- 固定多项式 Gram 矩阵的正下界，以及允许权重依赖整组观测的积分下界。
- 二元治疗、实值响应的 Markov 条件模型；有限乘积条件核与原始 iid 样本分布的测度恒等式。
- 完整条件 score 恒等式及二阶矩界，只要求条件响应二阶矩，不要求有界响应或四阶矩。
- 以补全概率控制部分核二阶矩的 Cauchy–Schwarz 归约。

在 `formalization/` 中使用原有锁定工具链运行：

```powershell
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' build
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' env lean Audit.lean
```

两个命令的退出码均为 0，输出包括：

```text
Build completed successfully.
Axiom audit passed for 5781 theorem/definition roots. Only propext, Classical.choice, and Quot.sound are allowed.
```

原始日志保留于本地 `formalization/.tools/upper-geometry-full-build.log` 和
`formalization/.tools/upper-geometry-full-audit.log`。新增源码扫描未发现 `sorry`、`admit`、
`native_decide` 或自定义 `axiom`；关键新增构造已经加入审计列表。

**完整上界主定理仍未完成。** 还需要实际经验核与 Taylor 系数向量、总体偏差和矩阵扰动、
每类共享观测模式的具体补全概率界、估计量可测性，以及统一风险和最终速率定理。
当前证明采用 `(p+1)^d` 个辅助张量节点，另加锚点和近邻点；
最终重叠求和仍须验证这一固定节点数保持论文的速率。
当前风险归约中的总体矩阵下界与估计量可测性仍是显式前提，不能将其视为主定理已经证明。
完整工作清单见 [`UpperBound.lean`](../formalization/CausalLowerbound/UpperBound.lean)。

## 2026-10-10：两尺度上界的首批证明

新增 `CausalLowerbound/UpperBound/` 下 11 个模块，包含 97 条显式定理和 25 个定义，
并通过 `CausalLowerbound/UpperBound.lean` 接入整库构建。
已验证精确的分组元组方差展开、Hölder–Taylor 桥接、两尺度消去、插值权重构造、
截断逆和裁剪的均方风险归约，以及低／高光滑度的指数关系。

在 `formalization/` 中使用锁定的便携工具链运行：

```powershell
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' build
& '.\.tools\lean-4.19.0-windows\bin\lake.exe' env lean Audit.lean
```

两个命令的退出码均为 0，最终输出为：

```text
Build completed successfully.
Axiom audit passed for 5480 theorem/definition roots. Only propext, Classical.choice, and Quot.sound are allowed.
```

原始日志保留在本地 `.tools/upper-full-build.log` 与 `.tools/upper-full-audit.log`。
新增源码没有 `sorry`、`admit` 或自定义公理；关键构造定义已加入审计列表。

**这不表示论文上界主定理已经完成。** 节点盒上的统一插值可逆性、边界几何、
Gram 正下界、实际部分核的体积和二阶矩界、估计量可测性及完整模型上的最终组装仍待证明。
当前风险归约中的矩阵下界和可测性是显式前提，后续必须由具体构造推出。
完整工作清单见 [`UpperBound.lean`](../formalization/CausalLowerbound/UpperBound.lean)。

## 2026-10-04：Part B 与 Part C 的验证范围

| 范围 | 结果 |
| --- | --- |
| Part B 最终 minimax 定理 | 已通过 Lean 编译 |
| Part C 粗糙倾向分支 | 已通过 Lean 编译 |
| Part C 粗糙结局分支 | 已通过 Lean 编译 |
| Part C 统一入口 | 已通过 Lean 编译 |
| 整库构建 | 通过，退出码 0 |
| 传递公理依赖审计 | 通过，5,334 个定理／构造入口 |
| Part A | 尚未形式化 |
| GitHub Actions | 已配置；尚无远端运行结果 |

在 `formalization/` 中执行的命令为：

```powershell
.\Build.ps1 -Audit
```

本地保存的构建日志末尾为：

```text
✔ [3132/3136] Built CausalLowerbound.PartC.OutcomePaperMinimax
✔ [3133/3136] Built CausalLowerbound.PartC.OutcomeMinimax
✔ [3134/3136] Built CausalLowerbound.PartC.Minimax
✔ [3135/3136] Built CausalLowerbound
Build completed successfully.
Axiom audit passed for 5334 theorem/definition roots. Only propext, Classical.choice, and Quot.sound are allowed.
```

完整原始日志保留于本地 `formalization/verification-partC.log`，不打包进仓库。
此记录是已有运行结果的摘要，复核方法见[复现说明](REPRODUCING.md)。

## 公理与数学前提

[`Audit.lean`](../formalization/Audit.lean) 允许且仅允许：

```text
propext
Classical.choice
Quot.sound
```

审计使用 Lean 的 `CollectAxioms.collect`，检查项目命名空间中的全部定理及列表中的关键构造定义的传递公理依赖。
检查入口数包含 Lean 自动生成的辅助定理，并非显式 `theorem` 声明数。
源代码扫描未发现 `sorry`、`admit`、`native_decide` 或自定义 `axiom` 声明。

“没有未证明的技术前提”不等于“没有数学假设”：最终定理仍包含论文要求的正则性、低光滑度条件、固定半径和概率／密度界。
载体存在、模型构造、矩匹配和 TV 界则由内部证明给出。
关于模型范围及与 TeX 中间证明的差异，见[详细技术文档](../formalization/README.md)。

## Part B 与 Part C 完成版本的代码规模（2026-10-04）

以下计数不包括 `.lake/` 中的依赖及 `.tools/` 中的本机工具：

| 源码目录 | Lean 模块数 |
| --- | ---: |
| `CausalLowerbound/PartB/` | 154 |
| `CausalLowerbound/PartC/` | 399 |
| `CausalLowerbound/` 的公共模块 | 58 |
| 合计 | 611 |

另有统一导入文件 `CausalLowerbound.lean` 和审计文件 `Audit.lean`。
Part C 目录共 **37,090 行**、**33,334 个非空行**，399 个模块全部进入统一导入入口。
详细技术文档中的“Part B 完成版本 207 个模块”包含当时的公共模块，统计口径不同于这里按目录计数的 154。
