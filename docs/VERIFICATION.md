# 验证记录

本记录对应 2026-10-04 完成的 Part B 与 Part C 版本。

## 验证范围

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

## 代码规模

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
