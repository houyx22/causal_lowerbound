# Causal Lower Bound — Lean 4 Formalization

Lean 4 formalization of minimax lower bounds for pointwise CATE estimation with binary outcomes and rough design.

本项目收录论文原稿及其 Lean 4 形式化。目前 **Part B 和 Part C 已完成，Part A 尚未完成**。
完整论文覆盖三种情形，因此不能将当前状态表述为整篇主定理已经全部形式化。

## 完成范围

| 情形 | 正则性范围 | 状态 | 最终入口 |
| --- | --- | --- | --- |
| Part A | `0 < α, β ≤ 1` | 尚未形式化 | — |
| Part B | `α > 1, β > 1` | 已完成 | [`paper_partB_minimax`](formalization/CausalLowerbound/PartB/PaperMinimax.lean) |
| Part C | `0 < α ≤ 1 < β` 或 `0 < β ≤ 1 < α` | 两个分支均已完成 | [`paper_partC_minimax`](formalization/CausalLowerbound/PartC/Minimax.lean) |

已完成的最终定理给出任意 `ε > 0` 下的点态绝对误差 minimax 下界

$$
R_n^*(x_0) \ge C_\varepsilon n^{-(\rho+\varepsilon)},\qquad
\rho=\frac{\alpha+\beta+2s}{d+4s+2ds/\gamma},\qquad
s=\frac{\min(\alpha,1)+\min(\beta,1)}2.
$$

定理保留论文自身的条件，包括正则性范围、
`(α+β)(2+d/γ) < d`、Hölder 半径和概率／密度界。
正载体、模型合法性、矩匹配和信息界均在证明内部构造或证明，没有作为未解决的技术前提留在最终定理中。

形式化使用全空间正则的子模型；它与论文模型的关系，以及 Part C 中 taper 和 ghost 估计的调整，见[详细说明](formalization/README.md)。

## 从哪里开始

- [论文 PDF](LowerBound_Complete_Revised.pdf) / [TeX 源码](LowerBound_Complete_Revised.tex)
- [安装、构建与公理审计](docs/REPRODUCING.md)
- [验证记录与代码规模](docs/VERIFICATION.md)
- [完整模块说明及论文对应](formalization/README.md)
- [Part C：粗糙倾向分支](formalization/CausalLowerbound/PartC/PropensityMinimax.lean)
- [Part C：粗糙结局分支](formalization/CausalLowerbound/PartC/OutcomeMinimax.lean)

## 快速复现

安装 [Lean / elan](https://leanprover-community.github.io/get_started.html) 后，在仓库根目录执行：

```sh
cd formalization
lake exe cache get
lake build
lake env lean Audit.lean
```

Windows PowerShell 可使用已有脚本，它同时处理中文路径：

```powershell
cd formalization
.\Build.ps1 -Audit
```

固定版本为 **Lean 4.19.0** 和 mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`。
依赖版本保存在 `lean-toolchain`、`lakefile.toml` 和 `lake-manifest.json` 中。

2026-10-04 的本地整库构建及公理审计通过，检查了 **5,334 个定理／构造入口**。
允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`。
GitHub Actions 工作流已配置为构建同一工程并执行同一份 `Audit.lean`；远端运行结果以 GitHub Actions 页面为准。

## 目录

```text
.
├── README.md
├── LowerBound_Complete_Revised.tex
├── LowerBound_Complete_Revised.pdf
├── formalization/
│   ├── CausalLowerbound/          # 公共模块、PartB、PartC
│   ├── CausalLowerbound.lean      # 统一导入入口
│   ├── Audit.lean                # 传递公理依赖审计
│   ├── Build.ps1                 # Windows 构建入口
│   ├── lean-toolchain
│   ├── lakefile.toml
│   ├── lake-manifest.json
│   └── README.md                 # 详细技术文档
├── docs/                         # 复现说明、验证记录
├── scripts/Export-Repository.ps1 # 生成干净的上传压缩包
└── .github/workflows/lean.yml    # 构建及审计
```

`.lake/`、`.tools/`、`tmp/`、`dist/`、调试日志及编译产物不进入版本控制。
历史调试日志归档在本地 `tmp/build-logs/`，最近的整库审计日志保留在 `formalization/verification-partC.log`。
本地打包命令：

```powershell
pwsh -NoProfile -File scripts/Export-Repository.ps1
```

输出为 `dist/causal-lowerbound.zip`，只包含发布所需的源码、论文、文档和配置。

## 许可

尚未指定开源许可证。
