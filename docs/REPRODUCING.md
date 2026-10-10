# 复现与本地打包

## 固定环境

| 项目 | 版本 |
| --- | --- |
| Lean | `leanprover/lean4:v4.19.0` |
| mathlib | `c44e0c8ee63ca166450922a373c7409c5d26b00b` |
| 其他依赖 | [`lake-manifest.json`](../formalization/lake-manifest.json) 中的固定提交 |

先按 [Lean 官方社区安装说明](https://leanprover-community.github.io/get_started.html) 安装 elan，并确保 Git 可用。
进入 `formalization/` 后，elan 会读取该目录的 `lean-toolchain`。
初次安装工具链和下载依赖缓存需要联网。
复现当前检查点时保留现有锁文件，不运行 `lake update` 升级依赖。

## 构建与审计

在仓库根目录开始：

```sh
cd formalization
lake exe cache get
lake build
lake env lean Audit.lean
```

`lake exe cache get` 下载固定版本 mathlib 的预编译缓存。
`lake build` 检查项目源码；`lake env lean Audit.lean` 随后审计项目定理和列出的关键构造定义的传递依赖。
必须在构建成功后运行审计，才能审计本次源码对应的结果。

当前版本的成功输出包括：

```text
Build completed successfully.
Axiom audit passed for 6194 theorem/definition roots. Only propext, Classical.choice, and Quot.sound are allowed.
```

入口数量会随新增声明发生变化。成功条件是命令退出码为 0，且没有出现白名单以外的公理。
`sorryAx` 或其他额外公理会使审计失败。

## Windows 与中文路径

在 PowerShell 中执行：

```powershell
cd formalization
.\Build.ps1 -Audit
```

该脚本在需要时创建 ASCII 临时目录联接，源码仍保留在原目录。
如果本机存在 `.tools/lean-4.19.0-windows/`，脚本使用其中的便携工具链；否则使用 PATH 中的 `lake.exe`。
便携工具链和已有缓存是本地辅助文件，不包含在仓库或上传压缩包中。
新机器需要先安装 elan；建议首次下载依赖时使用不含中文的克隆路径。

构建依赖之后，可以单独检查文件：

```powershell
.\Build.ps1 -Check CausalLowerbound\PartC\Minimax.lean
```

单文件检查不会更新库中对应的 `.olean`，不能替代最终的整库构建与审计。

## GitHub Actions

[`lean.yml`](../.github/workflows/lean.yml) 在源码或工作流改变时执行，也可手动触发。
它使用 [leanprover/lean-action](https://github.com/leanprover/lean-action) 安装固定工具链、获取 mathlib 缓存并构建 `formalization/`，随后执行本项目的 `Audit.lean`。
已配置远端检查；当前验证记录来自本地运行，不能据此声称 GitHub 上已经运行成功。

## 论文文件

根目录保留提供的 [PDF](../LowerBound_Complete_Revised.pdf) 与 [TeX](../LowerBound_Complete_Revised.tex)，未在此次整理中改写。
TeX 可选引用 `Proof_Flowcharts.pdf` 或旧版 PDF 的前三页；当前目录没有这两个附加文件。
源码已设置缺省分支，缺少它们时跳过前置流程图。因此重新编译的 PDF 不保证与现存 PDF 的前置页面一致。
论文编译独立于 Lean 构建和公理审计。

## 生成上传包

在仓库根目录运行 PowerShell 7：

```powershell
pwsh -NoProfile -File scripts/Export-Repository.ps1
```

输出位于 `dist/causal-lowerbound.zip`，压缩包内顶层目录为 `causal-lowerbound/`。
脚本按明确的文件清单收集论文、Lean 源码、锁文件、文档、脚本和工作流，排除本机编译器、依赖缓存、临时文件和调试日志。
已有压缩包会被当前版本替换；原始论文、源码和本地构建缓存保持原位。
以后增加新的顶层发布文件时，同时更新脚本中的文件清单。
