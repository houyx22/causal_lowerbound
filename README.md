# Causal Lower Bound — Lean 4 Formalization

Lean 4 formalization of upper and lower bounds for pointwise CATE estimation.

本项目形式化条件平均处理效应（CATE）的点态估计速率，包含均匀协变量主下界、
rough-design 模型的 Part A/B/C 下界，以及两尺度估计量的统一上界。

**截至 2026-10-11，上述最终定理均已完成。** 均匀协变量下界和由其直接推出的 Part A
保持精确指数，对所有 $n\ge1$ 成立；Part B/C 为任意正 $\varepsilon$ 的结论。
上界覆盖实值响应、闭立方体边界及低／高光滑度两种速率。
下界均采用下文列明的严格低光滑度条件和模型参数范围。

| 已验证结果 | 模型与范围 | 结论 | Lean 入口 |
| --- | --- | --- | --- |
| 均匀协变量主下界 | 固定均匀设计；任意正光滑度满足严格低光滑度条件 | 精确指数，无 $\varepsilon$ 损失 | [`paper_uniform_minimax_explicit`](formalization/CausalLowerbound/UniformLowerBound/Minimax.lean) |
| Part A | rough design；$0<\alpha,\beta\le1$ | 由均匀主下界直接推出，无 $\varepsilon$ 损失 | [`paper_partA_minimax`](formalization/CausalLowerbound/PartA.lean) |
| Part B | rough design；$\alpha,\beta>1$ | 任意 $\varepsilon>0$ 的下界 | [`paper_partB_minimax`](formalization/CausalLowerbound/PartB/PaperMinimax.lean) |
| Part C | rough design；一侧指数在 $(0,1]$，另一侧大于 1 | 两个分支均完成，任意 $\varepsilon>0$ | [`paper_partC_minimax`](formalization/CausalLowerbound/PartC/Minimax.lean) |
| 两尺度上界 | 可测设计密度有固定正下界和有限上界；实值响应；全部正光滑度 | 同一估计量在模型和目标点上统一的风险上界 | [`paper_upper_bound`](formalization/CausalLowerbound/UpperBound/PaperUpperBound.lean) |

本地整库构建通过，**6,395 个定理／构造入口通过传递公理审计**。
源码无 `sorry`、`admit`、`native_decide` 或自定义公理；
允许的基础公理仅为 `propext`、`Classical.choice`、`Quot.sound`。
详见[验证记录](docs/VERIFICATION.md)与[完整模块说明](formalization/README.md)。

## 问题的数学表述

### 下界的观测模型与估计目标

观测独立同分布的样本 $Z_1,\ldots,Z_n$，其中 $Z=(X,A,Y)$ 满足

$$
\begin{aligned}
X&\in[0,1]^d,\\
A\mid X=x&\sim\operatorname{Bernoulli}(\pi(x)),\\
Y\mid(X=x,A=a)&\sim\operatorname{Bernoulli}(\mu_0(x)+a\tau(x)).
\end{aligned}
$$

这里 $d\ge1$，$A,Y\in\{0,1\}$。固定一个内部点 $x_0\in(0,1)^d$，
目标是估计该点的条件均值差

$$
\tau(x_0)=\mathbb E[Y\mid X=x_0,A=1]-\mathbb E[Y\mid X=x_0,A=0].
$$

模型中的函数及其光滑度分别为：

| 符号 | 含义 | 约束 |
| --- | --- | --- |
| $f(x)$ | 协变量 $X$ 的设计密度 | 可测、积分为 1，并有固定正下界和有限上界 |
| $\pi(x)$ | 倾向函数，即接受处理的条件概率 | $\alpha$ 阶 Hölder 光滑度，半径 $L_\pi$ |
| $\mu_0(x)$ | 未接受处理时的结局条件均值 | $\beta$ 阶 Hölder 光滑度，半径 $L_0$ |
| $\tau(x)$ | 处理组与对照组的条件均值差 | $\gamma$ 阶 Hölder 光滑度，半径 $L_\tau$ |

### 下界使用的模型类

固定 $\alpha,\beta,\gamma>0$、$L_\pi,L_0>1/2$、$L_\tau>0$，以及

$$
0<\underline f<1<\overline f<\infty,\qquad 0<\kappa<1/4.
$$

论文中的模型类 $\mathcal P$ 包含所有满足上述观测模型及以下条件的分布：

$$
\begin{aligned}
&\underline f\le f(x)\le\overline f,\qquad \int_{[0,1]^d}f(x)\,dx=1,\\
&\pi\in\mathcal H^\alpha(L_\pi),\qquad
  \mu_0\in\mathcal H^\beta(L_0),\qquad
  \tau\in\mathcal H^\gamma(L_\tau),\\
&\kappa\le\pi(x)\le1-\kappa,\qquad
  \kappa\le\mu_0(x)\le1-\kappa,\\
&\kappa\le\mu_0(x)+\tau(x)\le1-\kappa.
\end{aligned}
$$

这些条件在立方体上成立；论文的 Hölder 类使用固定邻域上的延拓约定。
设计密度 $f$ 也是模型类中可以变化的对象，**不要求具有任何光滑度**，
这就是标题中的 **rough design（粗糙设计）**。

Part A/B/C 则按两个函数 $\pi,\mu_0$ 的光滑度划分：指数处于 $(0,1]$ 的一侧称为粗糙一侧。
例如，当 $0<\alpha\le1$ 时，倾向函数满足
$|\pi(x)-\pi(y)|\le L_\pi\|x-y\|^\alpha$；$\alpha=1$ 对应 Lipschitz 条件。
$\gamma$ 始终表示目标函数 $\tau$ 的光滑度，不参与 A/B/C 的分支划分。

### 点态绝对误差 minimax 风险

对所有可测估计量 $\widehat\tau_n=\widehat\tau_n(Z_1,\ldots,Z_n)$ 定义

$$
R_n^*(x_0;\mathcal P)
=\inf_{\widehat\tau_n\ \mathrm{measurable}}
  \sup_{P\in\mathcal P}
  \mathbb E_{P^{\otimes n}}
  \left[\left|\widehat\tau_n(Z_1,\ldots,Z_n)-\tau_P(x_0)\right|\right].
$$

下界描述的是：任意估计方法在这个模型类上的最坏情形误差，都受到下述速率的限制。
这里的损失是固定点 $x_0$ 处的绝对误差；期望取自该模型真实的 $n$ 个独立样本。

## 最终下界与 Part A 推论

以下所有下界均假设 $\alpha,\beta,\gamma>0$，并处于严格低光滑度区间：

$$
(\alpha+\beta)\left(2+\frac d\gamma\right)<d.
$$

### 均匀协变量主下界：精确指数

[均匀协变量论文](UniformCovariate_LowerBound.pdf) 固定
$X\sim\operatorname{Unif}([0,1]^d)$。令

$$
\rho_U=\frac{1}{1+d/(2\gamma)+d/[2(\alpha+\beta)]}.
$$

最终定理证明

$$
\exists C>0,\quad\forall n\ge1,\qquad
R_n^*(x_0;\mathcal P_{\mathrm{uniform}})\ge Cn^{-\rho_U}.
$$

常数 $C$ 可依赖固定模型参数及 $x_0$，但不依赖 $n$。
此定理允许 $L_\pi,L_0>1/2$、$L_\tau>0$、$0<\kappa<1/2$；
取三个半径均为 1 即得到论文中的单位 Hölder 球结论。

证明采用固定大小的依赖图分量截断、大分量坏事件概率界和实际混合实验的 Hellinger 界。
模型合法性、符号矩消去、尺度选择和风险归约均在 Lean 内完成。
形式化范围是最终主下界；证明对中间构造作了调整，具体对应见[技术说明](formalization/README.md)。

### Part A：均匀设计子模型直接给出下界

原 rough-design 论文的指数为

$$
s_1=\frac{\min(\alpha,1)+\min(\beta,1)}2,\qquad
\rho=\frac{\alpha+\beta+2s_1}{d+4s_1+2ds_1/\gamma}.
$$

当 $0<\alpha,\beta\le1$ 时，$s_1=(\alpha+\beta)/2$，从而 $\rho=\rho_U$。
固定相同的 Hölder 半径和重叠参数，均匀密度 $f\equiv1$ 满足原模型的密度界，所以

$$
\mathcal P_{\mathrm{uniform}}\subseteq\mathcal P,
\qquad
R_n^*(x_0;\mathcal P)\ge
R_n^*(x_0;\mathcal P_{\mathrm{uniform}})\ge Cn^{-\rho}.
$$

[`PartA.lean`](formalization/CausalLowerbound/PartA.lean) 已形式化指数恒等式和模型包含的风险比较。
因此 Part A 对全部 $n\ge1$ 成立，保持精确指数，无 $\varepsilon$ 损失。

### Part B 与 Part C：任意正 ε

在各自的正则性分支和上述低光滑度条件下，最终结论为

$$
\begin{gathered}
\forall\varepsilon>0,\quad
\exists C_\varepsilon>0,\quad
\exists N_\varepsilon\in\mathbb N,\\
\forall n\ge N_\varepsilon,\qquad
R_n^*(x_0;\mathcal P)\ge C_\varepsilon n^{-(\rho+\varepsilon)}.
\end{gathered}
$$

$C_\varepsilon,N_\varepsilon$ 可依赖固定模型参数、$x_0$ 和 $\varepsilon$，但不依赖 $n$。
Part B 中 $s_1=1$；Part C 中 $s_1=(1+\min(\alpha,\beta))/2$，
两个分支均包含粗糙指数等于 1 的边界。

## 两尺度估计量的统一上界

[`paper_upper_bound`](formalization/CausalLowerbound/UpperBound/PaperUpperBound.lean)
在有固定正下界和有限上界的可测设计密度下，为原始 $n$ 个 iid 样本构造可测估计量。
响应允许为实数，假设条件二阶矩有界、满足重叠条件，
并在预先固定且包含单位立方体的开邻域上满足 Hölder 条件。

对全部充分大的 $n$，同一估计量的平均绝对误差在全部合法模型及闭立方体目标点上统一满足

$$
\mathbb E_P\bigl[|\widehat\tau_n(x_0)-\tau_P(x_0)|\bigr]
\le
\begin{cases}
Cn^{-\rho}, & (\alpha+\beta)(2+d/\gamma)<d,\\
Cn^{-\gamma/(2\gamma+d)}, & (\alpha+\beta)(2+d/\gamma)\ge d.
\end{cases}
$$

这里 $\rho$ 与上文的 rough-design 指数相同，估计量、常数和样本量阈值均先于模型和目标点选定。
上界的实值响应模型与下界的二元响应子模型分别定义；完整参数和量词见对应 Lean 声明。

## 下界模型在 Lean 中的表示

Lean 直接验证的模型类由 `StatisticalModel` 定义。它把函数、设计密度和所有合法性证明
放在同一个结构中；最终风险对该结构的全部实例取上确界。

| 数学对象 | Lean 表示与定义位置 |
| --- | --- |
| 维数与协变量 | `d` 是有限非空的坐标索引类型，数学维数为 `Fintype.card d`，协变量类型为 `d → ℝ` |
| 光滑度指数 | [`Regularity`](formalization/CausalLowerbound/PartB/NuisanceLegality.lean)：整数阶 `order` 与 `fraction ∈ [0,1]`，数值为 `.exponent = order + fraction` |
| Hölder 界 | [`HolderControl`](formalization/CausalLowerbound/HolderScaling.lean)：控制各阶导数的范数及最高阶导数的 Hölder 差分 |
| 三个参数函数 | [`NuisanceFields`](formalization/CausalLowerbound/PartB/NuisanceLegality.lean)：`propensity`、`baseline`、`effect` 分别表示 $\pi,\mu_0,\tau$ |
| 设计密度与完整合法性 | [`DesignLegal`、`ModelLegal`](formalization/CausalLowerbound/PartB/ConcreteModels.lean)：可测性、归一化、密度界、函数光滑度界及概率范围 |
| 统计模型类 | [`StatisticalModel`](formalization/CausalLowerbound/PartB/StatisticalModel.lean)：再加入各函数相应整数阶的 `ContDiff` 证明及设计密度的非负性 |
| 样本的实际概率律 | [`StatisticalModel.sampleMeasure`](formalization/CausalLowerbound/PartB/StatisticalModel.lean)：设计的乘积测度与条件独立的二元观测律 |
| 绝对误差风险及 minimax 风险 | [`StatisticalModel.risk`、`minimaxRisk`](formalization/CausalLowerbound/PartB/StatisticalModel.lean)：先积分，再对模型取上确界、对可测估计量取下确界 |

具体而言，`Regularity` 表示指数 $m+\theta$，其中 $m\in\mathbb N$、$0\le\theta\le1$。
`HolderControl m θ L g` 要求

$$
\begin{aligned}
\forall j\le m,\ \forall x,&\quad \|D^j g(x)\|\le L,\\
\forall x,y,&\quad \|D^m g(x)-D^m g(y)\|\le L\|x-y\|^\theta.
\end{aligned}
$$

`StatisticalModel.regular` 另外要求 $g$ 为 $m$ 阶连续可微，保证这些导数是经典导数。
$m=0$ 时是对函数本身的控制；$\theta=0$ 时最后一项是最高阶导数的有界振荡条件。

风险的核心定义如下，其中 `hκ` 是 `0 ≤ κ` 的证明，`est.val` 是可测估计量本身：

```lean
def minimaxRisk (α β γ : Regularity) (Lπ L₀ Lτ κ lower upper : ℝ) (hκ : 0 ≤ κ)
    (x₀ : d → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨅ est : {f : ((Fin n → d → ℝ) × (Fin n → Bool × Bool)) → ℝ // Measurable f},
    ⨆ M : StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper, M.risk hκ x₀ n est.val
```

样本类型将 $X^n$ 与 $(A,Y)^n$ 分别存放，`Bool` 编码二元变量。
`cubeMeasure` 是限制在单位立方体上的 Lebesgue 测度；乘上密度后构造真实样本分布。
风险使用扩展非负实数 `ℝ≥0∞` 和非负积分 `lintegral`，所以也允许估计量的风险为无穷大。
Part B/C 结论中的 `∀ᶠ n : ℕ in atTop` 表示“对所有充分大的样本量 $n$”，
`ENNReal.ofReal` 将非负实数下界嵌入同一风险值域。

### Lean 模型与论文模型的关系

代码在整个 $\mathbb R^d$ 上施加函数正则性、概率范围及设计密度上下界，
设计的归一化与样本分布仍只使用 $[0,1]^d$。
将这些模型限制到立方体及其邻域，就得到论文模型中的一个全空间正则子类。
记该子类为 $\mathcal P_{\mathrm{Lean}}$，在对应的 Hölder 范数约定下，
模型类包含关系给出

$$
\mathcal P_{\mathrm{Lean}}\subseteq\mathcal P,\qquad
R_n^*(x_0;\mathcal P)\ge R_n^*(x_0;\mathcal P_{\mathrm{Lean}}).
$$

因此，Lean 直接证明的 `minimaxRisk` 下界蕴含论文模型上的同一速率下界。
最终下界定理允许任意 `x₀ : d → ℝ`；rough-design 下界对密度界只要求 `lower < 1 < upper`。
取论文中的内部点和正密度下界即可应用。完整的定义与定理声明以上述链接中的源码为准。

### 最终入口与证明链

均匀协变量主下界的入口是 `CausalLowerbound.UniformLowerBound.paper_uniform_minimax_explicit`。
`CausalLowerbound.PartA.paper_partA_minimax` 调用该定理，通过指数恒等式和模型包含关系得到原 Part A。

Part B 的入口是 `CausalLowerbound.PartB.ShellGeometry.paper_partB_minimax`。
Part C 的统一入口是 `CausalLowerbound.PartC.paper_partC_minimax`，它调用
[`paper_partC_roughPropensity_minimax`](formalization/CausalLowerbound/PartC/PropensityMinimax.lean)
和 [`paper_partC_roughOutcome_minimax`](formalization/CausalLowerbound/PartC/OutcomeMinimax.lean)。

Part B/C 最终定理只接收正则性指数、分支条件、上述参数区间和 $\varepsilon>0$。
证明内部完成以下步骤：

1. 选择尺度和振幅，构造满足全部模型约束的两组参数族，并证明在 $x_0$ 处的目标分离。
2. 构造正载体与先验，证明所需矩匹配，并识别比较实验为合法统计模型上的真实先验混合。
3. 证明局部 Hellinger 比较及全局总变差（TV）控制，使两组混合实验难以区分。
4. 通过二点检验下界，完成先验平均到模型上确界、再到所有可测估计量下确界的推导。

正载体存在、模型合法性、矩匹配和信息界均已在内部构造或证明。
Part C 对部分 taper（截断）和 ghost（辅助积分点）估计作了调整，额外损失由任意正 $\varepsilon$ 吸收，
最终指数 $\rho$ 及上述下界保持不变。各模块与论文证明的对应见[详细说明](formalization/README.md)。

## 从哪里开始

- [论文 PDF](LowerBound_Complete_Revised.pdf) / [TeX 源码](LowerBound_Complete_Revised.tex)
- [均匀协变量下界附件](UniformCovariate_LowerBound.pdf) / [主定理](formalization/CausalLowerbound/UniformLowerBound/Minimax.lean) / [Part A 推论](formalization/CausalLowerbound/PartA.lean)
- [安装、构建与公理审计](docs/REPRODUCING.md)
- [验证记录与代码规模](docs/VERIFICATION.md)
- [完整模块说明及论文对应](formalization/README.md)
- [两尺度统一上界](formalization/CausalLowerbound/UpperBound/PaperUpperBound.lean)
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

最近一次本地整库构建及公理审计的命令、结果和入口数量见[验证记录](docs/VERIFICATION.md)。
允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`。
GitHub Actions 工作流已配置为构建同一工程并执行同一份 `Audit.lean`；远端运行结果以 GitHub Actions 页面为准。

## 目录

```text
.
├── README.md
├── LowerBound_Complete_Revised.tex
├── LowerBound_Complete_Revised.pdf
├── UniformCovariate_LowerBound.pdf
├── formalization/
│   ├── CausalLowerbound/          # 公共模块、PartA/B/C、UniformLowerBound、UpperBound
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
历史调试日志归档在本地 `tmp/build-logs/`，各阶段整库验证日志的位置见[验证记录](docs/VERIFICATION.md)。
本地打包命令：

```powershell
pwsh -NoProfile -File scripts/Export-Repository.ps1
```

输出为 `dist/causal-lowerbound.zip`，只包含发布所需的源码、论文、文档和配置。

## 许可

尚未指定开源许可证。
