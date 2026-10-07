# Part B 与 Part C 的 Lean 形式化

[项目首页](../README.md) · [复现说明](../docs/REPRODUCING.md) · [验证记录](../docs/VERIFICATION.md)

Part B 状态：第 1、2、3 项均已完成；实际实验的全局 TV 趋零、先验混合识别和最终 minimax 下界已通过 Lean 检查（2026-10-03）。
最终入口是 `CausalLowerbound/PartB/PaperMinimax.lean` 的 `paper_partB_minimax`。
其输入仅为 Part B 的正则性指数、参数区间、固定半径和密度界；不要求另行提供 Wiener 估计、正载体、模型合法性或信息界。
Part B 完成版本的整库编译及公理审计通过，2339 个定理/构造入口仅依赖 Lean/mathlib 标准基础公理。

Part C 的两个混合光滑度情形及统一最终定理已通过整库构建和公理审计（2026-10-04）。
统一入口是 `CausalLowerbound/PartC/Minimax.lean` 的 `paper_partC_minimax`，
证明原始统计模型中任意 `ε>0` 下的 `C n^(-(ρ+ε))` minimax 下界。
其输入同样只有原始模型参数与正则性条件，不含载体存在、模型构造、矩匹配或 TV 界假设。

本项目从 `LowerBound_Complete_Revised.tex` 的 Part B 开始。Part B 完成版本包含 207 个证明模块、
1225 条显式 theorem/lemma 声明，覆盖独立符号矩、单点与多点桥接、部分块扰动的定量稳定性、
二元概率律、有限矩扰动、局部 Hellinger 不等式、条件正载体构造，以及具体 Wiener
空间、完整的正极化算子、均匀各向异性格点求和、配置图拉回和紧支集光滑函数的
Fourier 导数衰减估计，以及实际周期化、混合周期坐标、具体细壳层商、taper 和
dyadic 截断的分析。正极化已接入载体定理，不再是具体 Wiener 版本的输入假设。
**第 1 项（具体 Wiener 估计与正极化）、第 2 项（具体模型构造与合法性）和第 3 项（全局信息界与 minimax 下界）已连接为完整证明。**
入口是 `PartB/PaperWiener.lean` 的 `paper_wiener_strong`、`paper_wiener_rate`、
`paper_wiener_vanishes` 和 `paper_item_one`。它们使用实际完全图、完整多项式系数空间、
全部 `Ψ_{4Q}` 矩坐标，以及原文的坐标 Wiener 范数之和。
`J_n` 的范数界、趋零、实值性、置换对称性和正极化均已由构造推出。
小球内的支持点、正基线概率和矩右逆现已具体构造，已接入正载体定理。
插值、二次分割、实际包场及非整数阶 Hölder 缩放也已证明。
完整结局回归的合法性、物理设计密度和可数先验的 Zⁿ 倾斜均已连接到实际构造。
第二项的汇总入口是 `PartB/ConcreteModels.lean` 的 `paper_item_two` 和
`paper_item_two_polynomial`。后者给出固定正振幅及所有充分大 n 的合法模型序列。
`PartB/GlobalPriors.lean` 与 `PartB/DesignExperiments.lean` 给出实际乘积先验、
倾斜后的共同设计密度律、连续 Xⁿ 概率边际，以及精确似然抵消。

## 最终定理与模型范围

令 `D = Fintype.card d`、`A = α.exponent + β.exponent`，则
`ρ = (A + 2) / (D + 4 + 2D/γ.exponent)`。`paper_partB_minimax` 证明：

```text
α > 1，β > 1，γ > 0，D > (α+β)(2+D/γ)，ε > 0，
Lπ > 1/2，L₀ > 1/2，Lτ > 0，0 < κ < 1/4，lower < 1 < upper
  ⇒ ∃ C > 0，∀充分大 n，C n^(-(ρ+ε)) ≤ minimaxRisk(..., x₀, n)。
```

这里的 `minimaxRisk` 是实际样本分布下绝对误差积分的 minimax 风险：
对所有可测估计量取下确界，对 `StatisticalModel` 取上确界。
风险用 `ℝ≥0∞` 表示，因此包括不可积、风险为无穷大的估计量。
样本是连续设计 Xⁿ 与二元 (A,Y)ⁿ，给定固定模型后按独立同分布采样。
`physicalComparisonDensity_eq_mixture` 精确证明比较实验就是合法模型上的实际先验混合，
最终定理同时完成先验平均、模型上确界、估计量下确界之间的推导。

`StatisticalModel` 要求全空间上的 Hölder 界和相应阶数的经典连续可微性；
`Regularity` 用整数阶与 `[0,1]` 内的小数部分表示指数。
论文允许固定立方体邻域上的 Hölder 延拓，所以代码中使用的是其一个更小的、
全空间正则的子模型。该子模型上的下界蕴含论文模型上的下界，因为扩大模型类
只会增大 minimax 风险。全空间版本同时对概率范围和设计上下界施加更强要求。
设计仅要求可测、积分为 1 及上下界；没有对设计密度增加光滑性条件。
Part A 尚未完成。Part C 的粗糙倾向与粗糙结局情形均已完成，详见下文。

## Part C 的最终定理与证明链

目标是完整证明两个混合光滑度情形的真实 minimax 下界；允许改变 TeX 的中间构造和估计。
最终指数保持 `ρ = (A + 2s) / (d + 4s + 2ds/γ)`，其中 `A = α + β`、`s = (1 + min α β)/2`。
粗糙倾向情形 `0<α≤1<β` 的入口为 `PartC/PropensityMinimax.lean` 中的 `paper_partC_roughPropensity_minimax`；粗糙结局情形 `0<β≤1<α` 的入口为 `PartC/OutcomeMinimax.lean` 中的 `paper_partC_roughOutcome_minimax`。二者及统一入口 `PartC/Minimax.lean` 中的 `paper_partC_minimax` 均已通过 Lean 编译，覆盖粗糙指数等于 1 的边界。它们对任意 `ε>0` 给出原速率的 minimax 下界，输入只有原始模型参数、正则性范围、半径和密度界。以下模块已加入统一构建入口：

- `PartC/RateRegime.lean`、`RateLedgers.lean`：一般有效光滑度下的尺度次序、三个实际误差单项式及其带任意固定对数幂的收敛。
- `PartC/ScaleBudget.lean`：同时选择体积指数 `0 < v < d`、taper 间隙 `0 < θ < 1` 和乘子损失 `η > 0`；证明改用 `t_n = t^(1-θ)` 后的 ghost 误差及载体耦合因子仍趋零。
- `PartC/Scales.lean`：实际正尺度、精确振幅平衡以及共用振幅常数时 `j_shift ≤ j_rough` 和平方界。
- `PartC/SingleSiteBridge.lean`：两个实际 Bernoulli 编码似然的恒等式、精确多项式平移展开、带设计指数的单点 bridge。
- `PartC/RoughFieldMoments.lean`、`PhysicalRoughMoments.lean`：由有限独立 Rademacher 符号律和实际有限包分割推出前四阶矩、四阶修正及两个单点桥接；公式覆盖粗包络为零的区域，不要求外部提供权重归一化。
- `PartC/LinearPartition.lean`：以现有二次分割的平方构造线性分割，证明紧支撑、分割恒等式及中心立方体上的严格一致下界。
- `PartC/AssignmentWindow.lean`、`AssignmentPartition.lean`：采用两个光滑阶跃之差构造窄分配窗，证明光滑性、范围、紧支撑、中心平台、精确单位分割以及支撑上的载体下界。
- `PartC/AssignmentMultiplier.lean`：构造全空间光滑的正分母延拓，得到光滑紧支撑乘子 `m`，严格证明 `m * ψ = φ` 和 `0 ≤ m ≤ 1/c`。
- `WienerSpatialShift.lean`、`WienerCoordinate.lean`、`CompactIntervalWiener.lean`、`CompactChartWiener.lean`：实际 Fourier 系数上的空间平移、坐标嵌入、缩窄区间函数和闭载体图表重构；空间平移严格保持 Wiener 范数。
- `PartC/AssignmentDyadic.lean`、`AssignmentWindowWiener.lean`、`AssignmentPartitionWiener.lean`：窄窗的精确 dyadic 分解和实际 Wiener 实现，范数分别为 `C(N+1)` 和 `C(N+1)^d`。
- `PartC/AssignmentReciprocalWiener.lean`、`AssignmentMultiplierWiener.lean`：以固定紧支撑光滑修正构造倒数的 Wiener 实现，得到真实乘子及范数界。
- `PartC/DyadicPowerBound.lean`、`DyadicSelection.lean`：将层数多项式吸收到任意小幂次损失，并选择与所需过渡宽度相差不到两倍的 dyadic 宽度。
- `PartC/LatticeFields.lean`、`PhysicalRoughRegularity.lean`、`CarriedField.lean`：实际粗糙场和线性分割承载场的光滑性、导数缩放、Hölder 界及粗糙包绝对值和的统一界，常数不随包数增长。
- `PartC/MixedOutcomeControl.lean`：两个完整编码结局函数及四阶修正的统一导数界；分别在载体尺度和粗糙尺度上控制。
- `PartC/CodedModelLegality.lean`、`MixedModels.lean`、`MixedModelLegality.lean`：定义实际 P/Q 参数函数，证明真实编码似然恒等式、中心点效应，以及对所有系数和符号取值同时成立的 Hölder 与概率范围约束。
- `PartC/MixedScaleBalance.lean`、`PaperLegalFamily.lean`：两种混合情形的实际振幅精确平衡，给出固定正振幅及所有样本量下的合法参数族；不把正则性或概率范围作为外部假设。
- `PartC/AssignmentTransition.lean`：真实物理分配过渡集合可测，单块体积为 `O(r^d w)`，全部活跃块并集体积为 `O(h^d w)`。
- `PartC/AssignmentInterior.lean`：离开过渡层后，粗邻域中的每个点唯一分配给一个活跃块；其余块的分配权重与乘子为零。
- `PartC/AssignmentScaleChoice.lean`：选择实际 dyadic 宽度 `t^d/4 ≤ w ≤ t^d/2`，构造精确 Fourier 乘子，给出 `C t^(-dη)` 范数界及 `O(h^d t^d)` 全局过渡体积界。
- `PartC/SignCarrierMoments.lean`、`SignCarrierConstruction.lean`：以符号求值前的系数范数归一化，构造对所有符号共用标签律的严格正系数核；证明真实联合概率律的加权矩恒等式，并接入一般 Banach 空间固定点。此接口仍以具体极化重构和原子范数界为输入。
- `PartC/WalshCoefficients.lean`、`WalshCarrierKernel.lean`：实际 Walsh 系数 ℓ¹ 空间、范数不增的求值与投影，以及固定有限矩支撑上的正概率核。所有求值界均不随粗糙符号数量增长。
- `PartC/WalshRemoval.lean`：去除指定符号的系数投影恰等于对真实独立 Rademacher 符号重新平均；投影范数不增，去除误差由各符号分量范数之和控制。
- `PartC/WalshProduct.lean`：以符号子集的对称差定义实际乘法，证明求值乘法、系数范数的乘法界、符号分量的乘积界及所有次数的幂次界。
- `PartC/PhysicalRoughWalsh.lean`、`RoughWalshPowers.lean`：实际有限粗糙场及其幂次的连续 Walsh 系数数组；每个单符号分量恰对应相应物理包，幂次分量保留一个局部包因子。
- `PartC/RoughPacketChartVolume.lean`、`RoughWalshCentering.lean`：真实载体图表内单个粗糙包的 `O((ℓ/r)^d)` L¹ 界，实际 Bochner 积分中心化、求值与积分交换，以及中心化多项式的统一范数和单符号体积界。
- `PartC/CarrierSymbolBound.lean`：固定点在任意连续线性符号投影下的范数，由原子符号界乘以非基准标签总质量控制；原子符号界为 `O(t^d)` 时得到 `O(L t^d)`，无需另做符号半范数上的压缩证明。
- `PartC/FiniteL1Array.lean`、`RepresentativeArray.lean`：有限次数、符号子集和 Fourier 系数构成的实际 Banach 数组；次数权重吸收到系数中。证明行变换、单符号投影及局部符号去除的范数界，常数不依赖行数或符号数。
- `PartC/RepresentativeEvaluation.lean`、`PhysicalRepresentativeEvaluation.lean`：代表元到闭单位图表连续函数的实线性求值；从实际乘子和粗糙包选择统一常数，证明求值范数不增及单位代表元取值恒为 1。
- `PartC/WalshParity.lean`、`RepresentativeTensor.lean`：以有限对称差保留乘积中的 Walsh 符号，构造实际跨槽张量积并证明范数乘法界、复值求值公式及实值因子下的乘积公式。
- `PartC/RepresentativeReflection.lean`、`PhysicalRepresentativeReflection.lean`：次数与符号奇偶性定义的等距反射、范数不增的偶部投影，以及它们与真实粗糙场符号翻转的精确对应。
- `PartC/RepresentativeFactors.lean`、`NormalizedTrigCentering.lean`：实际三角基、将 Walsh 中心化系数嵌入次数零的代表元、以及归一化基的真实积分。中心化系数范数至多为 1；每个符号分量至多为 `(n/N₀) * (ℓ/(2r))^d`。
- `PartC/PositiveRepresentativeFactors.lean`、`PhysicalRepresentativeAtoms.lean`：实际单槽正密度原子，证明实值性、严格正性、积分为 1、代表元范数界和单符号体积界。
- `PartC/WalshFiniteProduct.lean`、`WalshPolarizationWeights.lean`：实际有限乘积和正极化系数；先在 Walsh 系数范数中估计，再对符号求值，界不随粗糙符号数增长。
- `PartC/RepresentativeAverage.lean`、`RepresentativeAtomDictionary.lean`、`RepresentativeSymTensor.lean`、`PolynomialPolarization.lean`：固定可数正密度字典、对称张量，以及每个多项式三角基的精确正极化恒等式。
- `PartC/PhysicalFactorIntegral.lean`、`PhysicalPolynomialDictionary.lean`：完整字典的实际物理积分为 1、严格正性、代表元范数界和单符号体积界；中心化系数由真实积分构造。
- `PartC/RepresentativeRealExpansion.lean`、`RepresentativeRealReconstruction.lean`：从保留的复 Fourier 系数直接构造实级数，同时置换每槽次数和 Fourier 槽位；重构一般代表元的对称化，实展开范数损失至多为 `2^Q`。
- `PartC/VectorSeries.lean`、`PolynomialCoefficientOperator.lean`：Banach 值绝对可和级数和完整连续线性极化算子，输出实际 Walsh 值系数；证明绝对可和性、统一范数界及 Lipschitz 界。
- `PartC/PolynomialSeriesReconstruction.lean`、`PolynomialChartReconstruction.lean`：完整极化级数的逐点重构与紧图表连续函数空间中的一致范数收敛。一般对称代表元经求值后被精确重构，没有将取值相等冒充数组相等。
- `PartC/RepresentativeTensorSymbol.lean`、`PhysicalPolynomialTensor.lean`：实际多槽密度张量的乘积公式、严格正性和范数界；每个符号分量保留 `O((ℓ/r)^d)` 因子，常数不随符号数增长。
- `PartC/VectorSeriesExtension.lean`、`VectorSeriesStack.lean`、`VectorSeriesMap.lean`、`NaturalPolynomialPolarization.lean`：把完整极化编码到自然数标签并组合为有限矩向量；零扩展保持 ℓ¹ 范数，向量范数只损失固定矩坐标数。
- `PartC/WalshReflection.lean`、`ReflectedMomentPolarization.lean`：构造反射后的完整矩系数，证明与原系数具有相同范数界，并在真实符号翻转图表上重构同一目标。
- `PartC/PairedSeries.lean`、`CarrierInvolution.lean`、`PairedCarrierOperator.lean`、`PairedSignCarrier.lean`：原标签与反射标签分别保留，两者质量相等；构造共同标签律、严格正系数核及反射不变固定点。
- `PartC/NaturalPhysicalDensity.lean`、`PairedPhysicalDensity.lean`：所有实际密度（包括常数标签）连续、积分为 1，值域在 `[1-θ,1+θ]`；多点乘积恰等于代表元原子的实际求值，并保留单符号体积界。
- `PartC/PolynomialCarrier.lean`、`PhysicalPolynomialCarrier.lean`：完整极化已经接入正载体固定点与真实密度矩恒等式，同时得到 `O(δ (ℓ/r)^d)` 的固定点单符号界。一般入口以目标算子及其对称性、小范数估计和有限矩实现接口为输入；次数为 1 和次数为 3 的实际物理目标均已由后续模块实例化。
- `PartC/RepresentativeSubstitution.lean`：在数组上构造移动次数行、乘 Fourier 系数的连续线性代换；证明实际求值公式、范数界和符号分量界，并证明与符号去除投影交换。这是具体目标算子的基础，尚非两个情形的完整代换构造。
- `PartC/PropensitySubstitution.lean`：次数为 1 的设计加权代换。被选中的位置翻转次数 0/1，并在原次数为 1 时乘归一化修正系数；实际求值、范数、符号分量和去除交换均已证明。
- `PartC/PolynomialShiftExpansion.lean`、`ShiftChoiceWiener.lean`：保留粗糙场的完整有限扰动展开，以及每项实际 Fourier 系数的 Wiener 构造和总范数界。增量从一次项开始，没有使用 Part B 先平均符号后的二次起始增量。
- `PartC/PropensityChoiceTarget.lean`：按实际扰动位置筛选多线性项，构造连续线性目标算子，证明设计加权求值和符号去除恒等式；范数常数先于粗糙符号类型选择。
- `PartC/RepresentativePermutation.lean`、`PropensityVectorTarget.lean`：同时置换 Fourier 坐标与次数行，在数组上构造范数不增的对称化；组合为有限矩向量目标，输出对称性、去除交换及准确的对称化求值公式。其范数上界为固定对数幂乘归一化振幅与 taper 阈值之比。
- `PartC/CarrierCoefficientWiener.lean`：构造实际粗包络任意固定整数次幂的 Fourier 代表；统一界不依赖活跃载体、位置或满足 `0<r≤h` 的尺度。固定截断函数在分配乘子非零处恒等于 1。
- `PartC/NormalizedPropensityCorrection.lean`、`PhysicalPropensityCorrection.lean`：实际修正项的 Fourier 构造、实值性与归一化范数界；闭图表上精确实现 `(m/N)^2 j_a^2 G_h^4`，也覆盖 `m=0`。小性条件为固定常数乘 `j_a^2≤1`，现已由尺度序列推出。
- `PartC/PaperPropensityTarget.lean`、`PhysicalPropensityTarget.lean`：实例化完整系数空间和全部 `Ψ_{4Q}` 矩坐标，构造实际小网格的有限矩实现半径；目标的值公式包含实际分配乘子和粗包络，范数常数先于粗糙符号类型选择。
- `PartC/NormalizedCarrierScales.lean`、`NormalizedAssignment.lean`：同时构造实际乘子和粗糙场所需的统一归一化，证明完整有限壳层范数上界沿尺度趋零。归一化为 `N = R t^(-dη)`，taper 阈值为 `t^(1-gap)`，保留正指数余量 `gap-dη`。
- `PartC/PaperPropensityCarrier.lean`、`ScaledPropensityCarrier.lean`、`RatePropensityCarrier.lean`：从实际矩支撑、目标算子及归一化构造共同标签律、严格正系数核和密度加权矩恒等式；实际密度连续、积分为 1、值域在 `[1-θ,1+θ]`。最终入口 `exists_rate_paperPropensityCarrier` 同时选择幂次预算、全部活跃块共用的过渡宽度和物理载体，推出目标范数趋零及固定点小性，并保持 ghost 误差单项式乘任意固定对数幂后趋零。本入口完成局部载体构造，并保留实际粗糙场范数界及归一化下界；后续模块已接到真实观测混合的信息界和粗糙倾向情形的最终 minimax 入口。
- `PartC/SitePolynomialFunctional.lean`、`PropensityPolynomialTarget.lean`、`CoefficientShiftPolynomial.lean`：将已有有限矩目标精确识别为未平均虚拟平移多项式上的线性泛函；出现位置的单射筛选恰等于每槽次数至多为 1 的截断，常数项单独保留。
- `PartC/WeightedPolynomialMoments.lean`、`PhysicalPropensityPolynomial.lean`、`PhysicalPropensityLikelihood.lean`：同一个实际正载体、可数标签律和符号依赖核，同时实现全部次数 ≤4Q 的系数多项式。`HasPaperPropensityCarrier.polynomial_realization` 包含完整基线项，保持实际密度乘积和 `HasSum`，并保留反射、正性及单符号界。
- `PartC/PropensityLikelihoodPolynomials.lean`：粗糙倾向情形的 q 点似然是次数至多 q 的实际系数多项式。保留点虚拟平移精确成为仿射槽乘积，允许任意保留／幽灵坐标划分；乘 taper 后的公式也覆盖碰撞位置。对称目标的对应公式保留了置换后的保留点索引。
- `PartC/AffineSitePolynomial.lean`、`NormalizedPropensityBridge.lean`、`FrozenPropensityMatching.lean`、`FrozenCoefficientMatching.lean`：设计加权泛函作用在仿射乘积上的精确公式，以及独立粗糙变量下的多点系数匹配。归一化桥接不除以分配乘子，所以也适用于乘子为零的位置。
- `PartC/LocalSignResampling.lean`、`PhysicalLocalSigns.lean`：从真实有限乘积概率权重证明不相交局部符号集合的重采样公式；距离大于 `2ℓ` 的物理观测点使用不相交符号集合，每点至多涉及 `2^d` 个符号。
- `PartC/PropensityRemovalEvaluation.lean`、`RemovedPropensityMatching.lean`、`PhysicalLocalPropensityMatching.lean`：去除局部 Walsh 符号后的系数目标在原始共享符号律下精确匹配真实似然增量。`removed_physical_propensity_coefficient_matching` 的局部依赖和矩条件都来自实际粗糙场；删除范数代价至多为 `q·2^d` 乘统一单符号界。后续模块已补齐保留点投影和实际对称化匹配；完整多块似然比较仍待组装。
- `PartC/PhysicalPropensityShift.lean`：实际载体图表中的承载场、归一化粗糙变量和修正系数逐项对应；归一化因子 N 精确抵消，桥接得到的效应为实际分配权重乘目标效应。
- `PartC/CarrierPermutationSymmetry.lean`：由正密度原子级数证明载体的置换对称性，并证明局部符号去除保持该性质。结论适用于任意形式实槽变量，没有从真实粗糙场图表上的取值相等推断数组相等。
- `PartC/DensityCarrierMarginals.lean`、`UnitCubeGhosts.lean`、`PhysicalCarrierMarginals.lean`：固定可数标签律、密度字典和有界系数权重的实际 ghost 投影；任意保留／辅助点划分均适用。辅助点几乎处处落在闭单位图表内，真实物理密度及其系数矩随密度乘积一起积分。
- `PartC/PhysicalPropensityProjectivity.lean`：`HasPaperPropensityCarrier.projective_realization` 用同一组 `B,H,kernel` 同时实现全部有限保留／辅助点划分、全部次数 ≤4Q 的多项式期望及增量积分公式，并保留反射、正性、配对、原子级数和单符号估计。
- `PartC/DensityCarrierPosterior.lean`、`PhysicalPropensityPosterior.lean`、`ProjectedPropensityLikelihood.lean`：从完整可数标签律的正倾斜构造真实有限系数后验。`HasPaperPropensityCarrier.likelihood_realization` 给出所有 q≤Q 的归一化保留点似然增量；分母是实际正设计边际，不增加矩匹配假设。
- `PartC/RetainedPropensityCompletion.lean`：辅助点的两个观测系数取零后，其多项式和真实似然因子严格等于 1。由此把完整配置的共享物理符号匹配用于任意保留点划分；仍保留全部槽位的真实密度次数，并明确要求完整配置的局部符号集合分离。
- `PartC/DensityGhostLeakage.lean`、`CompletedCubeTaper.lean`、`PhysicalPropensityGhostLeakage.lean`：真实密度加权的 ghost 缺陷可积，归一化误差在 `[0,1]` 内。完成单位立方体上的保测重排，将 Part B 的坏配置体积界接到实际符号依赖密度；`concrete_weighted_ghost_bound` 和 `concrete_ghost_bound` 分别给出带设计边际权重及不带权重的 `C_{Q,s,θ} τ^s` 界，对每个 `0<s<d` 成立，常数不随粗糙符号取值变化。
- `PartC/SymmetricPropensityMatching.lean`、`PaperPropensityMatching.lean`：以逆置换重排保留／辅助点划分，证明实际置换平均目标的共享符号匹配。`carrier_propensity_retained_matching` 的对称性来自同一载体的真实原子级数；在去除完整配置的局部符号后，实际修正系数及归一化粗糙变量精确产生分配权重乘物理目标效应。公式包括 taper 为零的配置。
- `PartC/PhysicalTaperSeparation.lean`、`ScaledTaperSeparation.lean`：由全局弦距离上界和完整 taper 推出物理点距离大于 `2ℓ`；对 `ℓ=t r`、`τ=t^(1-gap)` 和任意固定正 gap，这一尺度条件最终成立，并且对载体位置、半径和配置统一。共享符号匹配中的分离条件因此由实际尺度推出。
- `PartC/CrossBlockRemoval.lean`：同时去除所有关联块的指定局部符号，给出原始共享符号取值下的乘积误差界；不要求块独立或中间因子为正。删除与反射交换，因此真实物理载体乘积在全局符号翻转下仍保持偶性。
- `PartC/SharedSignParity.lean`、`PropensityPatternParity.lean`：实际一次设计代换的奇偶性等于所选槽数的奇偶性。`parity_weighted_shift_bound` 证明非空扰动项的符号平均带有 `shift * rough` 因子：一次项利用奇系数消去常数粗糙项，高次项利用 `shift² ≤ shift * rough`；物理观测点间不需要独立性。
- `PartC/WeightedPropensityPatterns.lean`、`PhysicalPatternBounds.lean`：把每个被选槽的归一化因子 N 吸收到设计代换权重，保留准确的振幅恒等式。真实物理槽满足 `|N z| ≤ N₀/c`、`|N κ| ≤ 1/(c N₀)`，所以加权目标的范数界不随 N 或物理尺度增长。
- `PartC/CrossBlockPatternRemoval.lean`、`PhysicalCrossBlockPatterns.lean`：对所有关联块的实际代换模式乘积给出共享符号删除界，包括没有扰动的关联块。`physical_propensity_pattern_shift_removal_bound` 将前述奇偶估计实例化到真实粗糙场、归一化变量和修正系数，得到固定常数乘 `η * shift * ja`，其中 η 为各块统一单符号界。常数仅依赖有限块／槽／点个数、维数及固定的 c、N₀；完整多块似然差与 Hellinger 界仍待证明。
- `PartC/CarrierDesign.lean`、`PhysicalCarrierDesign.lean`、`CarrierSampleDensity.lean`：从实际符号依赖物理密度构造全局设计，证明可测性、归一化和只依赖维数中载体重叠数的密度上下界；接口同时适用于次数 1 和 3。固定模型的独立样本测度恰有归一化密度的乘积，图表坐标与物理点的对应也已验证。
- `PartC/SharedSignPriors.lean`、`GlobalPriors.lean`：允许各块有不同标签律和依赖同一组共享符号的系数核，构造完整可数先验及实际 `Z^n` 倾斜。`tiltedCarrierPrior_cancellation` 精确抵消样本设计的归一化因子，归一化常数只依赖共同的标签／符号先验；两侧的完整 `X^n` 边际相同。没有假定倾斜后符号仍独立。
- `PartC/MixedStatisticalModels.lean`、`GlobalExperiments.lean`：把两种已证明合法性的实际混合函数族装入原来的 `StatisticalModel`，保持原始中心目标值；构造这些模型的全局观测混合，证明其为概率测度、共同设计边际，以及先验平均风险受原模型最坏风险控制。
- `PartC/CarrierPosterior.lean`、`ModelComparison.lean`：对全部标签、共享符号及系数一起条件化，证明后验可测和真实 Bayes 混合恒等式。`carrierModelConditional_raw_weight` 给出 `Z^n` 消去后的原始设计乘积公式，`carrierComparisonDensity_eq_mixture` 将共同支配测度上的比较密度精确识别为实际观测混合。`carrierComparison_minimax_lower` 是仍以实际 TV≤1/2 为前提的风险归约，不是最终 Part C 速率定理。
- `PartC/CarrierLocalSigns.lean`、`RepresentativeLocality.lean`、`PhysicalCarrierLocality.lean`：定义实际载体区域读取的有限符号集合，证明区域外符号在中心化积分、密度原子及其可数混合代表元中的投影严格为零；实际密度只依赖该集合内的符号。
- `PartC/PropensityTargetLocality.lean`、`LocalPaperPropensityCarrier.lean`：实际目标增量继承上述局部性。`HasPaperPropensityCarrier.local_realization` 将载体外符号固定后重选系数核，保留同一 `B,H`、正性、基准核、反射、原子级数和全部真实加权矩等式，同时证明核只读取本载体内的符号。没有把原先任意存在性选择的核直接当作局部核。
- `DiscreteGrouping.lean`、`PartC/SharedSignFactorization.lean`、`SharedBlockFactorization.lean`、`SharedObservationFactorization.lean`：从完整可数标签律及真实有限符号概率权重证明按分量的期望分解，再加入条件系数核。`shared_observation_factorization` 对整个原始观测乘积成立；无观测的辅助分量贡献严格为 1，因此无需假设未使用系数核之间的符号集合互不相交。
- `PartC/SharedSignIncidence.lean`、`SharedCarrierGeometry.lean`：扩大的依赖图包含观测点自己的粗糙符号及其入射载体读取的全部符号。证明不同分量的符号集合不相交；当 `ℓ≤r≤h` 时，相邻点逐坐标距离至多 `10r`，大分量包含 `Q+1` 个不同点，落在半径 `(5+10Q)h` 的粗尺度盒和半径 `20Qr` 的相对细尺度盒中。
- `PartC/MixedObservationLocality.lean`、`PhysicalDesignLocality.lean`、`PhysicalSharedFactorization.lean`：两种实际 mixed model 的二元观测概率及真实符号依赖设计乘积均满足扩大的图上的局部性。`physical_raw_observation_factorization` 将设计加权的完整原始观测混合分解为分量期望；此处尚未给出小分量似然差或 Hellinger 界。
- `PartC/LocalPropensityProjectivity.lean`：同一组局部 `B,H,kernel` 同时实现全部保留点／ghost 划分及次数不超过 `4Q` 的多项式投影；局部性、正性、反射、原子级数和原有范数界一并保留。
- `PartC/SharedBlockMoments.lean`、`BlockPolynomialExpansion.lean`、`SharedPolynomialMoments.lean`：完整多项式按块拆成单项式，证明每块所需次数不超过原多项式总次数；在实际可数标签律和条件系数核下，设计加权期望等于各块加权矩乘积的有限和。多项式本身可以依赖共享符号，符号平均始终保留在最外层。
- `PartC/MixedLikelihoodPolynomials.lean`：将全部承载系数同时作为变量，构造两种实际二元观测概率的多项式；逐点验证其等于真实模型的 cell mass。单点次数分别不超过 1、3，`q` 点乘积分别不超过 `q`、`3q`。此处次数 3 的似然表示不表示次数 3 的载体目标已经构造完成。
- `PartC/RetainedDesignProduct.lean`、`DesignWeightedPolynomialMoments.lean`、`PhysicalPolynomialProjection.lean`：把真实样本设计乘积按载体重排，只保留落在相应载体内的观测；为至多 `Q` 个观测构造固定 `Q` 槽的完成。`raw_design_weighted_polynomial_moments` 精确连接原始设计加权似然与保留点加权矩，`physical_multiblock_polynomial_projection` 再将各块投影公式组装为共享符号平均下的 ghost 积分乘积。
- `PartC/RepresentativeStability.lean`、`RoughChartResampling.lean`、`GhostSignResampling.lean`：证明形式变量变化的代价由 `‖B-unit‖` 控制，以及改变一个实际粗糙符号的归一化图表积分代价至多为 `2/(cN) * (ℓ/(2r))^d`。固定保留点形式变量后，实际 ghost 积分的单符号变化界为 `2‖symbolPart j B‖ + ‖B-unit‖ * D * card(G) * 2/(cN) * (ℓ/(2r))^d`；同时证明单符号变化界可累加为有限符号集合重采样及其平均的误差界。该结果控制积分引入的额外符号依赖，下述模块已将它扩展到所选扰动模式及其乘积。
- `PartC/BlockPolynomialFunctional.lean`、`BlockPatternFunctional.lean`、`BlockCoefficientShift.lean`、`TaperedSiteFunctional.lean`：证明任意单块多项式线性泛函的乘积恒等式，以及独立系数平移平均与各块模式泛函的交换。每个位置至多出现一次的模式由同一个全局多项式泛函提取；taper 只乘非空模式，空模式保留完整基准矩。零 taper 块关闭平移后，泛函值严格不变。
- `PartC/ObservationBlockChoices.lean`、`GlobalPropensityShift.lean`、`RetainedObservationSlots.lean`、`PropensityObservationExpansion.lean`：将实际粗糙 propensity 情形的完整观测多项式展开为“每个观测保留基准项或选择一个扰动块”的有限和，各块选择的观测集合互不相交。`completed_propensity_pattern_expansion` 使用真实保留点／ghost 配置构造插值位置和所需单射性，覆盖零 taper 块并保留每个二元观测的 `1/4` 因子，无须一般 Taylor 公式。
- `PartC/PhysicalPatternFunctional.lean`、`BlockFunctionalAverages.lean`：实际载体的原子级数推出置换对称性，并将“基准矩＋增量”精确写成上述模式泛函的置换平均；独立有限平均和实际乘积测度积分与多块多项式展开交换，积分交换只需检查该多项式支持上的有限多个单项式。后续 `RawPropensityExpansion` 已将这些恒等式接到真实设计加权观测混合。
- `PartC/WeightedPropensityStability.lean`：所选槽位的变量保持不变时，归一化模式权重的变量变化代价为 `C^Q ‖B-unit‖ Σ|z-z'|`。重采样符号的额外代价为 `2 C^Q Σ‖symbolPart j B‖`；这里的 C 只控制 `Nz`、`Nκ`，没有额外损失 `N^card(S)`。
- `PartC/PhysicalPatternContinuity.lean`、`GhostPatternResampling.lean`、`GhostPatternParity.lean`：对实际物理修正、完整配置及固定保留点形式变量证明连续性和有界性，并建立带有界可测 taper 的所选模式积分界。单符号误差至多为 `C^Q [2‖symbolPart j B‖ + ‖B-unit‖ card(G)·2/(cN)·(ℓ/(2r))^d]`；要求所选槽位来自保留点。积分和重采样平均均保留同时翻转保留变量与粗糙符号时的次数奇偶性。
- `PartC/ResamplingParity.lean`、`PhysicalGhostPatterns.lean`、`CrossBlockGhostPatterns.lean`：对多块乘积使用同一组新鲜符号进行条件平均，不引入块间符号独立性。`physical_ghost_pattern_shift_resampling_bound` 实例化实际保留点粗糙变量、物理修正和完整图 taper，对每个非空模式证明误差界仍含 `shift·ja(1+N₀)`。各块允许不同的保留／ghost 划分，空模式不乘 taper，统一常数不依赖归一化 N。
- `PartC/ObservationPatternNormalization.lean`、`GhostPatternProjection.lean`：证明非零实际观测扰动只选择保留点，所选槽位总数严格等于扰动次数，归一化 N 的幂在模式展开中精确抵消；将物理 ghost 权重的对角取值识别为实际 tapered 模式积分，并在真实乘积测度上证明多块 ghost 积分分解。
- `PartC/PhysicalFullMomentFunctional.lean`、`CompletedMomentIntegrability.lean`、`PropensityMomentWitness.lean`、`BlockFunctionalMeasure.lean`：从已构造的局部正载体选出同一组代表元、标签律和核，保留完整矩级数、局部性与范数界。真实加权矩的可积性和保留点投影由密度级数推出；完整矩泛函的置换表示可以逐块组合。
- `PartC/RawPropensityPatternIntegral.lean`、`PhysicalPropensityRawCell.lean`：把实际设计乘积及真实二元观测概率直接识别为联合 ghost 积分内的多块泛函和置换平均。共享符号仍在最外层平均；没有额外假设插值公式、矩投影或积分交换。
- `PartC/TaperedObservationNormalization.lean`、`PhysicalPatternIntegrands.lean`、`CompletedPropensityObservation.lean`、`PropensityPatternIntegration.lean`、`RawPropensityExpansion.lean`：对零 taper 配置先证明整项为零，再移除振幅掩码；归一化 N 逐个所选位置精确抵消。逐项证明可积性并交换有限展开与乘积积分后，`physical_propensity_raw_cell_expansion` 将真实原始观测混合写成符号、置换及基准系数平均下的有限模式和，每项直接使用既有的 `physicalGhostPatternWeight`。
- `PartC/PropensityObservationWeights.lean`、`ObservationPatternResampling.lean`：从基准侧实际观测系数中提出所有粗糙 propensity 因子，剩余系数与粗糙符号无关。非零系数自动保证选中槽位属于保留点及次数计数；`propensity_observation_resampling_bound` 因而把已证明的共享符号重采样界直接应用于实际非空观测项，并保留 `t·ja(1+N₀)` 因子。
- `PartC/AssignedRowBridge.lean`、`AssignedPatternExpansion.lean`、`AssignedCoefficientMatching.lean`：非分配块乘子为零时，保留所有重叠块的次数因子及零次幂，完成逐行桥接、观测选块展开与全部行系数求和。系数可为任意实数，只要求分配块在该观测处的次数至多为一。
- `PartC/CompletedPatternRows.lean`、`RetainedPatternRows.lean`、`ResampledCoefficientMatching.lean`、`CompletedSharedMatching.lean`：将各块不同的保留观测集合嵌入共同下标，ghost 幂、Fourier 系数与 Walsh 因子全部保留；非入射选择由实际零扰动系数消去。对保留点局部符号集合的并集只使用一组共享新符号，证明完整多块匹配，没有假设各块代表元独立。
- `PartC/PhysicalAssignedParameters.lean`、`PhysicalCompletedMatching.lean`、`UntaperedObservationMatching.lean`：分配内部几何给出唯一归属、非归属乘子为零及原始目标振幅；实际粗糙场的矩与空间分离推出所需桥接。`physical_untapered_observation_matching` 包含实际二元观测系数、每点的 `1/4` 因子和归一化 `N`，结论中的扰动恰为原始 `targetField`。
- `PartC/UntaperedGhostMatching.lean`、`UntaperedIncrementMatching.lean`：从实际模式界推出可积性，将上述匹配交换到真实乘积 cube 积分之外；`physical_untapered_ghost_increment_matching` 精确抵消空模式，剩余非空模式和等于同一 ghost 载体乘以目标侧与基准侧的实际似然差。下述局部比较已将该恒等式接回原始共享符号。
- `PartC/GhostTaperRemoval.lean`、`CrossBlockTaperRemoval.lean`、`ObservationTaperRemoval.lean`、`GhostTaperVolume.lean`：用实际完整图 taper 的 ghost 积分缺陷控制去除误差；跨块共享奇偶性保留 `t·ja(1+N₀)` 因子，并接到每个实际非空观测项。该缺陷位于 `[0,1]`，其保留点 cube 积分具有明确的 `C_s τ^s` 界（`0<s<d`）。
- `PartC/PropensityCellDifference.lean`、`PropensitySignRestoration.lean`：实际二元 cell 的目标侧差值至多为 `|ja·b·t|/2`，`q` 点乘积差值至多为 `2^q q |ja·b·t|/2`；据此对实际空模式 ghost 载体恢复原始共享符号，误差保留目标振幅。点值界不要求空间分离，可用于后续坏区域估计。
- `PartC/PropensityChoiceBounds.lean`、`PaperCarriedBounds.lean`：每个非空模式的实际光滑系数含至少一个 `b`，其绝对值和至多为 `(card(S)+1)^q b`。由有限系数支持及载体场的统一尺度控制构造正振幅阈值，保证所需光滑项有界；阈值独立于活动块集合、位置和空间尺度。
- `PartC/ObservationComparisonBounds.lean`、`PhysicalPropensityComparison.lean`：`physical_propensity_pattern_comparison_bound` 在粗糙点分离、分配内部和覆盖条件下汇总全部模式误差、精确抵消空模式并恢复原始共享符号。实际模式和与目标侧基准 ghost 似然的差由明确的符号变化代价与 taper 缺陷控制，仍保留 `ja·b·t`；下述模块已将基准系数及槽位完成平均，并接到实际归一化条件实验。
- `PartC/BaselineGhostCarrier.lean`：从同一 `PropensityMomentWitness` 的常数矩推出设计边际投影，并将对角空模式 ghost 积分精确识别为该载体律的 `carrierMarginal`。此处不更换载体，也不假设额外投影恒等式。
- `PartC/BaselinePropensityMixture.lean`、`AveragedPropensityComparison.lean`、`RawPropensityComparison.lean`：识别真实基准侧原始观测混合，再对纸面系数律及全部槽位置换平均。`physical_propensity_raw_comparison_bound` 直接比较所构造扰动核与常数基准核下的实际设计加权观测混合，两侧使用同一载体律及共享符号。误差明确写为置换平均，不假设 taper 缺陷对置换不变。
- `PartC/ObservationPatternCrudeBound.lean`、`CrudePropensityComparison.lean`：利用同时翻转的奇偶性，在任意配置上控制非空模式，抵消空模式并完成系数／置换平均。`physical_propensity_raw_crude_bound` 的误差为 `propensityCrudeConstant * |ja·b·t|`，不要求粗糙点分离、分配覆盖或避开过渡层；常数仍依赖观测点数和参与块数。
- `PartC/RawCarrierConditional.lean`：以真实设计乘积对标签、共享符号及系数的联合先验做正倾斜，构造有限条件概率律。两侧分母等于同一个 `rawCarrierDesignMarginal`，下界为 `((1-θ)^(5^d))^q`；合法性给出 cell 下界 `(κ²)^q`。该条件律与已有 `carrierModelConditional` 严格相等，原始混合差值可直接转成 Hellinger 平方界。
- `PartC/PropensityConditionalBounds.lean`：从同一 `PropensityMomentWitness` 构造两侧真实条件实验。`propensity_witness_conditional_crude_hellinger` 给出任意配置上的振幅平方界；`propensity_witness_conditional_good_hellinger` 给出分离、分配内部及有效覆盖条件下的细化界。二者均使用已证明的实际原始混合比较，没有把似然匹配或误差界作为额外输入。下述模块已完成与全局实际分量的限制／识别；精细空间积分和完整粗糙倾向下界现已由后续模块完成。
- `PartC/SupportedAssignment.lean`、`SupportedAssignmentGeometry.lean`：把完整匹配链中的覆盖／过渡条件缩小到粗包络非零的观测。包络为零时使用零缩放，另行处理空块集合；实际入射块集合满足这一有效覆盖条件，故不再要求支撑外观测具有分配块。
- `PartC/PhysicalBlockRestriction.lean`、`BlockPriorRestriction.lean`：删除未入射块保持实际设计乘积、承载场、cell 概率及原始似然不变。可数独立标签和条件系数的未使用坐标严格积分为 1；证明适用于仍依赖共享符号的系数核，并完成有限集合重编号。
- `PartC/RawConditionalRestriction.lean`、`PropensityExperimentRestriction.lean`：原始混合与共同设计分母同时保持不变，推出原始 `propensityWitnessConditional` 与仅保留入射块、沿用同一载体律及系数核的真实条件实验严格相等。
- `PartC/SharedComponentBlocks.lean`、`SharedComponentMarginals.lean`、`RawConditionalFactorization.lean`、`PropensityComponentHellinger.lean`：识别分量拥有的标签与实际入射块，块数不超过分量观测数乘以 `5^d`。把共享符号分量因子识别为原先验下的观测子集边缘，分别分解原始混合和设计分母，证明整样本条件概率律的真实分量乘积分解及 Hellinger 次可加性。
- `PartC/UniformPropensityConstant.lean`、`IncidentPropensityBounds.lean`：统一全部 `q≤Q`、`k≤Q·5^d` 的粗界常数，得到原始实验的 `H²≤C_Q·(ja·b·t)²`，常数不依赖总活动块数。细化界自动采用实际入射块及保留／幽灵槽位完成，并由几何证明覆盖条件；没有增加外部覆盖或槽位存在假设。振幅合法性及 smooth 小性仍是中间入口条件，已有统一小振幅定理可提供。
- `PartC/CarrierDesignMarginals.lean`：真实 `Z^n` 倾斜混合设计的任意 `m` 个不同观测坐标被 `designDensityCeiling^m` 倍的体积测度控制，常数与总样本量无关；提供柱事件概率、可积性及非负积分上界。
- `PartC/SharedClusterProbability.lean`、`SharedClusterRates.lean`：针对包含共享符号依赖的扩大图，构造可测大分量异常事件；异常事件外全部分量大小至多 `Q`。真实混合设计下其概率不超过 `C·n^(Q+1)·h^d·r^(dQ)`，并在混合情形的具体幂尺度下趋零，允许标签／符号索引集随样本量变化。

- `PartC/PropensityErrorReduction.lean`、`PropensityFineBound.lean`、`BoundedPropensityWitness.lean`：从已构造载体选择同一组矩见证，将符号变化、taper 和置换平均误差归并为固定常数乘几何代价与 ghost 缺陷。代表元符号界的常数不随样本量变化。
- `PartC/GhostDefectReindex.lean`、`GhostCostUnderCarrier.lean`、`SharedComponentCosts.lean`：证明真实 ghost 缺陷对完成方式及重编号不变，把共享符号图全部分量的缺陷之和控制为实际全局 ghost 代价，并对真实混合设计积分；保留 `n h^d τ^v` 界。
- `PartC/IncidentFineHellinger.lean`、`ObservationCountCosts.lean`、`CollisionObservationCost.lean`、`BadComponentCosts.lean`：对分量的精细 Hellinger 界自动使用实际入射块；坏分量数由粗糙碰撞对数与分配过渡层观测数控制。真实混合设计下各项均可积，并给出显式体积界。
- `PartC/GlobalPropensityCost.lean`、`GlobalPropensityHellinger.lean`、`PropensityJointComparison.lean`：合并真实分量的精细／粗糙估计，得到异常事件外的全局条件 Hellinger 界，再通过共同设计边际证明实际合法模型混合的 TV 上界；不再把条件信息界作为额外输入。
- `PartC/PropensityChoiceNormalization.lean`：每个观测展开项精确保留 `b^degree`，使奇偶性作用于有效平移 `b*t`。整个比较链的条件由过强的 `t≤ja` 修正为实际尺度满足的 `b*t≤ja`，覆盖 `α=1`，并保持原始目标振幅 `ja*b*t`。
- `PartC/PropensityCostAlgebra.lean`、`GlobalPropensityRates.lean`、`PropensityRateEnvelope.lean`：把显式积分界控制为单点、碰撞与次临界 ghost 三项，证明真实设计下全局代价积分趋零，并给出独立于所选载体的趋零数值包络。
- `PartC/PropensityFiniteMinimax.lean`、`PropensityPaperMinimax.lean`、`PropensityMinimax.lean`：选择具体正载体、固定合法振幅、统一符号常数和全部尺度，消除信息界和构造假设。最终 `paper_partC_roughPropensity_minimax` 覆盖 `0<α≤1<β` 和任意正 `ε`，对原始统计模型类证明 `C n^(-(ρ+ε))` 的下界。
- `PartC/OutcomeSubstitution.lean`、`OutcomeChoiceTarget.lean`、`OutcomePolynomialTarget.lean`：粗糙结局的次数三代换、原数组范数／符号界、精确求值和真实平移展开的三次截断目标。该目标与未平均平移多项式上的线性泛函严格相等，基线常数项恰为原代表元取值。
- `PartC/NormalizedRoughMoments.lean`、`PhysicalOutcomeVariance.lean`：给出实际归一化粗糙随机场的前四阶矩，并构造其方差的真实 Fourier 表示。范数常数独立于细尺度、活动符号数和物理块；不要求方差的 Fourier 范数小于一。
- `PartC/OutcomeVectorTarget.lean`、`PaperOutcomeTarget.lean`、`PhysicalOutcomeTarget.lean`：将三次代换组成完整 `4Q` 阶系数矩向量，进行范数不增的对称化，并插入实际归一化方差。固定的方差范数因子吸收到目标常数中，保留对符号删除算子的交换关系。
- `PartC/PaperOutcomeCarrier.lean`、`OutcomeTargetLocality.lean`、`LocalPaperOutcomeCarrier.lean`：构造真实的正三次载体和有限网格系数核，同时给出密度归一化、完整矩恒等式、代表元范数、单符号体积增益及只依赖局部粗糙符号的系数核。
- `PartC/ScaledOutcomeCarrier.lean`、`RateOutcomeCarrier.lean`：在实际混合速率尺度下选择归一化乘子与 taper，消除载体构造的小性条件，并保留后续 ghost 估计使用的同一幂次预算。`exists_rate_paperOutcomeCarrier` 不以目标算子、载体存在或矩实现为外部假设。
- `PartC/PhysicalOutcomePolynomial.lean`：把实际载体的矩恒等式推广到任意总次数不超过 `4Q` 的系数多项式。
- `PartC/NormalizedOutcomeBridge.lean`、`AssignedOutcomeBridge.lean`、`PhysicalOutcomeShift.lean`：在真实归一化下给出三次设计加权恒等式，处理重叠载体行及独立站点乘积。在分配权重为一的内部点，有效平移严格等于 `a*t`，实际四阶修正因而适用；这里没有把过渡层上的恒等式作为前提。
- `PartC/CubicSitePolynomial.lean`、`OutcomeLikelihoodPolynomials.lean`：给出三次站点泛函对多项式乘积的精确作用，构造真实保留观测似然的系数多项式，并将非零 taper 区域上的虚拟系数平移精确识别为各站点的三次 Taylor 乘积。
- `PartC/CubicTaylorEvaluation.lean`、`FrozenOutcomeMatching.lean`、`FrozenOutcomeCoefficientMatching.lean`：完整三次 Taylor 乘积在每个设计次数行上精确成为归一化桥接；冻结系数后，对独立站点律证明整个保留似然乘积的匹配，而不是只匹配单点或低阶矩。
- `PartC/OutcomeRemovalEvaluation.lean`、`RemovedOutcomeMatching.lean`、`PhysicalLocalOutcomeMatching.lean`：去除局部显式 Walsh 符号后，通过真实有限符号重采样恢复原始共享符号律。物理点分离推出局部符号集合不相交，前三阶矩及四阶修正都由实际粗糙场推出；包括粗包络为零或有效平移为零的情形。
- `PartC/RetainedOutcomeCompletion.lean`、`SymmetricOutcomeMatching.lean`、`PaperOutcomeMatching.lean`：补充点的观测系数为零，使其似然因子严格为一；由实际原子级数提供对称性，得到实际置换平均三次目标的保留点匹配。分配权重为零或一的条件只施加于粗包络非零的保留点，不要求补充点满足该条件。
- `PartC/OutcomeFullMomentFunctional.lean`、`OutcomeCarrierMarginals.lean`、`OutcomeMomentWitness.lean`：保存同一个已构造的正载体、可数标签律和局部系数核，导出含基线的完整多项式矩恒等式、可积性和实际补充点投影。所有次数不超过 `4Q` 的多项式共用这个构造。
- `PartC/BlockCubicFunctional.lean`、`TaperedCubicFunctional.lean`、`OutcomePatternFunctional.lean`：三次泛函的块张量与系数平均交换；taper 只乘非零次数模式，零模式保留真实设计基线。完整物理矩是这些泛函的真实置换概率平均。
- `PartC/CubicAssignedPolynomial.lean`、`CubicOutcomeCell.lean`：从完整多块三次多项式出发，证明非分配块的正次数权重为零时，所有跨块混合项被实际泛函消去，再应用四阶修正桥接；没有预先删掉多项式中的混合项。
- `PartC/CubicFunctionalReindex.lean`、`CubicOutcomeProduct.lean`、`CubicOutcomeRows.lean`：在块／观测坐标之间精确重排，对所有观测及全部有限载体行求和，得到完整三次多项式乘积的匹配。冻结的行系数可有任意符号，不要求行系数之间独立或为正。
- `PartC/SharedOutcomeRows.lean`、`PhysicalOutcomeRows.lean`：上述多块行匹配返回原始共享符号律，允许行系数依赖保留点局部集合以外的全部符号。物理版本从点分离、实际粗糙场与实际四阶修正导出所需概率条件。
- `PartC/CompletedOutcomeRows.lean`、`RetainedOutcomeRows.lean`、`RetainedPolynomialMap.lean`、`RetainedCubicFunctional.lean`、`BlockPolynomialMap.lean`、`RetainedBlockFunctional.lean`、`RetainedTaylorPolynomial.lean`：把真实完成配置的载体行接到保留槽位多项式；非保留坐标按零值代入，块张量泛函与这一代入精确交换。
- `PartC/GlobalOutcomeShift.lean`、`ResampledOutcomeRows.lean`、`SupportedOutcomeAssignment.lean`、`CompletedOutcomeMatching.lean`、`PhysicalCompletedOutcomeMatching.lean`、`PhysicalCompletedOutcomeAll.lean`：将全局系数平移、实际分配乘子和三次桥接连接为完整多块匹配；全部系数和补充点共用同一新符号场，涵盖空块集合。
- `PartC/BlockFunctionalShift.lean`、`OutcomeObservationExpansion.lean`、`CubeGhostIntegrability.lean`、`OutcomePatternContinuity.lean`、`OutcomeGhostIntegration.lean`、`OutcomeObservationMatching.lean`：完成系数平均、补充点积分和实际二元观测多项式的匹配。可积性由紧立方体上的连续性推出，保留 `4^(-q)` 归一化和物理目标振幅 `a*t*jb`。
- `PartC/OutcomePatternParity.lean`、`WeightedOutcomePatterns.lean`、`WeightedOutcomeStability.lean`、`PhysicalOutcomePatternBounds.lean`、`PhysicalOutcomePatternContinuity.lean`：给出三次模式的次数奇偶性、不额外随 `N` 增长的归一化范数界，以及保留中心化范数 `‖B-unit‖` 的变量变化界。
- `PartC/GhostOutcomePatternResampling.lean`、`GhostOutcomePatternParity.lean`、`PhysicalGhostOutcomePatterns.lean`、`ScalarParityBounds.lean`、`ScalarResamplingParity.lean`、`OutcomeTaylorBounds.lean`、`CrossBlockGhostOutcomePatterns.lean`：将单符号和有限集合重采样界推广到带实际三次 Taylor 系数的多块乘积。系数的常数项允许为零；奇偶消去仍保留有效平移乘粗糙振幅的因子。
- `PartC/GhostOutcomeTaperRemoval.lean`、`ScalarComparisonParity.lean`、`CrossBlockOutcomeTaperRemoval.lean`：以实际图 taper 的缺陷积分控制单块和多块去除误差，在共享符号平均后继续保留平移乘粗糙振幅。
- `PartC/CubicObservationChoices.lean`、`CubicObservationNormalization.lean`、`CubicObservationMasks.lean`、`OutcomeObservationResampling.lean`：保留每个观测的全部 0–3 次及跨块选择，精确计数并吸收每次出现对应的 `N`，去除仅在零 taper 区域使用的辅助掩码。非零物理分区系数直接推出重采样所需的保留槽位条件。
- `PartC/CubicGhostIntegration.lean`、`OutcomePatternIntegration.lean`、`CubicObservationChoiceBounds.lean`、`CubicObservationRescaling.lean`：有限三次展开与真实补充点积分精确交换，给出选择项数、总次数及权重界，将每个正次数出现的归一化因子移入模式权重。
- `PartC/PhysicalOutcomePatternIntegrands.lean`、`CompletedOutcomeObservation.lean`、`IntegratedOutcomeObservation.lean`：完成配置的实际观测多项式化为归一化三次模式；系数平均与补充点积分由连续性保证可以交换，保持 `4^(-q)` 和有效平移 `a*t`。
- `PartC/RawOutcomePatternIntegral.lean`、`PhysicalOutcomeRawCell.lean`、`RawOutcomeExpansion.lean`：同一已构造的三次载体矩见证，将真实设计加权原始观测混合精确识别为上述有限模式展开及全部槽位置换的平均，可积性与投影恒等式均从构造导出。
- `PartC/BaselineOutcomeGhostCarrier.lean`、`BaselineOutcomeMixture.lean`：零次模式恰为同一载体律的设计边际，并精确给出固定纸面系数律下真实基准侧混合的表达式。
- `PartC/CubicObservationBaseline.lean`、`UntaperedOutcomePatternIntegration.lean`、`UntaperedOutcomeObservationMatching.lean`、`OutcomeObservationIncrementMatching.lean`：识别唯一零次选择并严格抵消；共享符号重采样后，其余正次数模式的总和恰为同一补充点载体乘两侧实际观测似然之差。
- `PartC/OutcomeObservationTaperRemoval.lean`、`OutcomeCellDifference.lean`、`OutcomeSignRestoration.lean`：将去除 taper 的误差界实例化到真实三次观测项，并证明匹配后恢复原共享符号的误差界。误差保留完整目标振幅 `a*t*jb`；单点似然差不超过 `3|a*t*jb|/2`。
- `PartC/FinitePatternComparison.lean`、`CubicObservationFactors.lean`、`CubicObservationChoiceInstances.lean`、`OutcomeObservationFactors.lean`：统一有限模式比较、三次展开的精确因子分解和选择类型的有限枚举，识别两侧共同的零次基线。
- `PartC/OutcomeObservationErrors.lean`、`OutcomeObservationComparison.lean`、`AveragedOutcomeComparison.lean`、`RawOutcomeComparison.lean`：汇总共享符号重采样、去除 taper 和恢复原符号三类误差，经系数及置换平均后控制同一实际载体下的原始观测混合差。
- `PartC/CubicPatternBounds.lean`、`OutcomeObservationPatternBounds.lean`、`CrudeOutcomeComparison.lean`、`RawOutcomeCrudeComparison.lean`：利用三次模式的范数与奇偶性，给出任意配置上的粗比较界，始终保留目标振幅 `a*t*jb`。
- `PartC/OutcomeConditionalBounds.lean`、`UniformOutcomeConstant.lean`、`BoundedOutcomeWitness.lean`：将原始混合比较转为真实条件 Hellinger 界，并从同一已构造载体选出具有统一单符号界的矩见证；常数独立于样本量。
- `PartC/OutcomeErrorCompletion.lean`、`OutcomeErrorReduction.lean`、`OutcomeFineBound.lean`：证明误差与完成方式无关，将其平方控制为目标振幅平方乘局部几何代价与实际 ghost 缺陷。
- `PartC/OutcomeBlockRestriction.lean`、`OutcomeExperimentRestriction.lean`、`IncidentOutcomeBounds.lean`、`IncidentOutcomeFineHellinger.lean`：将真实实验精确限制到观测命中的块，得到可直接用于实际依赖图分量的统一精细界和粗界。
- `PartC/OutcomeComponentHellinger.lean`、`GlobalOutcomeCost.lean`、`GlobalOutcomeHellinger.lean`、`OutcomeJointComparison.lean`、`GlobalOutcomeRates.lean`：合并分量 Hellinger 界，对真实混合设计积分，并通过共同设计边际得到实际模型混合的 TV 上界；具体混合速率下全局误差积分趋零。
- `PartC/OutcomeFiniteMinimax.lean`、`OutcomePaperMinimax.lean`、`OutcomeMinimax.lean`、`Minimax.lean`：连接有限样本风险归约、具体正载体、合法振幅和全部尺度，得到粗糙结局的任意正 `ε` 入口，并用 `paper_partC_minimax` 统一两个混合情形。尺度条件使用 `a*t≤jb`，包括 `β=1`。

当前 Part C 目录包含 399 个模块、37,090 行、33,334 个非空行；加上为 Part C 新增的
5 个公共分析模块，合计 404 个模块、37,416 行、33,619 个非空行。
399 个 Part C 模块全部进入统一构建，两个分支均已连接实际正载体、局部原始混合比较、条件 Hellinger、全局 TV 与最终 minimax 下界。
最终整库构建与公理审计均已通过（2026-10-04），共检查 5,334 个定理/构造入口，命令退出码为 0。
审计仅允许 `propext`、`Classical.choice`、`Quot.sound`；完整原始输出保留在本地 `verification-partC.log`，副本为 `partC-build-latest.log`。日志不进入仓库，公开的结果摘要与复核命令见[验证记录](../docs/VERIFICATION.md)。
审计保留全部项目定理与所列构造的完整依赖扫描，移除了重复遍历相同依赖的逐条诊断打印。

两种情形均使用实际概率对象上的比较定理，并在最终入口内部选择正载体、合法振幅、统一符号常数和全部尺度。
形式化采用更宽的 taper `t^(1-gap)`、次临界体积指数 `v<d` 和任意小的乘子幂次损失，替换 TeX 的部分精细对数估计。
`ScaleBudget.lean` 同时选择这些损失，证明它们由任意给定的正 `ε` 所提供的指数余量吸收；因此最终的 `ρ` 和 `n^(-(ρ+ε))` 下界与 TeX 相同。
先对充分小的正 `ε` 完成构造，再通过幂次单调性扩展到任意正 `ε`。

乘子的最终分析入口是 `exists_assignment_multiplier_wiener`。对任意 `η > 0`，
它构造固定的 `c > 0`、`C ≥ 0`，使每个 `0 < w ≤ 1/4` 都有
`w ≤ 2^(-N) < 2w` 及一个真实 Fourier 元素 `M_N`，满足
`‖M_N‖ ≤ C w^(-η)`。该元素在整个闭单位图表上恰等于
`assignmentMultiplier c (2^(-N)) (4u-2)`；乘子在全空间上满足精确分割恒等式和统一上界。
证明采用光滑阶跃差的 dyadic 望远镜分解，每一层通过已有周期化定理和空间平移得到统一 Wiener 界。
这里已证明具体的乘子估计；完整极化构造的物理正载体已经接入两个混合情形的实际目标算子、观测比较和最终风险下界。

代表元采用有限“每槽次数 × 符号子集”数组，保留 Fourier 系数；相等性定义在数组上，不能由取值相等推出。
实际线性算子、跨槽张量积和范数界接入正载体固定点；扩大的依赖图同时包括粗糙包符号、载体标签和局部系数核的全部符号依赖。
两个全局 TV 界均作用于合法模型上的真实先验混合，最终 minimax 定理没有把载体存在、模型合法性、矩匹配或 TV 趋零作为输入。

实际参数族的入口为 `exists_roughPropensity_legal_family` 和 `exists_roughOutcome_legal_family`。
它们适用于任意固定有限系数支撑，所以可直接实例化已有 moment-grid 支撑；
次数为 1 和次数为 3 的局部载体概率律与密度均已构造，并通过共享符号全局先验、Zⁿ 倾斜、多块信息比较与全局 TV 界连接到最终下界；参数函数的正则性由上述入口保证。
图表内单个粗糙包的 `O(t^d)` 积分界和中心化多项式的单符号界已经构造；
中心化已经接入有限次数代表元并产生完整的真实正密度字典。代表元在闭单位图表上求值，
仅对平滑系数使用 Wiener 范数；粗糙场的实际求值由 Walsh 范数和连续性控制。
该求值、单槽积分和完整极化重构路线已经验证，无需把单个粗糙包的统一 Wiener 范数作为输入；
反射配对、物理载体固定点、两个具体增量算子、实际 ghost 投影及次临界积分界均已完成；实际对称化匹配和保留目标振幅的跨块模式删除界已用于两个分支的完整多块信息比较与原始 minimax 终点。
`SignCarrierConstruction.lean` 已复用 `CarrierFixedPoint.lean` 的一般 `CarrierCoefficients E V`，
扩展了符号依赖系数核的接口。`WalshCarrierKernel.lean` 给出其具体 Walsh 系数版本。
`exists_physical_polynomial_carrier` 进一步消除了外部极化和原子重构假设，输出真实密度加权矩恒等式与单符号界。
它的一般接口由 `exists_rate_paperPropensityCarrier` 和 `exists_rate_paperOutcomeCarrier` 分别在次数为 1 和次数为 3 的情形实例化，包括具体目标增量、小范数估计和有限矩网格参数；多块匹配接到原始共享符号的局部模式比较、实际观测混合的信息界和趋零的全局数值包络，并用于两个最终 minimax 下界。

## 文件与论文的对应

| 文件 / 定理 | 内容 | TeX 标签 |
| --- | --- | --- |
| `FiniteExpectation.lean` | 非负且总质量为 1 的有限概率律、期望、协方差、独立乘积律 | 基础定义 |
| `CubicBridge.codedLikelihood_eq_factors` | 编码似然等于倾向与条件结局因子的乘积 | Part I 的编码似然 |
| `CubicBridge.expect_cubic` | 扰动后的三次多项式期望 | `B:eq:partial-k` |
| `CubicBridge.expect_mul_cubic` | 扰动后的四次乘积期望 | `B:eq:partial-pk` |
| `CubicBridge.cubic_covariance` | 精确三次协方差恒等式 | `B:lem:cubic` |
| `CubicBridge.single_site_likelihood_bridge` | P、Q 两侧的完整单点编码似然相等 | `B:eq:two-sides`、`B:eq:walsh-vector` |
| `Rademacher.signSum_moments` | 任意有限独立符号和的前四阶矩 | `B:eq:variance`、`B:eq:fourth-moment` |
| `Rademacher.aggregate_likelihood_bridge` | 由实际符号乘积律推出桥接，不再假设矩公式 | 同上及 `B:lem:cubic` |
| `IndependentSites.joint_aggregate_likelihood_bridge` | 任意有限个观测的完整似然匹配；条件于固定基线场 | `B:lem:cubic` 的多点应用 |
| `IndependentSites.joint_propensity_match` | 部分扰动下，纯倾向 Walsh 系数仍精确相等 | `B:lem:partial-stability` |
| `BinaryExperiment.binaryLaw`、`binary_cell_lower` | 在明确参数范围内，L/4 非负、总质量为 1，并有显式下界 | 二元实验合法性与局部 Hellinger 的概率基础 |
| `PartialRademacher.partial_sign_moments` | 任意块子列表的奇数阶矩为零、方差与四阶矩上界 | `B:eq:partial-k` 前的矩估计 |
| `PartialRademacher.partial_aggregate_walsh_stability` | 单点部分扰动误差 ≤ 3 c j²，矩界由符号律推出 | `B:lem:partial-stability` 的单点部分 |
| `PartialRademacher.joint_partial_aggregate_walsh_stability` | 多点部分扰动误差 ≤ 3 Σᵢ cᵢjᵢ² | 同一引理的有限乘积部分 |
| `MomentPerturbation.exists_positive_moment_radius` | 给定矩映射右逆，在同一组原子上实现小矩扰动，所有质量严格为正 | `lem:moment-simplex` 的权重扰动步骤 |
| `ComponentMixture.partial_mixture_cell_bound` | 部分扰动混合分布的单元误差 ≤ ε Σₖ(1−χₖ) | `B:eq:component-cell-difference` 的有限概率步骤 |
| `ComponentMixture.partial_mixture_hellinger_bound` | H² ≤ (#Ω) ε² / λ · Σₖ(1−χₖ) | `B:eq:component-hellinger-local` 的有限概率步骤 |
| `CarrierFixedPoint.exists_unique_positive_fixed_point` | 从可数系数的 ℓ¹ 界证明收敛、压缩、唯一固定点、半径和总质量 < 1 | `B:eq:phi-contraction` 至 `B:eq:D-fixed-point` |
| `DiscreteLaw.joint_label_marginal` | 可数标签和有限条件系数律组成实际联合概率律；标签边缘不受条件律改变 | `B:prop:carrier` 的共同 H 边缘 |
| `CarrierProbability.fixed_point_density_hasSum` | 同一标签律的密度原子级数收敛到固定点 D | `B:eq:DQ` |
| `CarrierMoments.carrier_master_moment` | 两侧联合律的加权矩差等于极化系数级数，包括零权重标签 | `B:eq:master-moment` 的概率实现 |
| `CarrierConstruction.eventually_hasPositiveCarrier` | 给定极化、消失的增量范数界和矩右逆，对所有充分大 n 构造共同标签载体及精确矩差 | `B:prop:carrier` 的条件版本 |
| `WienerSeries.regroup_bound` | 实际 ℓ¹ Banach 空间、绝对收敛合成、任意频率合并时范数不增 | 配置空间 Fourier 拉回中的频率合并步骤 |
| `WienerFourier.norm_eq_fourier_tsum` | 系数序列实现为连续环面函数，提取 Fourier 系数恢复原序列，范数等于真正的 Wiener 范数 | `cW` 的基础 |
| `WienerAlgebra.toContinuous_convolution` | 构造卷积乘法，证明实现为逐点乘法以及范数乘法界；给出完备实赋范代数实例 | Wiener Banach 代数 |
| `WienerTrigonometric` | 具体正弦、余弦及去均值序列，Wiener 范数 ≤ 1、实值性、零频系数 | 正极化的实三角基 |
| `WienerTensor.tensor_norm` | 不同环面槽位的张量积、对称化及其实际 Wiener 范数界 | 对称张量的实现 |
| `PolarizationAlgebra.positive_polarization` | 任意正整数阶的显式容斥极化公式，以及有限系数总绝对值界 | `lem:polarization-identity` 的等价公式 |
| `PositiveWienerAtoms.dictionary_integral`、`dictionary_positive` | 固定可数字典，积分为 1，逐点位于 `[1−θ,1+θ]`，Wiener 范数 ≤ `1+θ` | `B:eq:positive-atoms` |
| `WienerStencil.synthesis_extendStencil` | 将有限线性展开扩展到完整 ℓ¹ 空间，证明范数界和级数重构 | 正极化的可数延拓步骤 |
| `PositiveWienerPolarization.coefficientOperator_reconstruction` | 对绝对可和实三角张量展开，具体线性极化算子在 Wiener 范数中精确且绝对收敛地重构 | `B:lem:positive-polarization` 的展开域版本 |
| `WienerRealExpansion.realExpansion_reconstruction` | 从任意对称实 Wiener 函数的实际 Fourier 系数构造规范实三角展开，范数 ≤ `2^Q ‖A‖_W`，并精确重构 | 正极化的 Fourier 转实三角接口 |
| `WienerSymmetric` | 按实际函数的实值性和置换对称性定义闭子代数，并证明其完备性 | 固定点的实际 Banach 空间 |
| `PositiveWienerComplete.carrierPolarization` | 自然数标签、有限向量系数、完整 Wiener 范数界及重构，构造实际 `CarrierPolarization` | `B:lem:positive-polarization` 在论文所用有限坐标空间中的完整版本 |
| `PositiveWienerComplete.eventually_hasPositiveWienerCarrier` | 在实际 Wiener 代数上接入载体定理；无需另行提供极化数据 | 通用接口；`J_n` 估计已由 `PaperWiener` 提供，矩右逆属于第 2 项 |
| `SignMonomials.expect_signPolynomial` | 任意次数有限符号多项式的精确奇数项消去；非恒定存活项总次数 ≥ 2 | `B:lem:wiener-increment` 的 parity 步骤 |
| `ConfigurationShells.admissible_card_bound`、`inverse_order_ledger` | 顶点总层级有界时壳层数 ≤ `(L+1)^#E`，并证明逆阶指数的精确计数恒等式 | `lem:admissible-shells` 的计数部分及 `B:eq:inverse-order-ledger` |
| `WienerLattice.anisotropicKernel_tsum_bound` | 各坐标独立取正整数尺度，归一化格点求和界与全部尺度无关 | 各向异性 Fourier 求和的乘积衰减版本 |
| `WienerConfiguration.configurationPullback_value`、`configurationPullback_of_decay` | 任意有限配置图的实际函数拉回和 Wiener 范数界，允许共享顶点和环路 | 配置空间拉回的 Fourier 步骤 |
| `WienerDerivativeDecay.compact_profile_wiener_bound` | 实际 Fréchet 导数界、共同紧支集推出 Fourier 采样系数的统一 ℓ¹ 界 | 壳层分析所需的通用欧氏 Fourier 估计 |
| `SmoothCompact.compact_slice_derivative_bound`、`WienerSmoothFamily` | 由联合光滑性和参数/支集紧性证明统一切片导数界及 Fourier 界，无需另行输入导数常数 | 紧参数族的一致分析 |
| `ShellGeometry`、`ShellProfiles` | 用实际 sinc 延拓重写弦长和 Lagrange 商，证明缩放公式、分母正性和局部光滑性，包括零尺度 | `cor:configuration-multipliers` 的细壳层公式 |
| `FineShellBounds` | 固定紧环带上的真实缩放商与弦长有统一导数界；弦长有统一正下界 | 细壳层的统一光滑性 |
| `ProductTaper.productTaper_uniform_derivatives` | 将任意非负尺度局部截断到固定紧区间，证明真实 product taper 的统一导数界 | `eq:rescaled-product-taper` 的分析步骤 |
| `TaperShellBudget` | 非零 taper × 壳层截断推出顶点逆距离预算与对数层级预算 | `lem:admissible-shells` 的支集步骤 |
| `WienerPeriodization`、`PeriodizedTorus` | 实际整数平移求和局部有限，保留光滑性，下降为连续环面函数；中央支集内没有额外副本 | 匹配周期的实际函数构造 |
| `LatticeUnfolding`、`PeriodizedFourier`、`FourierRescaling` | 基本胞积分展开、乘积 Haar 测度、各向异性 Jacobian 与 Fourier 相位 | 真实 Fourier 系数的积分计算 |
| `PeriodizedWiener.periodized_coefficient_eq_sampled` | 周期化函数的实际 Fourier 系数等于带正确体积因子的欧氏变换采样 | 周期化与 Fourier 采样的接口 |
| `WienerReconstruction`、`CompactPeriodizedFamily` | 从真实系数构造 Wiener 元素并逐点重构；统一界经过配置图拉回后不增 | 实际函数层面的统一 Wiener 估计 |
| `SmoothWindow`、`MixedPeriodization.mixed_family_configuration_wiener` | 显式光滑窗的整数平移和为 1；精确转换周期基点/紧支集边变量并给出混合 profile 的图拉回界 | `lem:configuration-pullback` 的光滑紧参数族版本 |
| `TaperWiener.tapered_family_wiener` | 实际紧支集 profile × product taper 有统一 Wiener 实现，常数与所有非负 taper 尺度无关 | 将 taper 估计接入 Wiener 函数 |
| `DyadicCutoffs` | 实际非负光滑 dyadic 截断与粗层余项、有限分割恒等式、具体支集预算和区分粗细标签的计数界 | dyadic 分割与 admissible shells |
| `FineLocalizedProfiles.localizedProfile_uniform_wiener` | 实际细壳层 Lagrange 商 × dyadic 截断 × 给定固定环带截断，零尺度处仍光滑，周期化后有统一 Wiener 界 | 单边细壳层的分析接口 |
| `ChordBounds`、`TruncatedDistance`、`AnnularCutoff` | 显式光滑截断距离、弦长上下界、固定紧环带截断；截断在实际细壳层上等于 1 | 截断距离与固定环带的具体选择 |
| `CentralShellLift`、`ElementaryCoefficients`、`FineFactorEvaluation` | 唯一中央差值提升、整数周期性、正反向真实系数与缩放 profile 的精确等式 | 局部差值及系数的几何匹配 |
| `FineShellDomain`、`FineEdgeWiener` | 固定紧环带上的共同正下界，原始单边乘子的实际 Wiener 估计 | 细壳层原函数 |
| `MixedShellDomain`、`MixedShellProfiles`、`MixedShellWiener` | 全部粗细边、重复因子及共同 taper 的联合光滑性、支集、紧参数族估计 | 完整多参数 profile |
| `MixedEvaluation`、`ConfigurationPeriodization`、`MixedShellEvaluation` | 无额外周期副本、图拉回、实际乘子与归一化 profile 的精确等式，允许共享顶点与环路 | 配置乘子的实现 |
| `MixedShellRealization.actual_shell_uniform_wiener`、`GraphShellMultipliers` | 每个真实图壳层的 Wiener 界，统一处理全部粗细模式 | `cor:configuration-multipliers` 的具体应用 |
| `FiniteShellPartition`、`IncidentFactorLedger`、`TaperedProductWiener` | 有限壳层精确分割、实际顶点预算、壳层求和后的重复因子乘积界 | `lem:admissible-shells` 与逆阶账目 |
| `LagrangeCoefficients`、`LagrangeProductWiener` | 原生多元多项式的真实 Lagrange 系数，包括负常数项；任意重复系数乘积的 tapered Wiener 界 | `eq:elementary-lagrange-multipliers` 与 `B:eq:generic-shift-term` |
| `ShiftedMonomials`、`IdealIncrementExpansion` | 实际独立符号平均的精确展开；基线项相消、一次项为零 | `B:eq:ideal-increment` 的展开 |
| `IdealIncrementWiener`、`IdealIncrementLogBound` | 实际单项矩增量的逆二次估计及对数壳层因子 | `B:eq:wiener-increment-strong` 的坐标版本 |
| `LogarithmicScale`、`IdealIncrementLimit` | `t=x^{-p}`、`t_n=t(1+log x)^B`，证明实际 Wiener 增量的速率及趋零 | `B:eq:wiener-increment` |
| `CompleteGraph`、`CompleteEdgeCard`、`IdealIncrementSymmetry` | 完全图的邻点积、边数 `choose Q 2`、实际 `J_n` 的实值性和置换对称性 | 对称 Wiener 闭子代数的成员证明 |
| `IdealIncrementDiagonal` | 碰撞距离为零时 taper 和实际增量均为零 | 跨对角线的零延拓 |
| `IdealIncrementVector`、`PartBAnalyticComplete` | 汇总全部次数不超过 `4Q` 的非恒定矩，并接入已构造的正极化和正载体定理 | 完整 `Ψ_{4Q}` 的分析结论 |
| `PaperWiener.paper_item_one` | 使用完整的次数 ≤ `Q−1` 系数基、原文的向量 Wiener 范数，组合具体速率、趋零和正载体结论 | 第 1 项的最终入口；矩右逆仍是第 2 项输入 |

上述表格中的文件位于 `CausalLowerbound/` 或其 `PartB/` 子目录；所有 Part B
定理的 Lean 命名空间均以 `CausalLowerbound.PartB` 为前缀。载体结果另使用
`CarrierCoefficients`、`CarrierPolarization` 子命名空间。

## 数学接口

`FiniteLaw.expect` 定义为实际有限加权和。独立性由 `FiniteLaw.prod` 和
`FiniteLaw.independent` 的乘积权重实现；`signLaw` 是逐个加入公平二元符号的
递归乘积律。有限混合也构造成了非负、总质量为 1 的实际概率律。

主定理 `aggregate_likelihood_bridge` 接受任意有限实数权重列表 `w`，要求
`sumSq w = 1`。对应论文中的参数为：

- `w_k = φ(u_k(x))`，`sumFourth w = q₄(x)`；
- `j = a t G_h(x)`，`c = b/a`；
- `η = j² (3 − 2 q₄)/3`，`d_* = c j²`；
- P 侧编码基线结局为 `K(p) − d_* (1 + 2p)`，等于论文中的
  `u_x(p) − d_* (1 + p)`。

通用桥接定理使用无除法的修正条件 `3 η E[δ²] = E[δ⁴]`，因此也覆盖零方差。
聚合定理则从乘积概率律和二次分割恒等式证明全部所需矩条件。似然等式对任意
实数 `R,T` 成立，因而特别适用于编码的二元观测。

## 定量结果的假设与边界

部分扰动用 `u.Sublist w` 表示，可取空子列表，也可保留全部块。单点稳定性只需
`sumSq w = 1`、`|p| ≤ 1`、`c ≥ 0`、`j² ≤ 1`；部分方差、四阶矩和
`0 ≤ η ≤ 1` 均已证明。单点 outcome 误差 ≤ c j²，interaction 误差 ≤ 3 c j²。

联合稳定性另外要求 P 参数和每个虚拟 Q 参数满足 `BinaryLegal`，即倾向系数和
两个条件结局系数均在 [-1,1]。因此每个 Walsh 系数绝对值 ≤ 1，乘积误差 ≤
3 Σᵢ cᵢjᵢ²。这里不假设基线场独立，只对给定基线后的虚拟符号取独立乘积。
实际几何构造中的 d_*(x) ≤ CΔ 现由 `PhysicalPartialStability` 接入。

矩扰动定理的输入是有限特征表、严格正的基线质量和 `MomentRightInverse`：
其列的质量和为零，对指定矩的作用为单位向量。定理证明存在 δ > 0，使每个满足
`∀ i, |v i| ≤ δ` 的扰动都能由同一有限样本空间上的严格正概率律实现。
这个通用引理单独不构造支持点和右逆；完整的具体构造位于 `MomentSupport`，
并已接入最终定理。

局部混合定理以每个块的 χₖ ∈ [0,1] 构造实际独立 Bernoulli 权重。要求所有部分
扰动律的单元误差 ≤ ε、完全扰动律与 P 精确相等，以及 P 的每个单元质量 ≥ λ > 0。
由此证明误差和 Hellinger 界。H² 定义为 Σ(√p−√q)²，不含可选的 1/2 因子。
通用引理所需的实际后验识别和 Walsh 误差，现由 `PhysicalActivation`、
`PhysicalRetainedLikelihood` 与 `PhysicalLocalHellinger` 证明并接入全部组件分布。

## 正载体构造已经证明到哪里

现在已经处理可数标签，而不局限于有限混合。`DiscreteLaw` 的质量非负且满足
`HasSum weight 1`；与有限条件系数律组合后，联合概率律的总质量和共同标签边缘
都已经证明。对无穷级数的拆分、相减、条件期望均提供了收敛依据。

固定点部分在完整 Banach 空间内使用

```text
ω_m(D) = K ‖a_m(D)‖
Φ(D) = e + Σ_m ω_m(D) (F_m − e)
q = K M L,   L = C_pol δ_n
```

由系数的绝对可和性及 ℓ¹ Lipschitz 界，推出 Φ 的 Lipschitz 常数为 q。
当 q ≤ 1/2、2 K L < 1、‖e‖ ≤ 1 时，证明唯一固定点 D 满足
`‖D−e‖ ≤ 2q`、`Σ_m ω_m(D) < 1`。残余质量放在常数原子 e 的标签上，
其密度矩级数恰好收敛到 D。

`CarrierPolarization` 是抽象接口：它包含一个线性系数映射、绝对可和范数界、
原子范数界，以及极化重构恒等式。现在已经在实际的对称实 Wiener 闭子代数上
构造了这个接口的实例。已经证明将它与小线性增量
映射 J 复合，确实给出上面需要的系数 Lipschitz 界。也已定义论文实际使用的
乘法映射 `D ↦ (D J_i)_i`，并证明其算子范数由 ‖J‖ 控制。

最终条件定理 `eventually_hasPositiveCarrier` 调用此前的有限矩半径定理，
内部选择 K，利用 δ_n → 0 验证充分大 n 的小量条件，并构造：

- 两侧相同的标签边缘，及同一有限系数支持集上的严格正条件律；
- 一个共同标签律，其密度矩等于 D；
- 精确的 Banach 空间值矩恒等式，矩差等于 J(D)。

`PositiveWienerComplete.eventually_hasPositiveWienerCarrier` 是保留的通用接口。
新的 `PaperWiener.paper_item_one` 已为它构造具体 `J_n`，证明其范数消失并调用
实际正极化。该通用接口仍接受有限基线律及其矩右逆作为参数；
`MomentSupport` 已在实际小球网格上构造二者。`SmallDensityCarrier` 进一步将
它们接入任意小密度幅度的正载体，`ConcreteModels` 使用这一构造完成第 2 项。

## 第 1 项的完成边界

各模块包含实际构造，没有增加数学公理或把重构恒等式放进假设。
`Wiener.Fourier d` 是 `ℓ¹(ℤ^d, ℂ)`，通过有界线性映射实现为连续环面函数。
已证明实现是单射、其 Fourier 系数就是原序列，并构造卷积、单位元、
交换环与 `NormedAlgebra ℝ` 实例。完备性来自实际的 ℓ¹ 空间。

极化使用与论文 Vandermonde 公式等价的容斥公式。对任意 `Q≥1`，将实三角函数
写成常数和零均值部分，再通过 `1+θg` 的有限平均生成原子。固定字典与待分解张量无关，
每个原子的积分为 1，`0<θ<1` 时严格为正，且 Wiener 范数 ≤ `1+θ`。
原子张量幂的 Wiener 范数 ≤ `(1+θ)^Q`。

此前 `PositiveWienerPolarization` 只处理给定的实三角展开。现在由
`WienerRealExpansion` 直接从函数的复 Fourier 系数构造实线性映射 `A ↦ a(A)`，
并证明对每个对称实 Wiener 函数：

```text
‖a(A)‖₁ ≤ 2^Q ‖A‖_W
S(a(A)) = A
```

把它与极化算子复合后，系数范数界已经是针对函数本身的 `‖A‖_W`，
不再依赖调用者提供的展开。实值性和对称性按连续函数逐点定义，所成子代数是闭的，
因而继承实际 Wiener 范数的完备性。自然数标签的空编号使用常数密度 1。
`naturalDensity_integral`、`naturalDensity_positive`、`naturalAtom_factorization`
分别证明单点密度积分为 1、`0<θ<1` 时严格为正，以及载体原子等于其 Q 次张量积。

对于论文实际使用的有限坐标空间 `I → ℝ`，`vectorCoefficients` 是一个线性映射，
其总系数范数 ≤ `(#I) C(Q,θ) ‖A‖`。结合重构、原子范数界和完备空间，
`carrierPolarization` 已构造完整接口，具体 Wiener 载体定理已经调用它。

Wiener 估计的通用分析部分也有实际进展。设 `p` 为总维数，已经证明：

```text
Σ_{k∈ℤ^p} ∏_i [N_i⁻¹ / (1+(k_i/N_i)²)] ≤ C_grid^p,  N_i 为任意正整数
```

再使用真实 Fourier 变换的导数定理，证明紧支集欧氏函数 `f` 的导数至 `2p` 阶
有统一界时，归一化采样系数 `(∏ N_i⁻¹) 𝓕f(k_i/N_i)` 的 ℓ¹ 范数有统一界。
常数仅依赖维数、共同紧支集及导数界，不依赖各坐标周期。
这采用了比原文通用引理更高的导数阶数；论文具体壳层 profiles 对任意固定阶均要求
一致光滑，因此该路线可用于其应用，但不能把它说成原文最弱正则性版本已经证明。

现在已经证明周期化函数的实际 Fourier 系数等于这些采样值，并通过绝对收敛
Fourier 级数重构为同一个连续函数。基点的周期坐标由显式光滑窗处理：
`smoothWindow(x)=smoothTransition(x+1)−smoothTransition(x)`，其整数平移和
精确等于 1。因而混合周期化的转换也是等式，并未假设重构恒等式。
配置图的实际逐点拉回与范数不增随之接入。

具体细尺度商已经用 sinc 的光滑延拓处理到尺度 0；在固定紧环带上，分母正下界、
商和弦长的任意固定阶导数界均由紧性证明。`annularCutoff` 是显式选择的 κ，
已经证明它在实际细壳层上等于 1。`distanceCap` 使用 `r₀=1/16` 的具体光滑
非递减截断，符合原文允许的选择。正反向系数、全部粗细边、重复 Lagrange 因子
及共同 taper 已在一个联合 profile 中组装；周期化与原配置乘子之间是精确等式。

Product taper 的任意非负尺度可在其相关支集上精确截断到固定紧区间。
相应统一导数界、乘以紧支集 profile 后的实际 Wiener 界都已证明。
显式 dyadic 截断非负且光滑，粗层加细层在每个正距离处形成有限分割。
距离落在 `[0,1]` 时，实际 taper 与截断的非零性推出顶点预算；粗细标签的
计数界也已经证明。任意次数符号多项式的 parity 消去和逆阶账目保留原有证明。

`LagrangeCoefficients` 使用 Lean 原生 `MvPolynomial` 定义各线性因子的乘积，
由真实系数提取构造 `c_i`；常数项的负号保留在定义中。实际有限符号平均的展开
证明零次项与基线相消，一次项的期望为零。再求和全部壳层，得到

```text
‖J_n‖_W ≤ C {1+log(1/t_n)}^(choose Q 2) Σ_{j=2}^{4Q} (t/t_n)^j
‖J_n‖_W ≤ C Λ^(choose Q 2−2B) → 0,  B > (choose Q 2+2)/2.
```

`PaperWiener` 采用全部次数 ≤ `Q−1` 的嵌入坐标单项式作为系数基；基的单射性
和完整性已证明。矩索引是所有总次数介于 1 和 `4Q` 的指数向量，没有以重复
排列的词替代矩向量。实际函数与原文矩公式的等式由 `partBIdealVector_value` 给出。
向量 Wiener 范数按原文取坐标范数之和；与正载体所用最大坐标范数之间的固定
维数因子也已明确证明。

尺度使用任意固定 `p>0` 的 `t=x^{-p}`。自然数序列采用 `x=n+1`，只是避开 `n=0`
的索引平移；`Λ=1+log x`。常数可以依赖固定基线、维数、Q 和固定尺度指数，
不依赖 n、配置或壳层标签。对角线上的实际增量为零，且其全域函数由 Wiener
元素连续实现。有限支持和矩右逆无需参与 Wiener 估计的证明。
右逆在 `paper_item_one` 中仍是参数，但 `MomentSupport.paper_positiveCarrier_small_support`
已经用实际构造消除了这一输入条件。

## 第 2 项：具体模型构造与合法性

| 模块 | 已证明的内容 |
| --- | --- |
| `MomentSupport` | 在任意小的系数最大范数球内放置有限网格；由一维 Lagrange 基系数显式构造张量矩右逆。均匀基线权重严格为正，小矩扰动由同一支撑上的正概率实现；接入实际正载体。 |
| `LagrangeInterpolation` | 原有真实系数的 0/1 插值性质、次数界、在论文全部次数 ≤ Q−1 单项式基中的精确展开；适用于任意 q≤Q。 |
| `LagrangePointwise` | 逐坐标证明 `abs(c_iκ) * P_i ≤ C(d,q)`，因而在 P_i>0 时得到 C/P_i 界；常数不依赖配置。 |
| `VirtualShift` | 实际系数扰动在观测点恰好产生 `t ζ_j`；在非零 taper 支撑上统一有 `O(t/t_n)=O(Λ^(-B))` 界并趋零。 |
| `QuadraticPartition` | 显式非负光滑紧支集 φ，φ(0)=1，平方和严格等于 1，每点最多 2^d 个非零包，共同包支撑的距离 ≤2r。 |
| `HolderScaling` | 全局迭代导数与非整数阶 Hölder 控制，缩放常数 C r^(-s)，乘积估计，以及只依赖重叠数的求和估计。 |
| `PacketProfiles` | 实际有限多项式包，物理载体坐标和内部支撑，P 与有限四次包和的统一导数界，P 的 C^s 界；常数与块数、抽样和尺度无关。 |
| `ActivePackets` | 明确有限块集合，所有遗漏包恒为零，有限模型仍保持精确平方和；实际包场公式、目标中心取值和 sup 范数界。 |
| `PacketAmplitudes` | a=c_a r^α 抵消 P 的 C^α 缩放损失；目标 ΔG_h² 的 Hölder 界，以及 Δ=h^γ 时的 C^γ 振幅抵消。 |
| `ScaleControl` | 真实迭代导数在共同尺度上的加法、乘法、振幅和 Hölder 控制；常数平移与 Bernoulli 均值的转换。 |
| `OutcomePackets` | 完整 η、K 及 P 侧交叉项的统一导数界；有限 q₄ 与无限周期和在 G_h² 权重下严格相等。 |
| `NuisanceLegality` | 同时选择固定 c_a,c_b>0；两侧 π、μ₀、τ 满足任意给定合法半径及 [κ,1−κ] 条件；中心分离量为 c_a c_b Δ。 |
| `SmallDensityCarrier` | 将真实正载体推广到任意正密度幅度 θ，与给定设计上下界兼容。 |
| `PhysicalDesign` | 自然数标签的真实物理因子；每点载体重叠数 ≤5^d；相对于单位立方体 Lebesgue 测度的归一化、可测性和两侧界。 |
| `PhysicalCarrierIntegral` | 环面 Haar 积分、单位立方体积分及真实仿射换元，证明每个物理载体上的 ∫(F_H−1)=0。 |
| `CarrierLocalization` | 所有活跃载体位于距中心 ≤5h 的区域；h 足够小时包含于观测立方体。 |
| `DiscreteProbability` | 可数载体律转换为 mathlib PMF 和概率测度；有限个可数标签的独立乘积及真实乘积权重。 |
| `DiscreteTilt` | 完整可数标签上的正倾斜，严格归一化；与测度 withDensity 的一致性、共同标签律和似然归一化因子的精确抵消。 |
| `GlobalPriors` | 真实有限块独立先验、实际设计归一化常数 Z 的 n 次方倾斜、共同标签边际和混合设计密度。 |
| `DesignExperiments` | 连续设计的概率测度及独立 n 样本；倾斜后两侧设计密度函数的分布和 Xⁿ 概率边际完全相同。 |
| `BalancedScales` | 具体幂尺度 r、h、t 满足 r≤h≤1、t≤1 和 h^γ=r^(α+β)t²，消除模型合法性中的尺度恒等式输入。 |
| `ConcreteModels` | 同一密度幅度的实际正载体与两行完整参数合法性的汇总；固定正振幅及充分大 n 的实际模型序列。 |
| `LegalBinaryModels` | 合法物理均值产生真实 Bernoulli 条件概率；单元质量严格等于倾向概率乘条件结局概率。 |
| `FiniteConditionalExperiment`、`ObservationModels` | 连续 X 与有限 (R,T) 的真实联合概率测度，可测性、X 边际及 f·L/4 密度公式。 |

网格支撑的原子数是 `(D+1)^M`，比论文证明中的最小单纯形大，但仍为只依赖固定
维数和矩阶数的有限常数。没有把多项式独立性或矩右逆作为新假设。
这里有限维函数空间使用 Lean 的最大范数；坐标点态界的有限维范数转换只改变固定常数。
`HolderControl m θ C f` 同时控制 0 到 m 阶导数及第 m 阶导数的 θ-Hölder 增量，
并且证明覆盖 `0≤θ≤1`，不是仅证明整数阶光滑性。
`quarticField` 是有限活跃块上的四次和；`weighted_quarticField_eq` 已证明它与原文
无限周期 q₄ 在乘以 G_h² 后的一致性。完整三次回归采用原文的符号和系数。
利用 abt²=c_a c_b Δ，把 d_*p 改写为带 b 因子的包场后，证明固定小振幅下的统一合法性。
所有 Hölder 常数独立于 n、活跃块数量和实际系数抽样。

可数先验没有截断标签：先在有限块上取可数标签的独立乘积，再按标签独立抽取
有限系数。其权重严格等于局部联合律权重的乘积。Zⁿ 倾斜既有真实权重实现，
也有与 mathlib `Measure.withDensity` 的一致性定理；连续的是观测设计 X。
本轮复用了 mathlib 的 PMF、有限乘积测度、Haar 测度换元和积分工具。

`paper_item_two_polynomial` 对满足 z/γ≤ξ、z>ξ(α+β) 的幂尺度给出充分大 n 的
合法性，并与 t=(n+1)^(-(z−ξ(α+β))/2) 的实际正载体连接。对论文最优速率的
具体指数选择、Q 的选择及渐近账目现已在 `RateRegime`、`RateLedgers` 中证明；
`PaperScales`、`PaperLegalFamily` 和 `PaperActualTV` 已将实际观测实验接入这些速率计算。

## 第 3 项：从实际后验到全局 minimax 下界

| 模块 | 已证明的内容 |
| --- | --- |
| `DiscreteIntegration`、`DiscreteMixture` | 对完整可数标签律交换期望与积分，构造实际有限系数混合律及其后验矩；没有截断标签。 |
| `CarrierProjectivity` | 固定同一个 Q 阶字典，在任意保留/幽灵坐标划分下证明真实密度矩的 Haar 积分投影恒等式。 |
| `CarrierMasterIdentity`、`CarrierPosteriorMoments` | 将 Banach 空间矩恒等式落实为逐点恒等式；`paper_posterior_master_moments` 直接给出实际网格支撑、正载体和 Q 点后验的全部矩差。 |
| `WeightedCarrierProjectivity` | 实际系数矩差乘密度后的幽灵积分恒等式，适用于任意有限系数函数；没有假设增量张量自身可投影。 |
| `RetainedEvaluation` | 在非零 taper 上，实际虚拟系数扰动在保留点的取值只依赖保留位置和符号；乘以 taper 的恒等式也覆盖碰撞位置。 |
| `GhostLeakage` | 真实密度加权的平均激活率在 [0,1] 内；逐点和积分后的幽灵泄漏恒等式，以及由异常集合体积控制泄漏的界。 |
| `DiscreteIndependence`、`BlockIndependence` | 实际可数块先验的乘积期望；以局部密度因子乘积倾斜后，仍是局部倾斜律的独立乘积。 |
| `DesignPosterior` | 实际样本设计似然按块因子分解；Zⁿ 倾斜与归一化密度抵消后，Bayes 后验精确等于独立块后验。 |
| `ObservationGraph` | 用实际载体包含关系构造观察图，证明不同组件使用的标签集合互不相交；连通 q 点配置位于根节点半径 4qr 的坐标立方体内。 |
| `FiniteTesting` | 有限概率律的乘积 Hellinger 次可加性、TV ≤ √H²、重叠质量恒等式及有限样本两点绝对损失界。 |
| `DensityTesting` | 任意支配测度下的真实概率律和 Le Cam 绝对损失界；风险允许为无穷大，不附加估计量风险可积假设。 |
| `CommonMarginalTesting` | 两侧共同连续设计边际下，联合 TV 等于条件 TV 的积分；异常概率加良好集合 Hellinger 代价积分平方根的界，以及随 n 改变样本空间的趋零定理。 |
| `RateRegime`、`RateLedgers` | 从 Part B 参数区间选定具体幂指数与 Q；证明单点、碰撞及大组件三个误差单项式乘任意固定对数幂后趋零。 |
| `CollisionVolume` | 真实周期截断距离的小球体积界，包含基本胞边界处的碰撞；碰撞对角线为零测集。 |
| `TailMoment`、`CollisionInverseMoment` | 复用 mathlib 的层蛋糕公式和幂函数积分，证明所有 0<s<d 的距离负 s 次幂可积，界与根位置无关。 |
| `StarCollisionVolume`、`TaperBadVolume` | 对实际距离乘积和完整图 taper 证明异常体积 ≤ Cₛ tˢ，任意 0<s<d；积分按真正的立方体乘积测度进行。 |
| `SubcriticalRates` | 证明可选择 s<d，使替换 tᵈ 为 tˢ 后的额外损失被 ε 余量吸收，两个主要误差单项式仍趋零。 |
| `PolynomialMoments`、`CarrierPolynomialMoments` | 将完整的非恒定矩匹配推广到所有次数 ≤4Q 的真实多项式，包括常数项；实际正载体后验满足该插值恒等式。 |
| `LikelihoodPolynomials`、`CarrierLikelihood` | 构造两侧实际 Bernoulli 似然的多项式，证明 q 点似然次数 ≤4q，接入实际网格系数及保留点虚拟扰动。 |
| `TorusTaper`、`CarrierMarginal` | 实际 complete-graph taper 连续下降到环面；后验重排不变，先投影带密度权重的矩差分子再除以 D_q。 |
| `EvaluatedCarrier`、`UniformEvaluatedCarrier` | `paper_uniform_evaluated_likelihood` 构造同一正 H 与核，使所有 q≤Q、全部保留点位置、两侧完整似然同时满足实际幽灵平均的激活恒等式。 |
| `TorusTaperVolume`、`ConcreteGhostLeakage` | 将立方体坏集体积界经保测映射转到环面，得到真实 taper 的带权及不带权泄漏积分上界。 |
| `PhysicalGhostLeakage` | 对实际物理载体盒作仿射换元，完整证明 Jacobian 为 (4r)^(dq)，从而得到物理泄漏积分 ≤ C r^(dq) tˢ。此处 t 可直接取实际 taper 阈值。 |
| `CarrierCounting` | 活跃载体数 ≤(7h/r)ᵈ，每个观察点涉及 ≤5ᵈ 个载体，q 个点总计涉及 ≤q·5ᵈ 个载体。 |
| `FiniteProductMixture`、`FiniteGrouping`、`FiniteProductReplacement` | 有限混合与独立乘积的交换、按任意纤维分组的期望恒等式，以及逐坐标条件期望匹配的张量化。 |
| `CoefficientIndependence` | 将真实设计后验的全部可数标签积分掉，严格得到各块实际有限系数后验的独立乘积；每块仅保留其载体内的观察点。 |
| `ComponentFactorization`、`PhysicalComponentFactorization` | 实际包场只依赖入射载体；`physical_conditional_cell_factorization` 从 Zⁿ 倾斜先验、真实设计似然和 Bernoulli 单元质量直接推出条件组件乘积分解。 |
| `FinitePushforward`、`AdditiveTensorization`、`BlockLikelihood` | 独立随机场逐块替换；载体外包函数为零使单块公式适用于整个观测似然，重叠块先相加再计算似然。 |
| `BlockActivation`、`ComponentActivation`、`PhysicalActivation` | 构造实际 Bernoulli 激活概率；同一正载体核同时给出所有配置的多块恒等式。`paper_physical_posterior_activation` 包含真实设计归一化、Zⁿ 倾斜和标签后验。 |
| `FiniteReindex`、`RetainedSignMarginal` | 证明保留符号边际、幽灵符号消去和块/观测索引交换；不同观测的虚拟符号确实独立。 |
| `FiniteRademacher`、`FinitePartialStability` | 对实际有限块索引证明一至四阶矩和完整二元似然的部分扰动误差界。 |
| `PhysicalJitterMoments`、`PhysicalPartialStability` | 物理包函数的方差、四阶矩修正 η 和目标函数严格相符；全激活精确匹配，部分激活单点似然误差 ≤6ab t²。 |
| `FiniteProductBounds`、`PhysicalFreshLikelihood`、`PhysicalRetainedLikelihood` | 任意基线实现的多点稳定性与完整保留符号似然相接；中间部分扰动函数不需要另行假设是概率密度。 |
| `PhysicalFiniteExperiment`、`EffectiveActivation` | 构造两侧真实有限条件概率律；合法性推出 q 点单元下界 κ^(2q)，未命中观测的块不贡献泄漏代价。 |
| `PhysicalLocalHellinger` | `paper_uniform_local_hellinger` 构造同一 H 与核，使所有合法物理配置满足局部 Hellinger 界；没有把部分匹配、矩恒等式或信息界作为输入。 |
| `FiniteProductMeasures`、`DesignMarginals` | 复用 mathlib 的乘积测度分解，证明任意不同观测的坐标边际；真实 Zⁿ 倾斜混合设计的 q 点边际 ≤ Cᵠ 倍 Lebesgue 测度，常数不依赖总样本量或载体核。 |
| `HighComponentGeometry`、`ClusterVolume` | 从过大的实际观察组件抽出 Q+1 个不同顶点；一个粗尺度盒与 Q 个细尺度盒的簇体积精确计算。 |
| `HighComponentProbability`、`HighComponentRates` | 构造可测异常事件，覆盖所有大组件，证明实际共同设计下概率 ≤ C n^(Q+1) hᵈ r^(dQ)，并按论文尺度趋零；H 与核可随 n 改变。 |
| `MixedGhostLeakage`、`SubsetGhostCost` | 将实际物理幽灵积分接到共同设计测度；按每个载体命中的非空观测子集枚举，得到可测、可积的实际泄漏上界和组合数计数。 |
| `GlobalGhostCost`、`GlobalGhostRates` | 证明所有活跃载体的泄漏总和由 `globalGhostCost` 控制；当 nrᵈ≤1 时积分 ≤ Cₛ n hᵈ εₙˢ，选定 s<d 后乘 δₙ² 趋零。没有把积分代价界作为假设。 |
| `ComponentHellinger`、`UniformLocalConstant` | 将真实入射组件乘积分解接到 Hellinger 次可加性，并统一全部 m≤Q 的局部信息常数。 |
| `GhostReindex`、`ComponentRestriction`、`ComponentCarrierRestriction` | 证明幽灵坐标置换、组件载体的重编号、系数后验限制，以及与局部物理配置的逐项识别。 |
| `ComponentSize`、`ComponentReindex`、`ComponentLeakage` | 非异常事件上组件大小 ≤Q；将不同大小组件改编号为 Fin m，并证明每个实际载体的泄漏恰好计入一次。 |
| `PhysicalComponentExperiments`、`PhysicalGlobalHellinger` | 同一个已构造载体给出整个样本的真实条件 Hellinger 界，由组件求和控制到 `globalGhostCost`。 |
| `ConditionalMeasurability`、`PhysicalJointComparison` | 证明完整可数标签后验及条件概率核可测；共同设计边际下的实际联合 TV ≤ 异常概率 + 代价积分平方根。 |
| `GlobalComparisonRates`、`PaperScales`、`PaperLegalFamily`、`PaperActualTV` | 选择论文尺度、固定合法振幅及正载体序列，证明实际整样本 TV 趋零。 |
| `FiniteProductDensities`、`DiscreteBayes`、`SampleDensity`、`PhysicalPriorMixture` | 用真实乘积测度与可数混合的 Bayes 公式，精确识别比较密度律和 Zⁿ 倾斜先验下的观测混合分布。 |
| `StatisticalModel`、`MixtureRisk`、`MinimaxReduction` | 定义含经典可微性的模型类和实际 minimax 风险；合法先验支持、目标分离和 Le Cam 引理给出模型上确界及估计量下确界的下界。 |
| `PaperMinimax.paper_partB_minimax` | 合并全部构造，证明任意 ε>0 的 Part B minimax 速率；最终定理不保留分析、几何、合法性或信息界作为输入。 |

这里的异常体积证明采用 `Cₛ tˢ`（s<d）路线，没有逐字形式化论文的精确临界对数界。
`exists_subcritical_rate_control` 已严格证明这一幂次损失与所需 ε 损失速率兼容。
因此这条替代证明已经推出相同的最终下界；精确临界对数界不是最终定理的输入。
向环面幽灵积分和物理载体积分的具体接口现已完成，所有常数均独立于样本量。
同一载体处理全部保留点数的量词在 `paper_uniform_evaluated_likelihood` 中显式给出，
没有为不同组件大小另选载体。组件分解的证明覆盖物理载体重叠的情况；
未被任何观测命中的载体放在一个无观测的辅助纤维中，其贡献为 1。

新局部入口的界为

```text
H²(P_q, Q_q) ≤ [4^q (C_q δ)^2 / κ^(2q)] × Σ_{k: carrierSites_k 非空} (1 − χ̄_k),
C_q = (3/2) q 2^q，δ = a b t²。
```

其中 P_q 与 Q_q 是 `finitePhysicalConditional` 构造的真实概率律，
χ̄_k 是既有幽灵积分定义的 `evaluatedBlockWeight`。
`paper_uniform_local_hellinger` 对一个固定构造的 H、核，量化所有配置及全部块；
所需的模型合法性由第二项提供，另有显式小振幅条件 a²t²≤1、ab t²≤1/2。
界对每块观测数≤Q 的配置成立，特别覆盖 q≤Q。
`PhysicalComponentExperiments` 已将它沿观察组件的重编号接入整样本条件实验；
`paper_uniform_global_hellinger` 完成组件求和，并使用已证明的实际代价界。

新增的全局积分入口是 `globalGhostCost_integral_le`。令 Eₙ 为 `largeClusterEvent`，
Lₙ 为 `globalGhostCost`，则已经证明

```text
μₙ(Eₙ) ≤ C n^(Q+1) hᵈ r^(dQ)，
∫ Lₙ dμₙ ≤ Cₛ n hᵈ εₙˢ  （0<s<d，nrᵈ≤1，0<r≤h）。
```

Eₙ 是有限个可测簇事件的并集，包含所有大小超过 Q 的实际观察组件。
Eₙ 外每个载体至多命中 Q 个观测；实际非空载体的幽灵泄漏总和逐点不超过 Lₙ。
Lₙ 的定义是对观测子集的显式有限和，不依赖随机变化的积分维数。
利用载体数 ≤(7h/r)ᵈ 和 nrᵈ≤1，将所有 1≤q≤Q 的项统一控制即可，
低阶积分部分不需要森林枚举。

`paper_largeCluster_probability_tendsto` 和 `paper_globalGhostCost_scaled_tendsto`
进一步证明按论文给定的幂尺度、对数 taper 阈值及适当的 s<d，
μₙ(Eₙ)→0 和 δₙ²∫Lₙdμₙ→0。这些结论适用于随 n 改变的真实先验和核，
常数不依赖 n；后者统一覆盖所有固定 Q 和对数幂 B。
实际全局结论 `paper_actual_totalVariation_tendsto` 由此得到

```text
TV(P̄ₙ,Q̄ₙ) ≤ μₙ(Eₙ) + √(C δₙ² ∫Lₙdμₙ) → 0。
```

载体 Hₙ 和条件系数核均由先前构造选出；同一个载体用于全部组件大小及全部配置。
`physicalComparisonDensity_eq_mixture` 将 P̄ₙ、Q̄ₙ 识别为真实先验混合，
`physicalComparison_minimax_lower` 再把 TV≤1/2 变成 δₙ/4 的 minimax 下界。
`paper_partB_minimax_small_epsilon` 完成小 ε 的具体选择，
`paper_partB_minimax` 选取 ε₀≤ε 并比较幂次，覆盖任意 ε>0。
最终结果没有 `axiom`、`sorry`，也没有把这些待证结论包装成输入假设。

## 编译和依赖

- Lean：`leanprover/lean4:v4.19.0`。
- mathlib：`c44e0c8ee63ca166450922a373c7409c5d26b00b`（`v4.19.0`）。
- 间接依赖版本记录在 `lake-manifest.json`。
- 本机便携编译器和缓存位于 `.tools/`，依赖位于 `.lake/`；这些目录不进入仓库，新机器的安装步骤见[复现说明](../docs/REPRODUCING.md)。
- Windows 构建脚本会在临时目录建立指向本项目的 ASCII 路径别名，以兼容中文路径；
  源文件保留在本项目目录，环境变量修改仅对本次脚本进程有效。

在此目录用 PowerShell 运行：

```powershell
.\Build.ps1 -Audit
```

Part B 完成时的命令返回退出码 0，输出 `Build completed successfully.`，2339 个定理/构造入口通过公理审计。
当时的完整构建与审计输出保留在本地 `verification.log`。
Part C 完成后的同一命令也返回退出码 0，5,334 个定理/构造入口通过公理审计，原始输出保留在本地 `verification-partC.log`，摘要见[验证记录](../docs/VERIFICATION.md)。
审计的入口数量包含 Lean 自动生成的
辅助定理，不等于显式 theorem 声明数量。
`Audit.lean` 扫描整个 `CausalLowerbound` 命名空间中所有定理，
以及审计列表中关键构造定义的传递公理依赖，最后输出检查入口总数。
编译器内部的擦除代码占位不作为证明入口；定理依赖的私有辅助证明仍会递归检查。
审计直接使用 Lean 的 `CollectAxioms.collect`，在所有入口之间共享已访问依赖记录，
避免反复遍历 Fourier 分析的相同依赖；检查范围和失败条件保持不变。
只允许：

```text
[propext, Classical.choice, Quot.sound]
```

这些是 Lean/mathlib 的标准基础公理。出现 `sorryAx` 或任何额外公理会使审计报错、
构建脚本失败，而不只是打印提示。本项目没有使用 `sorry`、`admit` 或 `native_decide`。
