import CausalLowerbound.UpperBound.SplitSample
import CausalLowerbound.UpperBound.FrechetTaylor
import CausalLowerbound.UpperBound.InterpolationWeights
import CausalLowerbound.UpperBound.RiskReduction
import CausalLowerbound.UpperBound.Rates
import CausalLowerbound.UpperBound.ObservedStencil
import CausalLowerbound.UpperBound.MixedClusterVolume
import CausalLowerbound.UpperBound.WeightedGram
import CausalLowerbound.UpperBound.RealOutcomeMoments
import CausalLowerbound.UpperBound.ProjectionMoment
import CausalLowerbound.UpperBound.ConditionalScore
import CausalLowerbound.UpperBound.AcceptedVolume
import CausalLowerbound.UpperBound.KernelPi
import CausalLowerbound.UpperBound.TupleLaw
import CausalLowerbound.UpperBound.ConditionalScoreMoment
import CausalLowerbound.UpperBound.AcceptanceProbability
import CausalLowerbound.UpperBound.EmpiricalStatistics

import CausalLowerbound.UpperBound.PaperUpperBound

/-!
# Density-free two-scale upper bound

Source: `rho_ts_upper_bound.pdf`, supplied by the user.

The main result is `paper_upper_bound`. For arbitrary positive smoothness
alpha, beta, gamma, it constructs a measurable estimator on the original n iid
observations and gives a uniform mean absolute error bound C n^(-rho).
The estimator, C and the eventual sample-size threshold are chosen before the
model and target. Targets range over the entire closed cube.

`upperRateExponent` uses s = (alpha + beta)/2 and
s1 = (min alpha 1 + min beta 1)/2. Below the threshold
s* = d gamma / (2 (2 gamma + d)), rho is
2 (s + s1) / (d + 4 s1 + 2 d s1 / gamma).
At and above the threshold, rho is gamma / (2 gamma + d).
`upperRateExponent_low_large_nuisance` gives the advertised simplification
(alpha + beta + 2) / (d + 4 + 2 d / gamma) when alpha, beta >= 1.

The model is `RealOutcomeModel`: a bounded measurable design density, binary
A, real Y, the conditional first-moment identities for CATE, overlap, and a
conditional second moment. Only E[Y^2 | X] <= M2 is used; the paper's stronger
armwise second-moment assumption implies this. Density derivatives, bounded
outcomes, fourth moments and nuisance estimators are not required.
`PaperRegularity` uses a fixed open neighborhood of the cube and exactly
q = ceil(a)-1, theta = a-q. Positive integer smoothness m therefore uses
m-1 continuous derivatives and a Lipschitz top derivative.

Key proved parts of the construction:

* `stencilTaylorCoefficients` and `acceptedStencil_taylor_error` provide the
  actual coefficient vector, its uniform norm bound and the local remainder.
* `stencilPopulationResidual_bias` identifies and bounds the actual bias.
* `acceptedStencil_anchor_integral`, `stencilLeadingGram_quadratic_lower` and
  `stencilPopulationMatrix_perturbation` prove population coercivity while
  preserving the treatment-variance weight's dependence on the entire tuple.
* `empiricalStencilResponse_meanSquare_le` and
  `empiricalStencilMatrix_meanSquare_le` sum all nonempty overlap patterns and
  give the vector/operator bounds from the conditional second moment alone.
* `empiricalStencilEstimate_measurable` proves measurability of the actual
  truncated inverse; `balancedSample_measurePreserving` embeds disjoint role
  groups into the original n observations, including unused leftovers.
* `sampleStencilEstimate_risk_bound` is the quantitative finite-sample squared
  and absolute risk bound, with explicit numerical bandwidth conditions.
* `sqrt_stencilMseEnvelope_le_master`, `BandwidthAdmissibility`,
  `PolynomialRisk` and `RateChoice` discharge these conditions and identify
  both final rates. None remain as assumptions in `paper_upper_bound`.

Construction choice: the auxiliary polynomial space has coordinate degree
at most p and (p+1)^d auxiliary nodes, plus an anchor and partner. It contains
the required Taylor polynomials. This is a fixed larger stencil than the
paper's total-degree stencil; its size enters only the constants. Equal role
groups have floor(n/M) observations. The high branch can use ell = r, because
the proved variation estimate only needs ell <= r and ell/h tending to zero.

These are upper rates, not a matching minimax lower-bound claim. All proofs
are kernel checked; the project axiom audit covers their transitive dependencies.
-/
