# Final review — R260402 / WCL2026-2945 supplement

**Verdict: both requested targets hold. No mathematically meaningful gap.**

This is a read-only audit of the two supplement targets below. It does not certify the rest of the accepted paper. Sources were not modified and were not recompiled here. The coordinator’s recorded Lean 4.31.0 / mathlib `fabf563a` run is what the evidence files already show: `evidence/full_build.log` ends in “Build completed successfully (8563 jobs)” with exit code 0, and `evidence/axiom_audit.log` / `evidence/verification.json` give axiom-audit exit code 0. Every audited declaration in these two files depends only on `propext`, `Classical.choice`, and `Quot.sound`. There is no `sorry` and no `sorryAx` in the project sources. The bytes reviewed match the audit record:

| File | SHA-256 |
| --- | --- |
| `R260402QuorumLimit.lean` | `15a0c4d770378746a75b92f022eacc616a422410d4fe8821e37dcffbd30eec33` |
| `R260402Geometry.lean` | `573d1fb7c23235fb407355837e1bdc7de8ea4ff9a4bd1974d9974330f448630b` |
| `accepted_reference.tex` | `52492e4f0fea79b186978c7e14c67bdee9dadc8ba4323367c51a2a3bf2a57bd7` |

Compared statements: Proposition (Finite-Node Quorum), display (eq:Pq), and Theorem (Downlink Success Boundary) with `F` in (eq:dl_boundary) and `\rho_i` as in (eq:sinr_dl). Probability-space derivation of the binomial law, polar-area integration, the even-`\gamma` degree bound, simulations, and full Raft safety were left out of scope, as requested.

## 1. Quorum asymptotics — met

`quorumProb n p` is exactly the paper’s sum. `Ico (n / 2) n` is `k = ⌊n/2⌋, …, n-1` because `Nat` division is floor division, and each term is `\binom{n-1}{k} p^k (1-p)^{n-1-k}`. That is `n-1` Bernoulli trials and follower threshold `⌊n/2⌋`, matching the leader-counts-itself rule in the text and in (eq:Pq).

`quorumProb_tendsto` is the full limit: for every `p ∈ [0,1]`,

- `p < 1/2` gives limit `0`, including `p = 0`;
- `p = 1/2` gives limit `1/2`;
- `p > 1/2` gives limit `1`, including `p = 1`.

Both parities are proved and then glued by `tendsto_of_even_odd`, so the limit is along every `n → ∞`, not along one subsequence. At exact half the finite identities are stronger than the limit: for `m ≥ 1`, `quorumProb (2m) (1/2) = 1/2`, and

`quorumProb (2m+1) (1/2) = 1/2 + \binom{2m}{m} / (2 · 4^m)`,

with absolute error at most `1 / (2 √(2m+1))`.

The argument does not assume a law of large numbers, a central-limit theorem, or the limit it proves. Off half it is an explicit multiplicative tilt `r = (1-p)/p ≥ 1`, reduced by the binomial theorem to the closed forms `2p (4p(1-p))^{m-1}` (even) and `(4p(1-p))^m` (odd). The hypothesis `4p(1-p) < 1` for `p ≠ 1/2` is proved from `(1-2p)^2 > 0`. The case `p = 0` never divides by `p`: for `n ≥ 2` every index in the sum is positive, so the sum is identically `0`. The case `p = 1` is the complement of that vanishing tail; on odd `n` the extra central mass `\binom{2m}{m}(p(1-p))^m` tends to `0` by comparison with `(4p(1-p))^m`. At half, even `n` is symmetry (`P(p)+P(1-p) = 1` with no central overlap), and odd `n` is that identity plus the central term. The bound `\binom{2m}{m}/4^m ≤ 1/√(2m+1)` is an induction on Pascal’s recurrence inside this file. Library facts used for the decay (`(x+y)^N`, `\binom{2m}{m} ≤ 4^m`, `r^m → 0` for `0 ≤ r < 1`) do not encode the quorum trichotomy. Small checks agree with the odd-half formula: `n = 1,3,5` give `1`, `3/4`, `11/16`.

## 2. Multi-jammer ray decomposition — met

`Config` is an arbitrary finite jammer family: real coordinates `(u_i,v_i)`, real `γ > 2`, `β > 0`, `R > 0`, and `u_i^2 + v_i^2 > 0` for every `i`. No distinct-distance, non-collinearity, or integer-exponent hypothesis is used. Collinear jammers, repeated locations, and jammers off the segment `(0,R]` are allowed. `ofPolar` sends any paper configuration `d_i > 0`, angles `φ_i`, and ray angle `θ` to such a `Config`.

The four analytic ingredients are proved for this field, not assumed as side conditions on `finite_ray_roots`:

- **Real analyticity.** On `regular = {r > 0 : squared distance to every jammer is positive}`, `r^{-γ}` and `q^{-γ/2}` are `exp(log(·) · exponent)`, hence analytic for every real exponent. Squared distance is a polynomial. `field` is therefore analytic on the paper’s domain `(0,R]` minus on-ray jammer radii. This covers non-integer `γ`, including `γ = 2.5`.
- **Endpoint divergence.** As `r → 0^+`, `r^{-γ} → +∞` while interference tends to the finite value at the origin, because every jammer is off the origin. As `r → a` from either side through a point where some jammer has squared distance `0` and `a > 0`, that jammer’s term tends to `+∞`, the other terms are nonnegative, `β > 0`, and `field → -∞`.
- **Finitely many zeros.** `finite_ray_roots` takes only a `Config`. Each regular component is an open interval whose left end is `0` or a pole. Left-end divergence supplies a point where `field` is nonzero, so the identity theorem makes zeros isolated on that component. Poles are a finite image of `ι`. Local exclusion on the compact interval `[0,R]` (at `0`, at poles, and at regular points) makes the zero set in the domain finite. Finiteness is the conclusion, not an input. Nothing in the chain restricts the jammer coordinates to a generic open set.
- **Finite union of intervals.** Cut points are `0`, `R`, the poles, and those zeros. Each success point lies in a cut-free open cell or is a successful cut. A continuous function with no zero on an interval keeps the sign it has at one point, so each such cell lies in `success`. `success_eq_finite_relatively_closed_intervals` rewrites the same set as a finite union of order-connected pieces `closure(J) ∩ domain`. `closedIntervalFamily_properties` shows each piece is closed in the subspace topology of `domain`.

**Relative closedness is the right statement.** `domain = (0,R] \ poles`, so the origin is excluded. The piece that starts at the origin is of the form `(0,a]` when the far end lies in the domain. An ambient closed interval is not claimed, and is not required: `success_relatively_closed` is closedness of `{field ≥ 0}` inside `domain`.

**Bridges.** `sqDist_ofPolar` is the paper’s law of cosines `r^2 + d_i^2 - 2 r d_i cos(θ-φ_i)`. `field_sqrt_formula` is `√q ^{-γ} = q^{-γ/2}` for `q ≥ 0`, which is the classical identity wherever `q > 0`, i.e. on the whole domain used for success. For nonempty `ι` and `r` regular, `field_nonneg_iff_sinr` is exactly `\overline{SINR}_D ≥ β`: the interference sum is positive because every term is positive. `interior_boundary_is_root` says that a frontier point which is regular and strictly inside the disk is a zero of `field`. That is the paper’s “interior endpoint” claim. A jammer on the ray is a pole, hence outside `domain`, and is not asserted to be a root. The deployment endpoint `r = R` is not forced to be a root.

## Genuine gaps

None in the two targets above.
