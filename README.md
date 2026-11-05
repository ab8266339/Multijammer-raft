# Multijammer-raft

Lean and other proofs for **Raft-Based Wireless Blockchain Networks in the Presence of Multiple Malicious Jammers**, by Hao Xu, Yinuo Liu, and Yan Liu, accepted in **IEEE Wireless Communications Letters (IEEE WCL)** (manuscript ID **WCL2026-2945**).

## Lean proof supplement

The [Lean project in proofs/lean/](proofs/lean/) is an **independent, machine-checked proof supplement to our accepted paper**. It provides formal proofs for selected mathematical results in the paper, with a precise treatment of the limiting and boundary cases. This supplementary research does not modify or replace the accepted manuscript.

本仓库的 [Lean 工程](proofs/lean/) 是我们已录用文章的独立数学证明补充，补齐完整渐近极限与多干扰源解析分解；录用稿保持不变。[中文证明说明与复现指南](proofs/lean/README.md)

The supplement includes:

- **The full quorum limit.** For the paper's exact binomial upper sum with n−1 followers and threshold floor(n/2), the commit probability converges to 0, 1/2, or 1 according as p is below, equal to, or above 1/2. The theorem covers every p in [0,1] and both parities of n, including the endpoints p=0 and p=1. The proof also gives explicit tail bounds and the finite odd-node correction at p=1/2.
- **General multi-jammer ray decomposition.** For arbitrary finite jammer configurations away from the leader, real path-loss exponent γ>2, and positive threshold and deployment radius, the proofs establish real analyticity, endpoint divergence, finitely many ray roots, and an exact finite interval decomposition of the success set. Closedness is relative to the domain with the origin and jammer singularities removed. Interior boundary points are proved to be roots of the analytic field.
- **Earlier supporting results.** The package retains the uplink critical-radius, quorum-threshold, single-jammer geometry, power-allocation, and binomial-symmetry results, including the β=1 line case.

## Reproduce the proofs

The toolchain is pinned to **Lean 4.31.0** and mathlib commit **fabf563a7c95a166b8d7b6efca11c8b4dc9d911f**. After installing [elan](https://github.com/leanprover/elan), run:

~~~sh
cd proofs/lean
lake exe cache get
lake build
lake env lean AxiomAudit.lean
~~~

The default Lake target imports all four proof modules. Verification on DESKTOP-BRJD313 completed on 2026-11-06 (user timezone Asia/Shanghai): **98 named theorems/lemmas and 112 audited declarations**, with build and axiom-audit exit codes both zero. Every audited declaration depends only on a subset of Lean's standard axioms propext, Classical.choice, and Quot.sound. No sorry, custom axioms, or native_decide are used.

See the [verification record](proofs/lean/evidence/verification.json), [build log](proofs/lean/evidence/full_build.log), [axiom audit](proofs/lean/evidence/axiom_audit.log), and [source checksums](proofs/lean/SHA256SUMS.json). Grok 4.7 contributed the quorum proof implementation and a final mathematical review; Codex completed the remaining compiler fixes, implemented the geometry module, and independently verified the integrated project. The [review](proofs/lean/evidence/grok_final_review.md) and [provenance](proofs/lean/evidence/grok_provenance.json) document these roles.

## Scope

This is a proof supplement for the stated mathematical claims. It does not claim a formal verification of the complete Raft protocol or of the paper's experiments. Deriving the binomial distribution from a probability-space model, the measure-theoretic area integral, the polynomial-degree specializations, and Rayleigh-outage probability derivations remain outside this artifact's scope. The [detailed coverage guide](proofs/lean/README.md) maps the paper's claims to the Lean declarations.
