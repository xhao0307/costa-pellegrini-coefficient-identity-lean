# Costa–Pellegrini coefficient identity

An integer mathematical proof and a complete Lean proof of the all-index
coefficient identity discussed in Costa and Pellegrini, *Some new results
about a conjecture by Brian Alspach*, Archiv der Mathematik 115 (2020),
479–488, Section 4.1, p. 485.
[Original publication](https://doi.org/10.1007/s00013-020-01507-7).

For every integer `k ≥ 2` and every `1 ≤ j ≤ k`, the project proves

$$e_{k,j}=(-1)^{\lfloor(k-1)/2\rfloor}c_{k,j}.$$

Here `V = ∏ᵢ<ᵣ (xᵣ−xᵢ)`, `H = ∏ᵢ<ᵣ (xᵢ+⋯+xᵣ)`, and `h` deletes the
single full-interval factor from `H`. The coefficient `c` comes from `V*h`
with exponent `k−2` at `j` and `k−1` elsewhere; `e` comes from `V*H` with
exponent zero at `j` and `k` elsewhere. [Definitions.lean](Definitions.lean)
uses integer multivariate polynomials and zero-based `Fin k` indices.

The terminal theorem is
[CostaPellegrini.coefficient_identity](Identity.lean):

```lean
theorem coefficient_identity {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
    eCoefficient k j = (-1 : ℤ) ^ ((k - 1) / 2) * cCoefficient k j
```

It covers all ranks and all indices, with no nonvanishing, rearrangement,
boundary-identity, or finite-computation premise. The accompanying
[integer proof](proof.md) uses signed exponent permutations and an interval
involution; [LaTeX source](coefficient-identity.tex) is also provided.

## Reproduce

Lean is pinned to `leanprover/lean4:v4.34.1`, and Mathlib to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Nine dependency packages are
locked in [lake-manifest.json](lake-manifest.json).

With the pinned Lean toolchain installed, run from this directory:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake exe cache get Mathlib.Algebra.BigOperators.Intervals Mathlib.Algebra.MvPolynomial.CommRing Mathlib.Algebra.MvPolynomial.Rename Mathlib.Data.Fin.Rev Mathlib.Data.Nat.Choose.Basic Mathlib.GroupTheory.Perm.Fin Mathlib.LinearAlgebra.Vandermonde Mathlib.RingTheory.Ideal.Quotient.Defs Mathlib.Tactic.Ring
lake build CostaPellegriniIdentity Audit
lake env lean -DwarningAsError=true -Ddebug.skipKernelTC=false Audit.lean
```

[Audit.lean](Audit.lean) prints the exact terminal statement, coefficient
definitions, and transitive axioms. The terminal theorem and principal
bridges depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The project has no `sorry`, `admit`, custom mathematical axioms,
`native_decide`, or disabled kernel checking in its proof chain.

The ten proof modules and Audit were rebuilt from an absent own Lake build
tree; the build and final audit exited zero. Pinned upstream dependency
artifacts were reused. A complete fresh compilation of every third-party
dependency or an external human referee review is not claimed.
See [verification](verification.json) and
[actual audit output](final-audit.log).

## Scope and attribution

This completely answers the specific published coefficient-identity
question. It does not prove that the coefficient vector is nonzero modulo
every relevant prime, and it does not settle Graham's rearrangement
conjecture or the complete original scope of JSP-000387.

No standalone JSP entry, prize eligibility, award amount, worldwide
first-priority finding, or recipient designation is established.
Earlier full proofs were not located in a bounded literature check;
that observation does not prove their absence.

The human requester initiated and directed this project. OpenAI Codex
developed the mathematical arguments and Lean scripts, with coordinated
AI reviews. The submitting project account is `xhao0307`; repository
ownership alone is not claimed as evidence of exclusive manual authorship
or award attribution. Costa and Pellegrini are credited for the published
question and coefficient families. The mathematical proof here is
presented for review with its AI provenance disclosed.

The original-publication correspondence and final statement were
separately checked against the published PDF pp. 483–485 and arXiv v2
Section 4.1. See [semantic review](semantic-review.md).
