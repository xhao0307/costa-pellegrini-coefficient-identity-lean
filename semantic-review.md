# Independent statement and semantic review

2026-10-10. **Result: semantic pass for the complete integer coefficient
identity.** This is a coordinated AI review, not an external human review,
a priority determination, or a prize-eligibility decision. The root's
separate fresh project build passed after the initial review; the
verification note below records the evidence inspected.

## Primary-source target

I directly read the published Costa–Pellegrini article's PDF text at
printed pages 483–485, and cross-checked the equations in arXiv v2 §4.1.
The published PDF defines `g_k` using the factors
`(x_j−x_i)(x_i+⋯+x_j)`, defines `F_k=g_k/(x₁+⋯+x_k)`, and specifies the
two coefficient monomials. Page 485 presents the sign relation for the
computed ranks and requests an all-rank proof. The present target is that
coefficient relation, not the surrounding rearrangement conjecture.

Sources:
[published PDF](https://d-nb.info/1221514253/34), printed pp. 483–485,
and [arXiv:2003.05939v2 §4.1](https://arxiv.org/html/2003.05939v2#S4.SS1).
The PDF's mathematical text and the arXiv TeX expressions agree on the
definitions and requested sign. No screenshot-rendering success or full
paper-wide priority search is claimed by this review.

## Exact encoding in the current Lean source

The review read the current `Definitions.lean` and `Identity.lean`, not
only a theorem-name registry or a build-success summary. Relabel Lean's
index `i : Fin k` as the paper's index `i.val+1`.

| Current declaration | Meaning under this relabeling | Assessment |
|---|---|---|
| `Poly k` | The ordinary multivariate polynomial ring over `ℤ` in exactly `k` variables | Matches the required coefficient ring; no quotient or replacement coefficient type. |
| `intervalPairs k` | All pairs of distinct ordered endpoints with the first smaller | Includes all required factors once. |
| `intervalSum a b` | The sum over the closed endpoint interval | Includes both endpoints and no outside coordinate. |
| `vandermonde k` | Product of `X b − X a` over the endpoint pairs | Orientation matches the source; it is not the opposite Vandermonde. |
| `intervalProduct k` | Product of closed-interval sums over the endpoint pairs | Multiplying by `vandermonde` gives the source polynomial, by finite-product distributivity. |
| `deletedIntervalProduct k` | The same interval product with exactly `(0,k−1)` removed | The full sum is deleted as a named polynomial factor before any substitution. |
| `cExponent k j` | Exponent `k−2` at `j`, `k−1` at every other index | Correct coefficient multi-index. |
| `eExponent k j` | Exponent `0` at `j`, `k` at every other index | Correct omitted-variable coefficient multi-index. |
| `cCoefficient`, `eCoefficient` | Actual `MvPolynomial.coeff` of the corresponding products | Neither coefficient is an abstract constant, an oracle, or an assumed identity. |

The full-factor interpretation is supported by the actual universal
theorem `intervalProduct_eq_totalSum_mul_deleted k hk`. Thus the encoded
polynomial for the c coefficient is precisely the deleted-factor version
of `F_k`. It does not evaluate a quotient at a zero of its denominator.
The total sum is a nonzero polynomial over integers, so this also agrees
with ordinary polynomial quotient notation used in the source.

`k−2` and `k−1` are natural-number subtractions. The terminal premise
`2 ≤ k` ensures these are the intended nonnegative exponents. Natural
division `(k−1)/2` is exactly the indicated floor. The index translation
is bijective onto all paper indices `1,…,k`.

## Terminal statement, scope and nonvacuity

The current terminal declaration is

```lean
theorem coefficient_identity {k : ℕ} (hk : 2 ≤ k) (j : Fin k) :
  eCoefficient k j = (-1 : ℤ) ^ ((k - 1) / 2) * cCoefficient k j
```

Its only mathematical parameters are the rank, its required lower bound,
and an arbitrary distinguished index. There is no upper bound on rank,
restriction to an endpoint index, numerical table hypothesis, coefficient
nonvanishing premise, finite-field premise, unresolved Graham assumption,
or asserted boundary identity. For every allowed rank the index type has
`k` inhabitants; the claim is not made true by using an empty index type.

This is a theorem about equality of two explicitly defined coefficients.
It remains an equality even at a rank/index where both coefficients
happen to vanish. Such possible vanishing is not a hidden logical
loophole: equality is exactly this target. It would be a gap only if one
used the equality to claim nonvanishing or a rearrangement theorem.

## Actual composition of the proof

1. `Transport.lean` supplies an arbitrary-polynomial zero-coordinate
   coefficient bridge. Its cyclic exponent reindex ranges over all
   permutations, with the full `finRotate` sign; it does not assume
   independence as an unproved coefficient statement.
2. `Annihilation.lean` proves `trace k (totalSum k * Q)=0` for every rank
   and every polynomial `Q`. Its pair involution gives actual coincident
   non-top exponent vectors and opposite signs; the top-label terms
   vanish because they exceed the balanced exponent at a coordinate.
3. `Reflection.lean` constructs a genuine permutation fixing the index,
   proves its involution and branch formulas, and derives the sign of the
   two reversed blocks from an all-rank reversal-sign proof.
4. `PrefixProduct.lean` and `IntervalBijection.lean` give a genuine segment
   permutation, the full strict-interval image, finite-product reindexing
   and the crossing cardinality. The full interval maps to the singleton
   at the distinguished index; the singleton maps back to the full
   interval. Removing or zeroing that full-interval contribution would
   have been incorrect, and the present proof retains it.
5. `Boundary.lean` proves individual factors under a ring homomorphism
   killing the total sum, applies the whole-product bijection, and then
   uses the actual quotient map by `Ideal.span {totalSum k}` to obtain an
   integer polynomial `Q`. The final existence theorem has no ring-map
   hypothesis and no missing mathematical premise. It needs no domain
   cancellation.
6. `Identity.lean` applies the trace to that genuine polynomial equality,
   uses total-sum annihilation, permutation covariance and the proven c
   coefficient shift, solves the resulting sign equation using the
   square-one property of the permutation sign, then applies the rank
   sign identities from `Signs.lean`.

The reflection's left/right block sizes are `j.val` and `k−1−j.val`.
Together with the boundary sign and transport sign, the terminal exponent
reduces to `floor((k−1)/2)` independently of the index. I found no
orientation, omitted-index, full-factor, sign, or scope mismatch in this
chain.

## Review boundaries

The listed modules have been individually strict-kernel compiled, and
the root reported the terminal module's strict compilation. This review
adds direct source/statement scrutiny; it does not replace the independent
fresh project build or the final whole-project axioms audit.

The reviewed result does not establish uniform coefficient content,
nonvanishing modulo every relevant prime, an ordering for every subset,
Graham #475, Alspach's conjecture, novelty, world-first priority, a catalog
identifier, or reward eligibility. Those are separate obligations. I
authored several supporting modules, so this is a second composition and
semantic check within the same coordinated AI effort, not a disjoint
external peer review.

## Post-review verification note

I subsequently read `verification.json`, its actual
`final-audit.log`, the current `lakefile.toml`, and `lean-toolchain`. The
receipt records the successful fresh build of all ten proof modules and
Audit from an initially absent project build directory, while reusing the
nine pinned upstream packages. This is not a fresh rebuild of third-party
sources. The project configuration lists all ten reviewed modules as
roots and supplies warning-as-error and kernel-checking flags.

The audit's recorded exit code is zero. Its actual output prints the
unrestricted terminal theorem and the concrete coefficient definitions;
the terminal theorem and four principal proof bridges depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Every current reviewed
proof-module source hash agrees with both this review's initial snapshot
and the parent verification receipt. The completed fresh build therefore
covers the same statement and source reviewed above. I did not rerun or
take over the parent's build session.
