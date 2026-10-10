# A direct integer proof of the all-index coefficient identity

2026-10-10. This proof uses polynomial coefficients, the signed
Vandermonde expansion, and one elementary specialization. It uses no
complex numbers, roots of unity, interpolation grids, factorial division,
or quotient by a Vandermonde polynomial. It proves the coefficient identity
only; it does not prove coefficient nonvanishing or Graham #475. No
publication priority or award claim is asserted. The accompanying Lean
project proves the complete universal identity.

## Statement and notation

Fix an integer k ≥ 2, let N = binomial(k,2), and work in
Z[x_1,...,x_k]. Put

    T = x_1+...+x_k,
    V = product_{i<r}(x_r−x_i),
    H = product_{1≤i<r≤k}(x_i+...+x_r),
    h = product_{1≤i<r≤k, (i,r)≠(1,k)}(x_i+...+x_r).

Thus H = T h, deg H = deg V = N, and deg h = N−1. Define

    c_{k,j} = [x_j^{k−2} product_{i≠j} x_i^{k−1}] Vh,
    e_{k,j} = [product_{i≠j} x_i^k] VH.

The omitted coordinate in the e monomial has exponent zero. Let Z_j
replace x_j by zero. Let

    M = product_i x_i^{k−1},       D(P) = [M](VP).

D is simply a coefficient functional. In particular

    c_{k,j} = D(x_j h).                                      (1)

**Theorem.** For every k ≥ 2 and 1 ≤ j ≤ k,

    e_{k,j} = (−1)^{binomial(k−1,2)} c_{k,j}
            = (−1)^{floor((k−1)/2)} c_{k,j}.

All arguments below are finite integer identities. The established equality
can consequently be reduced modulo any characteristic.

## Lemma 1: permutations and the total-sum factor

For a variable permutation sigma,

    D(P ∘ sigma) = sign(sigma) D(P).                          (2)

Indeed, M is invariant under the permutation, while V transforms by its
sign. Apply the inverse permutation to the product whose M coefficient
is being extracted. No averaging or division by k! is used.

Moreover, for every polynomial Q,

    D(TQ) = 0.                                              (3)

Here is a direct signed involution proving (3), independently of any
alternation/divided-difference quotient. By linearity it is enough to take
Q = product_i x_i^{a_i}. Expand

    V = sum_r sign(r) product_i x_i^{r_i},

where r ranges over permutations of the exponent labels 0,...,k−1.
A contribution to D(TQ) is a pair (r,i), selecting x_i from T, such that

    r_t+a_t+delta_{t,i} = k−1 for every t.

At the selected index, nonnegativity of a_i implies r_i ≤ k−2. There is
a unique index l ≠ i with r_l = r_i+1. Swap r_i and r_l, and select x_l
from T instead. At i the increase of the Vandermonde exponent replaces
the lost x_i; at l its decrease replaces the newly selected x_l. Every
total exponent is unchanged. The transposition reverses sign(r).

This operation is fixed-point-free and is an involution: at the newly
selected l the exponent is the old r_i, whose successor occurs at i.
The contributing terms therefore cancel in pairs. Terms of Q whose degree
is not N−1 cannot contribute in the first place; no degree hypothesis on
Q is needed for the displayed identity.

## Lemma 2: a zero-coordinate coefficient is a balanced trace

For any polynomial P independent of x_j,

    [product_{i≠j} x_i^k] V(Z_j x) P
       = (−1)^{k−1} D(P).                                  (4)

In D(P), independence of x_j forces the Vandermonde exponent r_j to be
k−1. In V(Z_j x), only Vandermonde terms with exponent zero at j survive.
Map the exponent labels by the cycle

    0 ↦ 1 ↦ ... ↦ k−1 ↦ 0.

This sends each term of the first kind bijectively to a term of the second
kind, with sign multiplied by (−1)^{k−1}. For i ≠ j, its new exponent is
r_i+1. The required exponent from P is therefore

    k−(r_i+1) = k−1−r_i,

exactly the exponent required in D(P). This proves (4), including its sign.
No numerical specialization is involved.

Taking P = H(Z_j x) and using the exponent-zero interpretation of e gives

    e_{k,j} = (−1)^{k−1} D(H(Z_j x)).                       (5)

## Lemma 3: the two-block boundary identity

Let rho_j reverse both blocks beside x_j and fix x_j. Its sign is

    alpha = (−1)^[binomial(j−1,2)+binomial(k−j,2)].

Put beta = (−1)^[k−1+(j−1)(k−j)]. Then

    H(Z_j rho_j x) − beta x_j h(x) is divisible by T.       (6)

Here is a direct factor proof in the commutative quotient by (T),
with no integral-domain cancellation. Use zero-based indices 0,...,k−1
and distinguished index d=j−1 for this proof. Write y=Z_d rho_d x.
For an inclusive interval [a,b], its sum is mapped as follows:

    b<d:       sum x[d−1−b,...,d−1−a],
    a>d:       sum x[k+d−b,...,k+d−a],
    a≤d≤b:    −sum x[d−a,...,k+d−b−1].

The crossing formula follows because the reflected left and right tails
and the complementary displayed interval partition all original indices;
their total sum is zero in this quotient. The formulas define an
involution on inclusive nonempty intervals. The full interval [0,k−1]
and singleton [d,d] are swapped. All other singletons remain singletons,
and all other strict intervals remain strict intervals.

Thus the strict interval factors of H(y) correspond bijectively to the
factors of h together with x_d. Exactly the crossing strict intervals
contribute minus signs. Their count is

    (d+1)(k−d)−1 = k−1+d(k−1−d),

which gives beta. Taking their products proves the equality in the
quotient. Its kernel is the principal ideal generated by T, so the
difference in (6) equals T times an integer polynomial. This argument
covers both endpoints and every interior index, including k=2.

## Finish the proof

Let P = H(Z_j x). The operations rho_j and Z_j commute. From (2),

    D(H(Z_j rho_j x)) = alpha D(P).

From (6) and (3),

    D(H(Z_j rho_j x)) = beta D(x_j h) = beta c_{k,j}.

Since alpha = ±1, (5) now gives

    e_{k,j} = (−1)^{k−1} alpha beta c_{k,j}.

Put u = j−1 and v = k−j. The exponent of the resulting sign is

    (k−1) + binomial(u,2)+binomial(v,2) + (k−1)+uv
      ≡ binomial(u+v,2) = binomial(k−1,2) mod 2.

For n = 2r or 2r+1, binomial(n,2) has the same parity as r = floor(n/2).
This proves both displayed forms of the theorem for all k ≥ 2 and every
distinguished index j. ∎

## Formal verification and scope

The accompanying [Identity.lean](Identity.lean) proves exactly this
universal integer coefficient identity. Its exact coefficient definitions
are in [Definitions.lean](Definitions.lean). [Boundary.lean](Boundary.lean)
uses the interval involution above; [Annihilation.lean](Annihilation.lean)
formalizes the signed pair cancellation in Lemma 1, and
[Transport.lean](Transport.lean) formalizes Lemma 2.

The ten proof modules and Audit were freshly rebuilt with warnings as
errors and kernel type checking enabled. The final theorem depends only
on the standard axioms propext, Classical.choice, and Quot.sound. See
[the verification receipt](verification.json).

The theorem gives no all-rank content or nonvanishing result and does not
settle Graham475. Literature priority and acceptance as an independent
prize problem remain unresolved. The published source of the question is
[Costa–Pellegrini2020, Section4.1 p485](https://doi.org/10.1007/s00013-020-01507-7).
