# Clifford+T Universality in Lean

This repository contains one proof project: distance-independent approximate
universality of the Clifford+T quantum gate set. It is extracted from the
original `two-control-lean` development together with the exact synthesis and
`{H,T}` density machinery required by the proof.

## Top 100 Quantum Theorems

[![Lean Action CI](https://github.com/AbdullahAlmanei/clifford-universality-lean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/AbdullahAlmanei/clifford-universality-lean/actions/workflows/lean_action_ci.yml)

This repository resolves **#41, "Universality of sets of two-qubit quantum
gates,"** in Marco David and Jens Palsberg's
[Top 100 Quantum Theorems](https://marcodavid.net/top100/) by proving
approximate universality of the finite Clifford+T gate set.

The exact exported statement is
[`TwoControl.Top100.clifford_t_is_an_approximately_universal_quantum_gate_set`](https://github.com/AbdullahAlmanei/clifford-universality-lean/blob/master/TwoControl/Top100.lean#L17-L25).

## Headline theorem

**Clifford+T approximates every finite-qubit unitary operation arbitrarily
well for every projective distance measure that satisfies the stated laws.**

```lean
theorem clifford_t_is_an_approximately_universal_quantum_gate_set {n : ℕ}
    (d : ProjectiveDistanceMeasure (2 ^ n))
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
        d U (circuitMatrix gates) < ε
```

The circuit uses only embedded CNOT, Hadamard, and `T` gates. The result does
not select a formula for distance.

## Four distance properties

A projective distance measure maps pairs of unitary matrices to nonnegative
real numbers and has four properties. Write
`E_A(t) = exp(i * t * π * A)`.

- **Reflexivity.** `d U U = 0`.
- **Consistency.** If `U₁ ∼ U₂` and `V₁ ∼ V₂`, then
  `d U₁ V₁ = d U₂ V₂`.
- **Subadditivity.** `d (U₁ * U₂) (V₁ * V₂)` is at most
  `d U₁ V₁ + d U₂ V₂`.
- **Continuity.** For every `ε > 0`, real `t₀`, and Hermitian `A`, there is a
  `δ > 0` such that `|t₀ - t| < δ` implies
  `d (E_A(t₀)) (E_A(t)) < ε`.

Projective Hilbert--Schmidt distance is one verified instance. Its instance
proof gives the corollary
`TwoControl.Top100.clifford_t_is_an_approximately_universal_quantum_gate_set_hs`.

## Proof path

```text
exact Clifford+Rz synthesis
  -> S = T^2 and S^dagger = T^6
  -> H,T approximation of each Rz under the distance laws
  -> circuit error accumulation by multiplicative subadditivity
  -> distance-independent Clifford+T universality
```

## Source map

- `TwoControl/Clifford/Universal/ProjectiveDistance.lean` defines the four
  distance laws and their transport through gate embeddings.
- `TwoControl/Clifford/Lemma12/G1G2/ProjectiveRzApprox.lean` proves
  distance-independent `{H,T}` approximation of `Rz`.
- `TwoControl/Clifford/Universal/ProjectiveRzApproximation.lean` embeds the
  one-qubit result into an arbitrary finite register.
- `TwoControl/Clifford/Universal/ProjectiveMainTheorem.lean` replaces all
  `Rz` gates and proves the generic universality theorem.
- `TwoControl/Clifford/Universal/Distance.lean` proves that projective
  Hilbert--Schmidt distance satisfies the abstract laws.

## References

- Michael A. Nielsen and Isaac L. Chuang, *Quantum Computation and Quantum
  Information*, Cambridge University Press, 2000.
- G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*,
  sixth edition, Oxford University Press, 2008.
- Bo-Ying Wang and Fuzhen Zhang,
  [*A Trace Inequality for Unitary Matrices*](https://doi.org/10.1080/00029890.1994.11996973),
  *American Mathematical Monthly* 101(5):453--455, 1994.
- C. C. Paige and M. Wei,
  [*History and Generality of the CS Decomposition*](https://doi.org/10.1016/0024-3795(94)90446-4),
  *Linear Algebra and its Applications* 208--209:303--326, 1994.
- Mikko Möttönen, Juha J. Vartiainen, Ville Bergholm, and Martti M. Salomaa,
  [*Quantum Circuits for General Multiqubit Gates*](https://doi.org/10.1103/PhysRevLett.93.130502),
  *Physical Review Letters* 93:130502, 2004.
- Ville Bergholm, Juha J. Vartiainen, Mikko Möttönen, and Martti M. Salomaa,
  [*Quantum Circuits with Uniformly Controlled One-Qubit Gates*](https://doi.org/10.1103/PhysRevA.71.052330),
  *Physical Review A* 71:052330, 2005.

## Documentation

- [GitHub Pages](https://abdullahalmanei.github.io/clifford-universality-lean/)
- [Interactive blueprint](https://abdullahalmanei.github.io/clifford-universality-lean/blueprint/)
- [Dependency graph](https://abdullahalmanei.github.io/clifford-universality-lean/blueprint/dep_graph_document.html)
- [Lean API documentation](https://abdullahalmanei.github.io/clifford-universality-lean/docs/)

## Build and verify

```bash
lake build
lake exe checkdecls blueprint/lean_decls
lake build TwoControl:docs
```

The linked Lean CI workflow runs both checks on every push and pull request.
