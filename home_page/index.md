---
usemathjax: true
---

# Distance-Independent Clifford+T Universality

**Clifford+T approximates every finite-qubit unitary operation arbitrarily
well for every projective distance measure that satisfies the stated laws.**

Useful links:

* [Blueprint](blueprint/)
* [Blueprint PDF](blueprint.pdf)
* [Dependency graph](blueprint/dep_graph_document.html)
* [Lean API documentation](docs/)
* [GitHub repository](https://github.com/AbdullahAlmanei/clifford-universality-lean)

## Main theorem

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

The circuit uses only embedded CNOT, Hadamard, and $T$ gates. The proof does
not select a formula for distance.

## Four distance properties

A projective distance measure maps pairs of unitary matrices to nonnegative
real numbers and has four properties. Write
$E_A(t) = \exp(i t \pi A)$.

* **Reflexivity.** `d U U = 0`.
* **Consistency.** If `U₁ ∼ U₂` and `V₁ ∼ V₂`, then
  `d U₁ V₁ = d U₂ V₂`.
* **Subadditivity.** `d (U₁ * U₂) (V₁ * V₂)` is at most
  `d U₁ V₁ + d U₂ V₂`.
* **Continuity.** For every `ε > 0`, real `t₀`, and Hermitian `A`, there is a
  `δ > 0` such that `|t₀ - t| < δ` implies
  `d (E_A(t₀)) (E_A(t)) < ε`.

Projective Hilbert--Schmidt distance is a verified instance. It gives the
derived theorem
`TwoControl.Top100.clifford_t_is_an_approximately_universal_quantum_gate_set_hs`.
