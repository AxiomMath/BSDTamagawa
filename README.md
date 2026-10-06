[![](logo.svg)](https://axiommath.ai/)

# Local Factors in the BSD Conjecture: A Unified Statistical View

This is a Lean formalization of the statistics of local Tamagawa numbers and reduction types of the elliptic curves `y² = x³ + a₄x + a₆` over `ℚ`, ordered by height.

## Main Results

* The multivariable generating function of the local data tends to an absolutely convergent Euler product.
* The joint law of the reduction-type counts `ω_K` exists, with an Euler-product generating function.
* The mean and variance of `ω_K` are explicit convergent series.
* The covariance of `ω_K` and `ω_{K'}` is an explicit convergent series.
* The law of the Tamagawa prime count `ω_Tam` exists, with an Euler-product generating function, mean and variance.
* The densities of `ω_Tam = r` in closed form.
* The mean of `v_ℓ(Tam(E))` is an explicit convergent series.
* The joint law of `(v_ℓ(Tam(E)))_{ℓ ∈ Π}` exists, with an Euler-product generating function.
* The density of `Tam(E)` coprime to a finite set of primes is an Euler product.
* The density of `ℓ ∣ Tam(E)` is one minus an Euler product.
* The density of odd `Tam(E)` is an Euler product.
* The joint generating function of `(ω_Tam, Tam)` is an Euler product.
* The law of `Ω(Tam(E))` exists, with an Euler-product generating function.
* The mean of `Ω(Tam(E))` is an explicit convergent series.
* The mean of `ω_Tam` is at most the mean of `Ω(Tam(E))`, which is finite.
* The covariance of `v_ℓ(Tam)` and `v_{ℓ'}(Tam)` is an explicit convergent series.
* The covariance of `v_ℓ(Tam)` and `v_{ℓ'}(Tam)` is negative.
* The covariance of `v_ℓ(Tam)` and `v_{ℓ'}(Tam)` is `O((ℓℓ')⁻²)`.
* The covariance of `ω_Tam` and `Ω(Tam)` is an explicit convergent series, and their correlation is well defined.
* The moments of the limiting distribution of `Tam(E)` are finite and are Euler products.
* The tail of the limiting distribution of `Tam(E)` decays faster than every power.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only depends on Mathlib. It contains formal statements of [§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean comparator on a Linux machine. First, follow the instructions in https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:
```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
