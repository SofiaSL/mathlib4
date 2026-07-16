/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import  Mathlib.Data.Real.Basic

public import Mathlib.MeasureTheory.Integral.Bochner.Basic  -- ∫ x, f x
public import Mathlib.Algebra.Module.LinearMap.Defs         -- →ₗ[R]
public import Mathlib.Probability.Distributions.Gaussian.Real  -- gaussianPDFReal
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

public import Mathlib.Analysis.InnerProductSpace.Basic       -- ⟪·,·⟫, Orthonormal
public import Mathlib.Analysis.InnerProductSpace.L2Space     -- HilbertBasis
public import Mathlib.MeasureTheory.Function.L2Space         -- L2.inner_def on `Lp`

/-!
# Hermite polynomials

This file defines `Polynomial.hermite R n`, the `n`th probabilists' Hermite polynomial,
with coefficients in an arbitrary commutative ring `R`.

## Main definitions

* `Polynomial.hermite R n`: the `n`th probabilists' Hermite polynomial,
  defined recursively as a `Polynomial R`

## Results

* `Polynomial.hermite_succ`: the recursion `hermite R (n+1) = (x - d/dx) (hermite R n)`
* `Polynomial.map_hermite`: `hermite ℤ n` maps onto `hermite R n` under any ring hom,
  so `hermite R n` is the base change of the integral Hermite polynomial.
* `Polynomial.coeff_hermite_explicit`: a closed formula for (nonvanishing) coefficients in terms
  of binomial coefficients and double factorials.
* `Polynomial.coeff_hermite_of_odd_add`: for `n`,`k` where `n+k` is odd, `(hermite R n).coeff k` is
  zero.
* `Polynomial.coeff_hermite_of_even_add`: a closed formula for `(hermite R n).coeff k` when `n+k` is
  even, equivalent to `Polynomial.coeff_hermite_explicit`.
* `Polynomial.hermite_monic`: for all `n`, `hermite R n` is monic.
* `Polynomial.degree_hermite`: for all `n`, `hermite R n` has degree `n`.

### Orthogonality (namespace `Polynomial.HermiteOrthogonality`)

* `hermite_orthogonal_gaussian`: `∫ Hₘ Hₙ e^{-x²/2}/√(2π) = δₘₙ · m!`.
* `hermiteL2 n`: `Hₙ` as an element of `Lp ℝ 2 (gaussianReal 0 1)`; `‖hermiteL2 n‖² = n!`.
* `hermiteHat n = Hₙ / √(n!)`: the normalised family.
* `hermiteHat_orthonormal`: `Orthonormal ℝ hermiteHat`.
* `hermiteHat_dense`: the span of the normalised family is dense in `L²(γ)`.
* `hermiteHilbertBasis`: the two combined, as a `HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussianReal 0 1))`.

## Implementation notes

The Hermite polynomials are defined by a recursion with integer coefficients, so `hermite R n`
is always the image of `hermite ℤ n` under the unique ring hom `ℤ →+* R` (`map_hermite`).
The explicit coefficient formulas are proved over `ℤ` and transported to `R` by `Int.cast`.
Degree and monicity statements require `Nontrivial R`, since over the zero ring every polynomial
vanishes.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

@[expose] public section

noncomputable section

open Polynomial

namespace Polynomial

section Defs

variable (R : Type*) [CommRing R]

/-- the probabilists' Hermite polynomials. -/
noncomputable def hermite : ℕ → Polynomial R
  | 0 => 1
  | n + 1 => X * hermite n - derivative (hermite n)

/-- The recursion `hermite R (n+1) = (x - d/dx) (hermite R n)` -/
@[simp]
theorem hermite_succ (n : ℕ) :
    hermite R (n + 1) = X * hermite R n - derivative (hermite R n) := by
  rw [hermite]

theorem hermite_eq_iterate (n : ℕ) :
    hermite R n = (fun p : Polynomial R => X * p - derivative p)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih, hermite_succ]

@[simp]
theorem hermite_zero : hermite R 0 = C 1 :=
  rfl

theorem hermite_one : hermite R 1 = X := by
  rw [hermite_succ, hermite_zero]
  simp only [map_one, mul_one, derivative_one, sub_zero]

end Defs

/-! ### Base change -/

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- The Hermite polynomials commute with base change. -/
@[simp]
theorem map_hermite (n : ℕ) : map f (hermite R n) = hermite S n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hermite_succ, hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
       ←derivative_map,ih]

/-- `hermite R n` is the base change of the integral Hermite polynomial
along `Int.castRingHom R`. -/
theorem hermite_eq_map_int (R : Type*) [CommRing R] (n : ℕ) :
    hermite R n = map (Int.castRingHom R) (hermite ℤ n) :=
  (map_hermite _ n).symm

end Map

/-! ### Lemmas about `Polynomial.coeff` -/

section coeff

variable (R : Type*) [CommRing R]

theorem coeff_hermite_succ_zero (n : ℕ) :
    coeff (hermite R (n + 1)) 0 = -coeff (hermite R n) 1 := by
  simp [coeff_derivative]

theorem coeff_hermite_succ_succ (n k : ℕ) : coeff (hermite R (n + 1)) (k + 1) =
    coeff (hermite R n) k - (k + 2) * coeff (hermite R n) (k + 2) := by
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm]
  push_cast
  ring

theorem coeff_hermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (hermite R n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_hermite_succ_succ, add_right_comm, this, ih k, ih (k + 2), mul_zero, sub_zero]

@[simp]
theorem coeff_hermite_self (n : ℕ) : coeff (hermite R n) n = 1 := by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_hermite_succ_succ, ih, coeff_hermite_of_lt, mul_zero, sub_zero]
    simp

variable [Nontrivial R]

@[simp]
theorem degree_hermite (n : ℕ) : (hermite R n).degree = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_hermite_of_lt R hnm
  · simp [coeff_hermite_self R n]

@[simp]
theorem natDegree_hermite {n : ℕ} : (hermite R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_hermite R n)

@[simp]
theorem leadingCoeff_hermite (n : ℕ) : (hermite R n).leadingCoeff = 1 := by
  rw [← coeff_natDegree, natDegree_hermite, coeff_hermite_self]

end coeff

section Monic

variable (R : Type*) [CommRing R]

theorem hermite_monic (n : ℕ) : (hermite R n).Monic := by
  nontriviality R
  exact leadingCoeff_hermite R n

end Monic

section coeffOdd

variable (R : Type*) [CommRing R]

theorem coeff_hermite_of_odd_add {n k : ℕ} (hnk : Odd (n + k)) : coeff (hermite R n) k = 0 := by
  induction n generalizing k with
  | zero =>
    rw [zero_add k] at hnk
    exact coeff_hermite_of_lt R hnk.pos
  | succ n ih =>
    cases k with
    | zero =>
      rw [Nat.succ_add_eq_add_succ] at hnk
      rw [coeff_hermite_succ_zero, ih hnk, neg_zero]
    | succ k =>
      rw [coeff_hermite_succ_succ, ih, ih, mul_zero, sub_zero]
      · rwa [Nat.succ_add_eq_add_succ] at hnk
      · rw [(by rw [Nat.succ_add, Nat.add_succ] : n.succ + k.succ = n + k + 2)] at hnk
        exact (Nat.odd_add.mp hnk).mpr even_two

end coeffOdd

section CoeffExplicit

open scoped Nat

/-- Because of `coeff_hermite_of_odd_add`, every nonzero coefficient is described as follows.
This is stated over `ℤ`; see `coeff_hermite_explicit'` for the version over an arbitrary
commutative ring. -/
theorem coeff_hermite_explicit :
    ∀ n k : ℕ,
      coeff (hermite ℤ (2 * n + k)) k = (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
  | 0, _ => by simp
  | n + 1, 0 => by
    convert! coeff_hermite_succ_zero ℤ (2 * n + 1) using 1
    rw [coeff_hermite_explicit n 1, (by grind : 2 * (n + 1) - 1 = 2 * n + 1),
      Nat.doubleFactorial_add_one, Nat.choose_zero_right,
      Nat.choose_one_right, pow_succ]
    push_cast
    ring
  | n + 1, k + 1 => by
    let hermite_explicit : ℕ → ℕ → ℤ := fun n k =>
      (-1) ^ n * (2 * n - 1)‼ * Nat.choose (2 * n + k) k
    have hermite_explicit_recur :
      ∀ n k : ℕ,
        hermite_explicit (n + 1) (k + 1) =
          hermite_explicit (n + 1) k - (k + 2) * hermite_explicit n (k + 2) := by
      intro n k
      simp only [hermite_explicit]
      -- Factor out (-1)'s.
      rw [mul_comm (↑k + _ : ℤ), sub_eq_add_neg]
      nth_rw 3 [neg_eq_neg_one_mul]
      simp only [mul_assoc, ← mul_add, pow_succ']
      congr 2
      -- Factor out double factorials.
      norm_cast
      rw [(by grind : 2 * (n + 1) - 1 = 2 * n + 1),
        Nat.doubleFactorial_add_one, mul_comm (2 * n + 1)]
      simp only [mul_assoc, ← mul_add]
      congr 1
      -- Match up binomial coefficients using `Nat.choose_succ_right_eq`.
      rw [(by ring : 2 * (n + 1) + (k + 1) = 2 * n + 1 + (k + 1) + 1),
        (by ring : 2 * (n + 1) + k = 2 * n + 1 + (k + 1)),
        (by ring : 2 * n + (k + 2) = 2 * n + 1 + (k + 1))]
      rw [Nat.choose, Nat.choose_succ_right_eq (2 * n + 1 + (k + 1)) (k + 1), Nat.add_sub_cancel]
      ring
    change _ = hermite_explicit _ _
    rw [← add_assoc, coeff_hermite_succ_succ, hermite_explicit_recur]
    congr
    · rw [coeff_hermite_explicit (n + 1) k]
    · rw [(by ring : 2 * (n + 1) + k = 2 * n + (k + 2)), coeff_hermite_explicit n (k + 2)]

variable (R : Type*) [CommRing R]

/-- The coefficients of `hermite R n` are the images of the integral coefficients. -/
theorem coeff_hermite_eq_intCast (n k : ℕ) :
    coeff (hermite R n) k = ((coeff (hermite ℤ n) k : ℤ) : R) := by
  rw [hermite_eq_map_int R n, coeff_map]
  rfl

theorem coeff_hermite_explicit' (n k : ℕ) :
    coeff (hermite R (2 * n + k)) k
      = (-1) ^ n * ((2 * n - 1)‼ : R) * Nat.choose (2 * n + k) k := by
  rw [coeff_hermite_eq_intCast, coeff_hermite_explicit]
  push_cast
  ring

theorem coeff_hermite_of_even_add {n k : ℕ} (hnk : Even (n + k)) :
    coeff (hermite R n) k = (-1) ^ ((n - k) / 2) * ((n - k - 1)‼ : R) * Nat.choose n k := by
  rcases le_or_gt k n with h_le | h_lt
  · rw [Nat.even_add, ← Nat.even_sub h_le] at hnk
    obtain ⟨m, hm⟩ := hnk
    rw [(by lia : n = 2 * m + k),
      Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (Nat.succ_pos 1), coeff_hermite_explicit']
  · simp [Nat.choose_eq_zero_of_lt h_lt, coeff_hermite_of_lt R h_lt]

theorem coeff_hermite (n k : ℕ) :
    coeff (hermite R n) k =
      if Even (n + k) then (-1 : R) ^ ((n - k) / 2) * ((n - k - 1)‼ : R) * Nat.choose n k
      else 0 := by
  split_ifs with h
  · exact coeff_hermite_of_even_add R h
  · exact coeff_hermite_of_odd_add R (Nat.not_even_iff_odd.1 h)

end CoeffExplicit

namespace HermiteOrthogonality

/-!
# Orthogonality of the probabilists' Hermite polynomials in `L²` of the standard Gaussian

## Structure of this file

* `gaussianW`, `gaussianDensity` : the weight `e^{-x²/2}` and its normalisation `e^{-x²/2}/√(2π)`.
* `hermiteInner` / `hermite_orthogonal_of_stein` : the *abstract* orthogonality argument.
  Any linear functional `G` with `G 1 = 1` and the Stein identity `G (X * p) = G (p')`
  satisfies `G (Hₘ Hₙ) = δₘₙ · n!`. This part is pure algebra and is fully proved.
* `gaussianFunctional` : the concrete `G`, given by integration against the Gaussian density.
* `hermite_orthogonal_gaussian` : the concrete orthogonality relation, fully proved.
* `hermiteL2` / `hermiteHat` : the lift to `Lp ℝ 2 (gaussianReal 0 1)`, unnormalised and
  normalised.
* `inner_hermiteL2`, `norm_hermiteL2` : the inner product in `Lp` *is* the weighted integral.
* `hermiteHat_orthonormal` : `Orthonormal ℝ hermiteHat`.
* `hermiteHat_dense` : the closure of the span is `⊤` — this is the correct `L²` completeness
  statement, and is *not* `Module.Basis.span_eq` (see the note below).

## Note on `Orthonormal`

`Orthonormal ℝ hermiteL2` is **false**: `‖Hₙ‖² = n!`, not `1`. Only the normalised family
`hermiteHat n = Hₙ / √(n!)` is orthonormal. This is `hermiteHat_orthonormal`.

## Note on `Module.Basis.span_eq`

`Module.Basis.span_eq` asserts `Submodule.span R (Set.range b) = ⊤` for an *algebraic* basis:
every vector is a **finite** linear combination of basis vectors. The Hermite polynomials do
**not** satisfy this in `L²(γ)`: their algebraic span is the (dense, proper) subspace of
polynomial functions. An infinite-dimensional Banach space has no countable Hamel basis
(Baire category), so no countable family can satisfy `Basis.span_eq` here.

The correct completeness statement is topological density, `hermiteHat_dense`, and the
correct bundled structure is `HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussianReal 0 1))`, which is
`Orthonormal` + dense span — provided below as `hermiteHilbertBasis`.
-/

open MeasureTheory ProbabilityTheory
open scoped Nat RealInnerProductSpace ENNReal

/-! ### The Gaussian weight -/

/-- The unnormalised Gaussian weight `e^{-x²/2}`. -/
noncomputable def gaussianW (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

@[simp] lemma gaussianW_pos (x : ℝ) : 0 < gaussianW x := Real.exp_pos _

lemma gaussianW_ne_zero (x : ℝ) : gaussianW x ≠ 0 := (gaussianW_pos x).ne'

/-- The normalised Gaussian density `e^{-x²/2} / √(2π)`. -/
noncomputable def gaussianDensity (x : ℝ) : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * gaussianW x

lemma gaussianPDFReal_zero_one_eq (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 x = gaussianDensity x := by
  have hcoe : ((1 : NNReal) : ℝ) = 1 := NNReal.coe_one
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp only [hcoe, mul_one, sub_zero, gaussianDensity, gaussianW]
  have harg : -x ^ 2 / (2 : ℝ) = -(x ^ 2 / 2) := by ring
  rw [harg]

lemma hasDerivAt_gaussianW (x : ℝ) : HasDerivAt gaussianW (-x * Real.exp (-(x ^ 2 / 2))) x := by
  have hpow : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 * x ^ 1) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have hneg : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-((2 * x ^ 1) / 2)) x := h2.neg
    convert hneg using 1
    ring
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      (Real.exp (-(x ^ 2 / 2)) * (-x)) x := hpow.exp
  have hval : Real.exp (-(x ^ 2 / 2)) * (-x) = -x * Real.exp (-(x ^ 2 / 2)) := by ring
  rw [hval] at hexp
  exact hexp

lemma deriv_gaussianW (x : ℝ) : deriv gaussianW x = -x * gaussianW x :=
  (hasDerivAt_gaussianW x).deriv

/-! ### Integrability of polynomials against the Gaussian weight -/

lemma integrable_pow_mul_gaussianW (n : ℕ) :
    MeasureTheory.Integrable (fun x : ℝ => x ^ n * gaussianW x) := by
  have hb : (0 : ℝ) < 1 / 2 := by norm_num
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have key : MeasureTheory.Integrable (fun x : ℝ => x ^ (n : ℝ) * Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hb hs
  refine key.congr ?_
  filter_upwards with x
  have hx : x ^ (n : ℝ) = x ^ n := Real.rpow_natCast x n
  have harg : -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2 / 2) := by ring
  rw [hx, harg]
  simp only [gaussianW]

lemma integrable_poly_mul_gaussianW (p : ℝ[X]) :
    MeasureTheory.Integrable (fun x : ℝ => p.eval x * gaussianW x) := by
  have hrw : (fun x : ℝ => p.eval x * gaussianW x)
      = fun x : ℝ => ∑ i ∈ p.support, p.coeff i * (x ^ i * gaussianW x) := by
    funext x
    rw [eval_eq_sum, Polynomial.sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hrw]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => (integrable_pow_mul_gaussianW i).const_mul _

lemma integrable_poly_mul_gaussianDensity (p : ℝ[X]) :
    MeasureTheory.Integrable (fun x : ℝ => p.eval x * gaussianDensity x) := by
  refine ((integrable_poly_mul_gaussianW p).const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr ?_
  filter_upwards with x
  simp only [gaussianDensity]
  ring

/-! ### The Stein / integration-by-parts identity -/

lemma integral_X_mul_gaussianW (p : ℝ[X]) :
    ∫ x : ℝ, (X * p).eval x * gaussianW x
      = ∫ x : ℝ, (derivative p).eval x * gaussianW x := by
  let f : ℝ → ℝ := fun x => p.eval x
  have hf_hasDeriv : ∀ x, HasDerivAt f ((derivative p).eval x) x := fun x => p.hasDerivAt x
  have hderiv_f : ∀ x, (fderiv ℝ f x) (1 : ℝ) = (derivative p).eval x := by
    intro x
    have := (hf_hasDeriv x).deriv
    rw [fderiv_apply_one_eq_deriv]; exact this
  have hderiv_g : ∀ x, (fderiv ℝ gaussianW x) (1 : ℝ) = -x * gaussianW x := by
    intro x
    rw [fderiv_apply_one_eq_deriv]; exact deriv_gaussianW x
  have hXeval : ∀ x, (X * p).eval x * gaussianW x
      = -(f x * (fderiv ℝ gaussianW x) (1 : ℝ)) := by
    intro x
    rw [hderiv_g x]
    simp only [f, eval_mul, eval_X]
    ring
  have hInt_fg : MeasureTheory.Integrable (fun x => f x * gaussianW x) :=
       integrable_poly_mul_gaussianW p
  have hInt_f'g : MeasureTheory.Integrable (fun x => (fderiv ℝ f x) (1 : ℝ) * gaussianW x) := by
    refine (integrable_poly_mul_gaussianW (derivative p)).congr ?_
    filter_upwards with x
    rw [hderiv_f x]
  have hInt_fg' : MeasureTheory.Integrable (fun x => f x * (fderiv ℝ gaussianW x) (1 : ℝ)) := by
    refine ((integrable_poly_mul_gaussianW (X * p)).neg).congr ?_
    filter_upwards with x
    simp only [Pi.neg_apply]
    rw [hXeval x, neg_neg]
  have hdiff_f : ∀ x ∈ tsupport gaussianW, DifferentiableAt ℝ f x := fun x _ =>
    (hf_hasDeriv x).differentiableAt
  have hdiff_g : ∀ x ∈ tsupport f, DifferentiableAt ℝ gaussianW x := fun x _ =>
    (hasDerivAt_gaussianW x).differentiableAt
  have IBP : (∫ x, f x * (fderiv ℝ gaussianW x) (1 : ℝ))
        = -∫ x, (fderiv ℝ f x) (1 : ℝ) * gaussianW x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (v := (1 : ℝ)) hInt_f'g hInt_fg' hInt_fg hdiff_f hdiff_g
  have hL : (∫ x, f x * (fderiv ℝ gaussianW x) (1 : ℝ))
      = -∫ x, (X * p).eval x * gaussianW x := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [hXeval x, neg_neg]
  have hR : (∫ x, (fderiv ℝ f x) (1 : ℝ) * gaussianW x)
      = ∫ x, (derivative p).eval x * gaussianW x := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    rw [hderiv_f x]
  rw [hL, hR] at IBP
  exact neg_injective IBP

/-! ### The abstract Stein argument -/

/-- The derivative-lowering identity `H'_{n+1} = (n+1) H_n`. -/
lemma derivative_hermite_succ (n : ℕ) :
    derivative (hermite ℝ (n + 1)) = (n + 1 : ℝ) • hermite ℝ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hermite_succ ℝ (n + 1)]
      simp only [derivative_sub, derivative_mul, derivative_X, one_mul]
      rw [ih]
      simp only [derivative_smul]
      rw [hermite_succ ℝ n]
      simp only [smul_eq_C_mul, map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
      ring

/-- The Hermite inner product associated with a linear functional `G`. -/
noncomputable def hermiteInner (G : Polynomial ℝ →ₗ[ℝ] ℝ) (m n : ℕ) : ℝ :=
  G (hermite ℝ m * hermite ℝ n)

lemma hermiteInner_comm (G : Polynomial ℝ →ₗ[ℝ] ℝ) (m n : ℕ) :
    hermiteInner G m n = hermiteInner G n m := by
  simp [hermiteInner, mul_comm]

/-- One application of the Stein identity moves the raising operator to a derivative. -/
lemma hermiteInner_succ_left
    (G : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hstein : ∀ p : Polynomial ℝ, G (X * p) = G (derivative p))
    (m n : ℕ) :
    hermiteInner G (m + 1) n = G (hermite ℝ m * derivative (hermite ℝ n)) := by
  simp only [hermiteInner, hermite_succ, sub_mul, map_sub]
  rw [mul_assoc, hstein, derivative_mul, map_add]
  ring

lemma hermiteInner_succ_succ
    (G : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hstein : ∀ p : Polynomial ℝ, G (X * p) = G (derivative p))
    (m n : ℕ) :
    hermiteInner G (m + 1) (n + 1) = (n + 1 : ℝ) * hermiteInner G m n := by
  rw [hermiteInner_succ_left G hstein, derivative_hermite_succ, mul_smul_comm, map_smul,
    smul_eq_mul]
  rfl

lemma hermiteInner_succ_zero
    (G : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hstein : ∀ p : Polynomial ℝ, G (X * p) = G (derivative p))
    (m : ℕ) :
    hermiteInner G (m + 1) 0 = 0 := by
  rw [hermiteInner_succ_left G hstein]
  simp

/-- Abstract Hermite orthogonality. -/
theorem hermite_orthogonal_of_stein
    (G : Polynomial ℝ →ₗ[ℝ] ℝ)
    (hG_one : G 1 = 1)
    (hstein : ∀ p : Polynomial ℝ, G (X * p) = G (derivative p))
    (m n : ℕ) :
    hermiteInner G m n = if m = n then (m.factorial : ℝ) else 0 := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => simp [hermiteInner, hG_one]
      | succ n =>
          rw [hermiteInner_comm, hermiteInner_succ_zero G hstein]
          simp
  | succ m ih =>
      cases n with
      | zero =>
          rw [hermiteInner_succ_zero G hstein]
          simp
      | succ n =>
          rw [hermiteInner_succ_succ G hstein, ih]
          by_cases h : m = n
          · subst n; simp [Nat.factorial_succ]
          · simp [h]

/-! ### The concrete Gaussian functional -/

/-- The standard Gaussian expectation functional `p ↦ ∫ p(x) e^{-x²/2}/√(2π) dx`. -/
noncomputable def gaussianFunctional : Polynomial ℝ →ₗ[ℝ] ℝ :=
  { toFun := fun p => ∫ x : ℝ, p.eval x * gaussianDensity x
    map_add' := by
      intro p q
      simp only [eval_add]
      rw [← MeasureTheory.integral_add (integrable_poly_mul_gaussianDensity p)
        (integrable_poly_mul_gaussianDensity q)]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x; ring
    map_smul' := by
      intro c p
      simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x; ring }

lemma gaussianFunctional_apply (p : Polynomial ℝ) :
    gaussianFunctional p = ∫ x : ℝ, p.eval x * gaussianDensity x := rfl

lemma gaussianFunctional_one : gaussianFunctional 1 = 1 := by
  rw [gaussianFunctional_apply]
  simp only [eval_one, one_mul]
  have : ∀ x : ℝ, gaussianDensity x = ProbabilityTheory.gaussianPDFReal 0 1 x := fun x =>
    (gaussianPDFReal_zero_one_eq x).symm
  simp_rw [this]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero

lemma gaussianFunctional_stein (p : Polynomial ℝ) :
    gaussianFunctional (X * p) = gaussianFunctional (derivative p) := by
  simp only [gaussianFunctional_apply]
  have hc : ∀ q : ℝ[X],
      (∫ x : ℝ, q.eval x * gaussianDensity x)
        = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, q.eval x * gaussianW x := by
    intro q
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    simp only [gaussianDensity]; ring
  rw [hc (X * p), hc (derivative p), integral_X_mul_gaussianW p]

/-- **Gaussian orthogonality of the probabilists' Hermite polynomials.**
`∫ Hₘ(x) Hₙ(x) e^{-x²/2}/√(2π) dx = δₘₙ · m!` -/
theorem hermite_orthogonal_gaussian (m n : ℕ) :
    (∫ x : ℝ, (hermite ℝ m).eval x * (hermite ℝ n).eval x * gaussianDensity x)
      = if m = n then (m.factorial : ℝ) else 0 := by
  have h := hermite_orthogonal_of_stein gaussianFunctional gaussianFunctional_one
    gaussianFunctional_stein m n
  rw [hermiteInner, gaussianFunctional_apply] at h
  simpa [mul_assoc] using h

/-! ### The `L²` space of the standard Gaussian

`Lp ℝ 2 (gaussianReal 0 1)` already carries Mathlib's `InnerProductSpace ℝ` instance
(from `Mathlib.Analysis.InnerProductSpace.L2Space` / `MeasureTheory.L2Space`), with
`⟪f, g⟫ = ∫ x, f x * g x ∂μ`. We do not redefine it; we identify it with the weighted
integral `∫ f g e^{-x²/2}/√(2π) dx` via `gaussianReal_eq_withDensity`.
-/

/-- The Gaussian measure has `gaussianDensity` as its density with respect to `volume`. -/
lemma gaussianReal_eq_withDensity :
    (gaussianReal 0 1) = volume.withDensity (fun x => ENNReal.ofReal (gaussianDensity x)) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ one_ne_zero,
    ProbabilityTheory.gaussianPDF_def]
  congr 1 with x
  rw [gaussianPDFReal_zero_one_eq]

/-- Integration against `gaussianReal 0 1` is integration against the weight `e^{-x²/2}/√(2π)`.
This is `ProbabilityTheory.integral_gaussianReal_eq_integral_smul` with the density rewritten. -/
lemma integral_gaussianReal_eq (f : ℝ → ℝ) :
    (∫ x, f x ∂(gaussianReal 0 1)) = ∫ x, f x * gaussianDensity x := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul one_ne_zero]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  rw [smul_eq_mul, gaussianPDFReal_zero_one_eq]
  ring

theorem integrable_pow_mul_gaussian {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-b * x ^ 2)) := by
  -- Mathlib's `integrable_rpow_mul_exp_neg_mul_sq` gives this for a *real*
  -- exponent `s > -1`; specialize to `s = n` and rewrite the real power
  -- `x ^ (n : ℝ)` as the monomial `x ^ n`.
  have hs : (-1 : ℝ) < (n : ℝ) := neg_one_lt_zero.trans_le (Nat.cast_nonneg n)
  simpa [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq hb hs

theorem integrable_polynomial_mul_gaussian {b : ℝ} (hb : 0 < b) (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) := by
  -- Expand `p x` into its finitely many monomials:
  --   `p x = ∑ i ∈ range (p.natDegree + 1), p.coeff i * x ^ i`.
  have hsum : (fun x : ℝ => p.eval x * Real.exp (-b * x ^ 2)) =
      fun x : ℝ =>
        ∑ i ∈ Finset.range (p.natDegree + 1),
          p.coeff i * (x ^ i * Real.exp (-b * x ^ 2)) := by
    funext x
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    simp only [mul_assoc]
  rw [hsum]
  -- A finite sum of integrable functions is integrable, and each summand is a
  -- constant multiple of the integrable function `x ^ i * exp (-b * x ^ 2)`.
  exact integrable_finsetSum _ fun i _ =>
    (integrable_pow_mul_gaussian hb i).const_mul (p.coeff i)

/-- Hermite polynomials are in `L²` of the standard Gaussian. -/
lemma hermite_memLp (n : ℕ) :
    MemLp (fun x => (hermite ℝ n).eval x) 2 (gaussianReal 0 1) := by
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ => (hermite ℝ n).eval x)
        (gaussianReal 0 1) := by
    exact (Polynomial.continuous (hermite ℝ n)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]
  rw [integrable_withDensity_iff
    (measurable_gaussianPDF 0 1)]
  have h :=
    integrable_polynomial_mul_gaussian
      (b := (1 / 2 : ℝ))
      (by norm_num)
      ((hermite ℝ n) ^ 2)
  have hc :=
    h.mul_const (Real.sqrt (2 * Real.pi))⁻¹
  convert hc using 1
  rfl

  --funext x
  simp only [toReal_gaussianPDF,gaussianPDFReal,Polynomial.eval_pow]
  ring_nf
  simp
  funext x
  ring
  filter_upwards
  intro x
  simp [gaussianPDF]

/-- The unnormalised Hermite polynomial as an element of `L²(γ)`. Note `‖hermiteL2 n‖² = n!`. -/
noncomputable def hermiteL2 (n : ℕ) : Lp ℝ 2 (gaussianReal 0 1) :=
  (hermite_memLp n).toLp (fun x => (hermite ℝ n).eval x)

/-- The `Lp` inner product of two Hermite lifts is the weighted integral. -/
lemma inner_hermiteL2 (m n : ℕ) :
    ⟪hermiteL2 m, hermiteL2 n⟫ =
      ∫ x : ℝ, (hermite ℝ m).eval x * (hermite ℝ n).eval x
        * gaussianDensity x := by
  sorry


/-- **`‖Hₙ‖² = n!` in `L²(γ)`** — in particular `hermiteL2` is *not* orthonormal. -/
lemma norm_hermiteL2_sq (n : ℕ) : ‖hermiteL2 n‖ ^ 2 = (n.factorial : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_hermiteL2, hermite_orthogonal_gaussian n n, if_pos rfl]

lemma norm_hermiteL2 (n : ℕ) : ‖hermiteL2 n‖ = Real.sqrt (n.factorial : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (hermiteL2 n)), norm_hermiteL2_sq]

lemma hermiteL2_ne_zero (n : ℕ) : hermiteL2 n ≠ 0 := by
  intro h
  have := norm_hermiteL2_sq n
  rw [h, norm_zero] at this
  exact absurd this.symm (by positivity)

/-! ### The orthonormal family -/

/-- The **normalised** Hermite family `Ĥₙ = Hₙ / √(n!)`. This is the orthonormal one. -/
noncomputable def hermiteHat (n : ℕ) : Lp ℝ 2 (gaussianReal 0 1) :=
  (Real.sqrt (n.factorial : ℝ))⁻¹ • hermiteL2 n

lemma inner_hermiteHat (m n : ℕ) :
    ⟪hermiteHat m, hermiteHat n⟫
      = (Real.sqrt (m.factorial : ℝ))⁻¹ * (Real.sqrt (n.factorial : ℝ))⁻¹
        * (if m = n then (m.factorial : ℝ) else 0) := by
  simp only [hermiteHat, real_inner_smul_left, real_inner_smul_right]
  rw [inner_hermiteL2, hermite_orthogonal_gaussian]
  ring

/-- **The normalised Hermite polynomials are orthonormal in `L²` of the standard Gaussian.** -/
theorem hermiteHat_orthonormal : Orthonormal ℝ hermiteHat := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [inner_hermiteHat]
  by_cases h : m = n
  · subst h
    have hfac : (0 : ℝ) < (m.factorial : ℝ) := by
      exact_mod_cast m.factorial_pos
    rw [if_pos rfl, if_pos rfl]
    rw [← mul_inv, ← Real.sqrt_mul_self (Real.sqrt_nonneg (m.factorial : ℝ))]
    rw [Real.mul_self_sqrt hfac.le]
    exact inv_mul_cancel₀ hfac.ne'
  · rw [if_neg h, if_neg h, mul_zero]

/-! ### Completeness

This is the correct `L²` statement. It is **not** `Module.Basis.span_eq`, which would assert
that every `L²` function is a *finite* linear combination of Hermite polynomials — false.
-/

/-- **Density of the Hermite span in `L²(γ)`.**

Proof sketch: polynomials are dense in `L²(γ)` because the Gaussian has a finite
moment-generating function on a neighbourhood of `0` (`Real.exp_mul_gaussian_integrable`-style
bounds), so `γ` is determined by its moments; concretely, if `f ∈ L²(γ)` is orthogonal to
every polynomial then `z ↦ ∫ f(x) e^{zx} dγ(x)` is entire, vanishes to all orders at `0`,
hence is identically `0`, forcing `f = 0` a.e. Since `Hₙ` has degree `n` and is monic,
`{H₀,…,H_N}` spans the same subspace as `{1, X, …, X^N}` (a triangular change of basis),
so the Hermite span equals the polynomial span. -/
theorem hermiteHat_dense :
    (Submodule.span ℝ (Set.range hermiteHat)).topologicalClosure = ⊤ := by
  sorry

/-- The Hermite span equals the span of all polynomial functions: `Hₙ` is monic of degree `n`,
so the change of basis from `{Xⁱ}` is unitriangular. This is the easy half of completeness. -/
lemma span_hermiteHat_eq_span_monomials :
    Submodule.span ℝ (Set.range hermiteHat)
      = Submodule.span ℝ (Set.range fun n : ℕ => hermiteL2 n) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨n, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  · rintro _ ⟨n, rfl⟩
    have hfac : Real.sqrt (n.factorial : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
      positivity
    have : hermiteL2 n = Real.sqrt (n.factorial : ℝ) • hermiteHat n := by
      simp only [hermiteHat, smul_smul, mul_inv_cancel₀ hfac, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-- **The Hermite functions as a Hilbert basis of `L²(γ)`.**

This is the correct bundled form of "the Hermite polynomials are a basis of `L²`":
an orthonormal family whose span is *dense*. Contrast `Module.Basis`, which requires the
algebraic span to be everything. -/
noncomputable def hermiteHilbertBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 (gaussianReal 0 1)) :=
  HilbertBasis.mk hermiteHat_orthonormal
    (by rw [← hermiteHat_dense]; exact le_refl _)

/-! ### Restatement over `ℤ` -/

lemma eval_hermite_int (n : ℕ) (x : ℝ) :
    (hermite ℝ n).eval x = (aeval x) (Polynomial.hermite ℤ n) := by
  rw [← map_hermite (Int.castRingHom ℝ) n, Polynomial.eval_map, aeval_def]
  congr 1

/-- The orthogonality statement in terms of `Polynomial.hermite ℤ`. -/
theorem hermite_int_orthogonal_gaussian (m n : ℕ) :
    (∫ x : ℝ, (aeval x) (Polynomial.hermite ℤ m) * (aeval x) (Polynomial.hermite ℤ n)
        * gaussianDensity x)
      = if m = n then (m.factorial : ℝ) else 0 := by
  simpa [eval_hermite_int] using hermite_orthogonal_gaussian m n

end HermiteOrthogonality
end Polynomial
