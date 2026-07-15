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
# Orthogonality of Mathlib's probabilists' Hermite polynomials

With `Polynomial.hermite` now taking the coefficient ring as a parameter, we work
directly with `Polynomial.hermite ℝ n` and drop the old `hermiteR` shim.
The abstract Stein argument is unchanged; only the analytic layer is ℝ-specific.
-/

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

def gaussianW (x : ℝ) : ℝ := Real.exp (-(x ^ 2 / 2))

@[simp] lemma gaussianW_pos (x : ℝ) : 0 < gaussianW x := Real.exp_pos _

lemma gaussianPDFReal_zero_one_eq (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * gaussianW x := by
  have hcoe : ((1 : NNReal) : ℝ) = 1 := NNReal.coe_one
  rw [ProbabilityTheory.gaussianPDFReal_def]
  simp only [hcoe, mul_one, sub_zero, gaussianW]
  have harg : -x ^ 2 / (2 : ℝ) = -(x ^ 2 / 2) := by ring
  rw [harg]

lemma hasDerivAt_gaussianW (x : ℝ) : HasDerivAt gaussianW (-x * gaussianW x) x := by
  have hpow : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-x) x := by
    have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 * x ^ 1) / 2) x :=
      (hasDerivAt_pow 2 x).div_const 2
    have hneg : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-((2 * x ^ 1) / 2)) x := h2.neg
    convert hneg using 1
    ring
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      (Real.exp (-(x ^ 2 / 2)) * (-x)) x := hpow.exp
  have hval : Real.exp (-(x ^ 2 / 2)) * (-x) = -x * gaussianW x := by
    simp only [gaussianW]; ring
  rw [hval] at hexp
  exact hexp

lemma deriv_gaussianW (x : ℝ) : deriv gaussianW x = -x * gaussianW x :=
  (hasDerivAt_gaussianW x).deriv

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

/-- The standard Gaussian expectation functional `p ↦ ∫ p(x) dμ`, where `μ` is the
standard normal distribution. -/
noncomputable def gaussianFunctional : Polynomial ℝ →ₗ[ℝ] ℝ :=
  { toFun := fun p => ∫ x : ℝ, p.eval x * ProbabilityTheory.gaussianPDFReal 0 1 x
    map_add' := by
      intro p q
      have hInt : ∀ r : ℝ[X],
          MeasureTheory.Integrable (fun x : ℝ =>
               r.eval x * ProbabilityTheory.gaussianPDFReal 0 1 x) := by
        intro r
        refine ((integrable_poly_mul_gaussianW r).const_mul
          (Real.sqrt (2 * Real.pi))⁻¹).congr ?_
        filter_upwards with x
        rw [gaussianPDFReal_zero_one_eq x]; ring
      simp only [eval_add]
      rw [← MeasureTheory.integral_add (hInt p) (hInt q)]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x; ring
    map_smul' := by
      intro c p
      simp only [eval_smul, smul_eq_mul, RingHom.id_apply]
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x; ring }

/-- `gaussianFunctional` is given by integration against the standard Gaussian density. -/
lemma gaussianFunctional_apply (p : Polynomial ℝ) :
    gaussianFunctional p = ∫ x : ℝ, p.eval x * ProbabilityTheory.gaussianPDFReal 0 1 x :=
  rfl

/-- Gaussian orthogonality of the real Hermite polynomials. -/
theorem hermite_orthogonal_gaussian (m n : ℕ) :
    (∫ x : ℝ, (hermite ℝ m).eval x * (hermite ℝ n).eval x * ProbabilityTheory.gaussianPDFReal 0 1 x)
      = if m = n then (m.factorial : ℝ) else 0 := by
  have hmap_one : gaussianFunctional 1 = 1 := by
    change ∫ x : ℝ, (1 : ℝ[X]).eval x * ProbabilityTheory.gaussianPDFReal 0 1 x = 1
    simp only [eval_one, one_mul]
    exact ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
  have hstein : ∀ p : Polynomial ℝ,
      gaussianFunctional (X * p) = gaussianFunctional (derivative p) := by
    intro p
    change (∫ x : ℝ, (X * p).eval x * ProbabilityTheory.gaussianPDFReal 0 1 x)
        = ∫ x : ℝ, (derivative p).eval x * ProbabilityTheory.gaussianPDFReal 0 1 x
    have hc : ∀ q : ℝ[X],
        (∫ x : ℝ, q.eval x * ProbabilityTheory.gaussianPDFReal 0 1 x)
          = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, q.eval x * gaussianW x := by
      intro q
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [gaussianPDFReal_zero_one_eq x]; ring
    rw [hc (X * p), hc (derivative p), integral_X_mul_gaussianW p]
  have h := hermite_orthogonal_of_stein gaussianFunctional hmap_one hstein m n
  rw [hermiteInner, gaussianFunctional_apply] at h
  simpa [mul_assoc] using h

open MeasureTheory ProbabilityTheory

def HermiteMemL2 (n : ℕ) : MemLp (fun x => (hermite ℝ n).eval x) 2 (gaussianReal 0 1) := by
  constructor
  · sorry
  · sorry

def HermiteLift (n : ℕ) : Lp ℝ 2 (gaussianReal 0 1) :=
  (HermiteMemL2 n).toLp (fun x => (hermite ℝ n).eval x)

def HermiteOrthogonality : Orthonormal ℝ HermiteLift := by sorry

lemma eval_hermite_int (n : ℕ) (x : ℝ) :
    (hermite ℝ n).eval x = (aeval x) (Polynomial.hermite ℤ n) := by
  rw [← map_hermite (Int.castRingHom ℝ) n, Polynomial.eval_map, aeval_def]
  congr 1

/-- The orthogonality statement in terms of `Polynomial.hermite ℤ`. -/
theorem hermite_int_orthogonal_gaussian (m n : ℕ) :
    (∫ x : ℝ, (aeval x) (Polynomial.hermite ℤ m) * (aeval x) (Polynomial.hermite ℤ n)
        * ProbabilityTheory.gaussianPDFReal 0 1 x)
      = if m = n then (m.factorial : ℝ) else 0 := by
  simpa [eval_hermite_int] using hermite_orthogonal_gaussian m n

end HermiteOrthogonality
end Polynomial
