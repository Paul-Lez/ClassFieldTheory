/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/

import Mathlib
import ClassFieldTheory.Project9.PowerSeriesD


-------------------------------------------------------
-- A few examples of proving power series identities --
-------------------------------------------------------

variable {R : Type} [Field R] [CharZero R]

/-
I take the base ring to be a field of characteristic zero.
This is because
     (i) my power series have rational coefficients
         (with all natural denominators),
    (ii) there is currently no instance of `has_inv (power_series R)`
         except in the case that `R` is a field.
-/


open PowerSeries
open Nat hiding pow_zero pow_succ
noncomputable section


local notation "coeff"  => PowerSeries.coeff R
local notation "D"      => D R


namespace my_PowerSeries

def exp             : R⟦X⟧ := mk λ n ↦ n !⁻¹
def logOneAdd       : R⟦X⟧ := mk λ n ↦ -(-1) ^ n / n
def geometricSeries : R⟦X⟧ := mk λ n ↦ (-1) ^ n
def polylog (d : ℕ) : R⟦X⟧ := mk λ n ↦ (n⁻¹: R)^d

/- Experiments with `exp(px)`-/
variable (p : ℕ) [Fact (Nat.Prime p)]

-- This is not the right series.
def expp : (Padic p)⟦X⟧ := mk λ n ↦ p ^ n / (n !)

lemma pHasEval : HasEval (p : (PadicInt p)) := by
  rw [show HasEval (p : PadicInt p) =
    Filter.Tendsto (fun x ↦ (p : PadicInt p) ^ x) Filter.atTop (nhds 0) from rfl]
  rw [@tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  refine mem_ball_zero_iff.mp ?_
  simp
  rw [@inv_lt_one_iff₀]
  right
  norm_num
  obtain this : (Nat.Prime p) := by apply Fact.elim; infer_instance
  exact Prime.one_lt this

-- See PR #24627
instance : IsLinearTopology (PadicInt p) (PadicInt p) := sorry

#check PowerSeries.aeval (pHasEval p) (expp p)

theorem geometricSeries_eq : geometricSeries = (1 + X : R⟦X⟧)⁻¹ :=
by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_add, mul_one]
  · ext n
    rw [map_add, geometricSeries]
    cases n with
    | zero =>
      rw [coeff_zero_mul_X, add_zero, coeff_mk, pow_zero,
        coeff_zero_eq_constantCoeff, map_one]
    | succ n =>
      rw [coeff_succ_mul_X, coeff_mk, coeff_mk, pow_succ,
        mul_neg_one, neg_add_cancel, coeff_one, if_neg (succ_ne_zero n)]
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero


theorem D_geometricSeries : D geometricSeries = -(1 + X)⁻¹ ^ 2 :=
by
  rw [geometricSeries_eq, PowerSeries.D_inv', map_add, D_one, D_X, zero_add,
    mul_one]

@[simp]
theorem D_exp : D exp = exp :=
by
  ext n
  rw [exp, coeff_D, coeff_mk, coeff_mk, factorial_succ, cast_mul, cast_add,
    cast_one, mul_inv, mul_comm, ← mul_assoc, Field.mul_inv_cancel, one_mul]
  rw [←cast_one, ←cast_add, cast_ne_zero]
  exact succ_ne_zero n

@[simp]
theorem constantCoeff_exp : constantCoeff R exp = 1 :=
by
  rw [exp, ← coeff_zero_eq_constantCoeff, coeff_mk, factorial_zero, cast_one,
    inv_one]

@[simp]
theorem exp_neg {f : R⟦X⟧} (hf : constantCoeff R f = 0) :
  exp ∘ᶠ (-f) = (exp ∘ᶠ f)⁻¹ :=
by
  have : constantCoeff R (-f) = 0 := by rwa [map_neg, neg_eq_zero]
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · apply eq_of_D_eq_of_constantCoeff_eq
    · rw [Derivation.leibniz, D_comp', D_comp', D_exp, Derivation.map_one_eq_zero,
        map_neg, mul_neg, smul_neg, smul_eq_mul, smul_eq_mul,
        ←mul_assoc, mul_comm (exp ∘ᶠ (-f) : R⟦X⟧), mul_assoc, add_neg_cancel]
      exact this
      exact hf
    · rw [map_mul, constantCoeff_comp hf, constantCoeff_comp this,
        constantCoeff_exp, map_one, mul_one]
  · rw [constantCoeff_comp hf, constantCoeff_exp]
    exact one_ne_zero


@[simp]
theorem exp_add (f g : R⟦X⟧) (hf : constantCoeff R f = 0) (hg : constantCoeff R g = 0) :
  exp ∘ᶠ (f + g) = exp ∘ᶠ f * exp ∘ᶠ g :=
by
  have eq : constantCoeff R (f + g) = 0 := by rw [map_add, hf, hg, zero_add]
  suffices : 1 = exp ∘ᶠ f * exp ∘ᶠ g * exp ∘ᶠ (-(f + g))
  · rwa [exp_neg, MvPowerSeries.eq_mul_inv_iff_mul_eq, one_mul] at this
    change constantCoeff R (exp ∘ᶠ (f + g)) ≠ 0
    rw [constantCoeff_comp eq, constantCoeff_exp]
    exact one_ne_zero
    rw [map_add, hf, hg, add_zero]
  apply eq_of_D_eq_of_constantCoeff_eq
  · rw [D_mul, D_mul, D_comp', D_comp', D_comp', D_exp, D_one, map_neg, map_add]
    ring
    exact hf
    exact hg
    rwa [map_neg, neg_eq_zero]
  · rw [map_mul, map_mul, constantCoeff_comp hf, constantCoeff_comp hg, constantCoeff_comp,
      constantCoeff_exp, map_one, mul_one, mul_one]
    rw [map_neg, eq, neg_zero]


@[simp]
theorem constantCoeff_logOneAdd : constantCoeff R logOneAdd = 0 := by
  rw [← coeff_zero_eq_constantCoeff, logOneAdd, coeff_mk, cast_zero, div_zero]

theorem hasComp_logOneAdd {f : R⟦X⟧} : f.hasComp logOneAdd :=
by
  apply hasComp_of_constantCoeff_eq_zero constantCoeff_logOneAdd

@[simp]
theorem D_logOneAdd : D logOneAdd = (1 + X)⁻¹ :=
by
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  ext n
  rw [mul_add, mul_one, map_add, coeff_D, logOneAdd, coeff_mk, cast_add,
    cast_one, IsUnit.div_mul_cancel]
  cases n with
  | zero =>
    rw [coeff_zero_mul_X, coeff_zero_one]; norm_num
  | succ n =>
    have : n + 1 ≠ 0 := succ_ne_zero n
    rw [coeff_succ_mul_X, coeff_D, coeff_mk, coeff_one, cast_add, cast_one, IsUnit.div_mul_cancel,
      pow_succ, mul_neg_one, neg_add_cancel, if_neg this]
    apply Ne.isUnit (by norm_cast)
  · apply Ne.isUnit (by norm_cast)
  · rw [map_add, map_one, constantCoeff_X, add_zero]
    exact one_ne_zero

theorem const_exp_sub_one : constantCoeff R (exp - 1) = 0 :=
by
  rw [map_sub, constantCoeff_exp, constantCoeff_one, sub_self]


theorem hasComp_exp_sub_one {f : R⟦X⟧} : f.hasComp (exp - 1) :=
by
  apply hasComp_of_constantCoeff_eq_zero const_exp_sub_one

@[simp]
theorem D_log_comp_exp : D (logOneAdd ∘ᶠ (exp - 1)) = 1 :=
by
  rw [D_comp' const_exp_sub_one, D_logOneAdd, map_sub, D_one, sub_zero, D_exp]
  have : (1 + X : R⟦X⟧).comp (exp - 1) = exp
  · rw [add_comp hasComp_exp_sub_one hasComp_exp_sub_one,
      X_comp, one_comp, add_sub_cancel 1 exp]
  · nth_rw 2 [← this]
    rw [← mul_comp hasComp_exp_sub_one hasComp_exp_sub_one,
      PowerSeries.inv_mul_cancel, one_comp]
    rw [map_add, map_one, constantCoeff_X, add_zero] --simp
    exact one_ne_zero


@[simp]
theorem log_comp_exp : (logOneAdd ∘ᶠ (exp - 1) : R⟦X⟧) = X :=
by
  apply eq_of_D_eq_of_constantCoeff_eq
  · rw [D_log_comp_exp, D_X]
  · rw [constantCoeff_comp const_exp_sub_one, constantCoeff_X, constantCoeff_logOneAdd]

@[simp]
theorem log_comp_mul (f g : R⟦X⟧) (hf : constantCoeff R f = 0) (hg : constantCoeff R g = 0) :
  (logOneAdd ∘ᶠ ((1 + f) * (1 + g) - 1)) = logOneAdd ∘ᶠ f + logOneAdd ∘ᶠ g :=
by
  have eq : constantCoeff R ((1 + f) * (1 + g) - 1) = 0 := by
    rw [map_sub, map_mul, map_add, map_add, hf, hg, map_one, add_zero, mul_one, sub_self]
  have : constantCoeff R (1 + X) ≠ 0
  · rw [map_add, map_one, constantCoeff_X, add_zero]; exact one_ne_zero
  apply eq_of_D_eq_of_constantCoeff_eq
  · rw [D_comp' eq, map_sub, D_mul, map_add, map_add, map_add, D_one, D_comp' hf,
      D_comp' hg, zero_add, sub_zero, zero_add, mul_add, D_logOneAdd, add_comm]
    congr 1
    · rw [inv_comp' _ _ this eq, add_comp (one_hasComp _) (X_hasComp _), one_comp, X_comp,
        add_comm, sub_add_cancel, inv_comp' _ _ this hf, add_comp (one_hasComp _) (X_hasComp _),
        one_comp, X_comp, ←mul_assoc, PowerSeries.mul_inv_rev,
        mul_comm (1 + g)⁻¹, mul_assoc (1 + f)⁻¹, PowerSeries.inv_mul_cancel, mul_one]
      · rw [map_add, map_one, hg, add_zero]; exact one_ne_zero
    · rw [inv_comp' _ _ this eq, add_comp (one_hasComp _) (X_hasComp _), one_comp, X_comp,
        add_comm, sub_add_cancel, inv_comp' _ _ this hg, add_comp (one_hasComp _) (X_hasComp _),
        one_comp, X_comp, ← mul_assoc, PowerSeries.mul_inv_rev, mul_assoc (1 + g)⁻¹,
        PowerSeries.inv_mul_cancel, mul_one]
      · rw [map_add, map_one, hf, add_zero]; exact one_ne_zero
  · rw [constantCoeff_comp eq, map_add, constantCoeff_comp hf, constantCoeff_comp hg,
      constantCoeff_logOneAdd, add_zero]

@[simp]
theorem exp_comp_log : exp ∘ᶠ logOneAdd = (1 + X : R⟦X⟧) :=
by
  apply eq_of_D_eq_of_constantCoeff_eq
  · rw [D_comp' constantCoeff_logOneAdd, map_add, D_one, zero_add, D_exp]
    apply eq_of_D_eq_of_constantCoeff_eq
    · rw [D_mul, D_comp' constantCoeff_logOneAdd, D_exp, D_X, D_one, D_logOneAdd,
        D_inv', map_add, D_one, D_X, zero_add, mul_one, pow_two, mul_neg, ←mul_assoc, mul_comm, neg_add_cancel]
    · rw [D_X, map_one, D_logOneAdd, map_mul, constantCoeff_comp constantCoeff_logOneAdd,
        constantCoeff_inv, map_add, map_one, constantCoeff_X, add_zero, inv_one, mul_one,
        constantCoeff_exp]
  · rw [constantCoeff_comp constantCoeff_logOneAdd, constantCoeff_exp, map_add, constantCoeff_one,
      constantCoeff_X, add_zero]

theorem constantCoeff_polylog_succ (n : ℕ) :
  constantCoeff R (polylog n.succ) = 0 :=
by
  rw [polylog, ← coeff_zero_eq_constantCoeff, coeff_mk, pow_succ,
    cast_zero, inv_zero, mul_zero]

theorem D_polylog_one : D (polylog 1) = (1 - X)⁻¹ :=
by
  rw [PowerSeries.eq_inv_iff_mul_eq_one, mul_sub, mul_one]
  · ext m
    cases m with
    | zero =>
      rw [map_sub, coeff_D, coeff_zero_mul_X, coeff_zero_eq_constantCoeff,
        sub_zero, cast_zero, zero_add, zero_add, mul_one, map_one, polylog, coeff_mk,
        cast_one, pow_one, inv_one]
    | succ n =>
      rw [map_sub, coeff_succ_mul_X, coeff_one, polylog, coeff_D, coeff_D, coeff_mk,
        coeff_mk, pow_one, pow_one, cast_add, cast_add, cast_one, inv_mul_cancel₀ _,
        inv_mul_cancel₀ _, sub_self, if_neg (succ_ne_zero n)]
      · rw [←cast_succ, cast_ne_zero]
        exact succ_ne_zero n
      · norm_cast
  · rw [map_sub, map_one, constantCoeff_X, sub_zero]
    exact one_ne_zero



theorem X_mul_X_polylog_succ (d : ℕ) : X * D (polylog (d + 2)) = polylog (d + 1) :=
by
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, coeff_zero_eq_constantCoeff, constantCoeff_polylog_succ]
  | succ n =>
    simp [polylog]
    rw [← zpow_neg_coe_of_pos _ (by norm_num)]
    rw [← zpow_neg_coe_of_pos _ (by norm_num)]
    nth_rw 2 [← zpow_one ((↑n + 1) : R)]
    rw [← zpow_add' (by grind)]
    grind
