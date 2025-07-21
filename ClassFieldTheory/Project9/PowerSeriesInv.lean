/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib
import ClassFieldTheory.Project9.PowerSeriesComp

/-
In this file we prove, for a commutative ring `R`, that
a power series `f : R⟦X⟧` is a unit if and only if its constant term
is a unit.

## Main result

- `PowerSeries.isUnit_iff` : a power series is a unit iff its
                                constant term is a unit.
-/

open PowerSeries BigOperators Polynomial


universe u

variable {R : Type u} [CommRing R]

namespace PowerSeries

/--The power series `∑ (a * X) ^ n`.-/
def geometricSeries (a : R) := mk fun n ↦ a ^ n

variable (a : R)

theorem one_sub_smul_X_mul_geometric_series_eq_one :
    ((1: R⟦X⟧) - a • X) * geometricSeries a = 1 := by
  ext n
  rw [sub_mul, map_sub, smul_mul_assoc, map_smul, one_mul, smul_eq_mul, coeff_one]
  cases n with
  | zero => simp [geometricSeries]
  | succ n => simp [geometricSeries, pow_succ']

theorem one_add_smul_X_mul_geometric_series_eq_one :
    ((1 : R⟦X⟧) + a • X) * geometricSeries (-a) = 1 := by
  have := one_sub_smul_X_mul_geometric_series_eq_one (-a)
  rwa [neg_smul, sub_neg_eq_add] at this

theorem C_unit_add_X_mul_inv_smul_geometricSeries_eq_one (a : Rˣ) :
  (C R a + X : R⟦X⟧) * (a.inv • geometricSeries (-a.inv)) = 1 := by
  rw [smul_eq_C_mul, ←mul_assoc, add_mul, ←map_mul,
    Units.inv_eq_val_inv, Units.mul_inv, map_one, mul_comm X,
    ←smul_eq_C_mul]
  apply one_add_smul_X_mul_geometric_series_eq_one

theorem isUnit_C_unit_add_X (a : Rˣ) : IsUnit (C R a + X) := by
  apply isUnit_of_mul_eq_one
  apply C_unit_add_X_mul_inv_smul_geometricSeries_eq_one

private lemma constantCoeff_sub_C_self (f : R⟦X⟧) :
  constantCoeff R (f - C R (constantCoeff R f)) = 0 := by simp

private lemma eq_C_add_X_comp (f : R⟦X⟧) :
  f = (C R (constantCoeff R f) + X) ∘ᶠ (f - C R (constantCoeff R f)) := by
  rw [add_comp]
  · simp
  all_goals
    apply hasComp_of_constantCoeff_eq_zero
    apply constantCoeff_sub_C_self

@[simp]
theorem isUnit_iff (f : R⟦X⟧) : IsUnit f ↔ IsUnit (constantCoeff R f) := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := hf
    apply isUnit_of_mul_eq_one (b := constantCoeff R g.inv)
    simp [← hg, ← map_mul]
  · intro hf
    obtain ⟨a,ha⟩ := hf
    obtain ⟨g,hg⟩ := isUnit_C_unit_add_X a
    rw [eq_C_add_X_comp f]
    apply isUnit_of_mul_eq_one (b := g.inv.comp (f - C R (constantCoeff R f)))
    rw [←  mul_comp, ← ha, ← hg]
    · simp
    all_goals
      apply hasComp_of_constantCoeff_eq_zero
      apply constantCoeff_sub_C_self

end PowerSeries
