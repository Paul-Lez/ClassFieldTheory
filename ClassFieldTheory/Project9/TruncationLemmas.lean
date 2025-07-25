/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Richard M. Hill.
-/
import Mathlib
import Mathlib.RingTheory.PowerSeries.Basic


/-
Some extra lemma about truncations of power series.
-/

universe u

namespace PowerSeries

open Nat hiding pow_succ pow_zero
open Polynomial BigOperators Finset Finset.Nat

variable {R : Type u} [CommSemiring R]
-- scoped notation:9000 R "⟦X⟧" => PowerSeries R

-- theorem trunc_trunc_of_le (f : R⟦X⟧) (hnm : n ≤ m := by rfl) :
--   trunc n ↑(trunc m f) = trunc n f :=
-- by
--   ext d
--   rw [coeff_trunc, coeff_trunc, Polynomial.coeff_coe]
--   split_ifs with h
--   · have : d < m := lt_of_lt_of_le h hnm
--     rw [coeff_trunc, if_pos this]
--   · rfl

-- @[simp]
-- theorem trunc_trunc (f : R⟦X⟧) : trunc n ↑(trunc n f) = trunc n f :=
-- by
--   exact trunc_trunc_of_le f

-- @[simp]
-- theorem trunc_trunc_mul (f g : R ⟦X⟧) :
--   trunc n ( (trunc n f) * g : R⟦X⟧ ) = trunc n ( f * g ) :=
-- by
--   ext m
--   rw [coeff_trunc, coeff_trunc]
--   split_ifs with h
--   · rw [coeff_mul, coeff_mul, sum_congr rfl]
--     intro _ hab
--     have ha := lt_of_le_of_lt (antidiagonal.fst_le hab) h
--     rw [Polynomial.coeff_coe, coeff_trunc, if_pos ha]
--   · rfl

-- @[simp]
-- theorem trunc_mul_trunc (f g : R ⟦X⟧) :
--   trunc n ( f * (trunc n g) : R⟦X⟧ ) = trunc n ( f * g ) :=
-- by
--   rw [mul_comm, trunc_trunc_mul, mul_comm]

-- @[simp]
-- theorem trunc_trunc_mul_trunc (f g : R⟦X⟧) :
--   trunc n (trunc n f * trunc n g : R⟦X⟧) = trunc n (f * g) :=
-- by
--   rw [trunc_trunc_mul, trunc_mul_trunc]

-- @[simp]
-- theorem trunc_trunc_pow (f : R⟦X⟧) (n a : ℕ) :
--   trunc n ((trunc n f) ^ a) = trunc n (f ^ a) :=
-- by
--   induction a with
--   | zero =>
--     rw [pow_zero, pow_zero, Polynomial.coe_one]
--   | succ a ih =>
--     rw [pow_succ, pow_succ, Polynomial.coe_mul, Polynomial.coe_pow,
--       trunc_trunc_mul, ←trunc_trunc_mul_trunc, ←Polynomial.coe_pow, ih,
--       trunc_trunc_mul_trunc]

-- theorem trunc_coe_eq_self (hn : natDegree f < n) :
--   trunc n (f : R⟦X⟧) = f :=
-- by
--   have this : support f ⊆ Ico 0 n
--   · calc
--       support f
--         ⊆ range (f.natDegree + 1)  := supp_subset_range_natDegree_succ
--       _ ⊆ range n                  := Iff.mpr range_subset hn
--       _ = Ico 0 n                  := by rw [range_eq_Ico]
--   nth_rw 2 [←sum_monomial_eq f]
--   rw [trunc, sum_eq_of_subset (hs := this), sum_congr rfl]
--   · intros
--     rw [Polynomial.coeff_coe]
--   · intros
--     apply monomial_zero_right

-- @[simp]
-- theorem trunc_succ (f : R⟦X⟧) (n : ℕ) :
--   trunc n.succ f = trunc n f + Polynomial.monomial n (coeff R n f) :=
-- by
--   rw [trunc, Ico_zero_eq_range, sum_range_succ, trunc, Ico_zero_eq_range]


/-- The function `coeff n : R⟦X⟧ → R` is continuous. I.e. `coeff n f` depends only on a sufficiently
long truncation of the power series `f`.-/
theorem coeff_stable (f : R⟦X⟧) (n m : ℕ) (h : n + 1 ≤ m := by rfl) :
  coeff R n f = coeff R n (trunc m f : R⟦X⟧) :=
by
  rwa [Polynomial.coeff_coe, coeff_trunc, if_pos]

variable (n a b d : ℕ)

/-- The `n`-th coefficient of a`f*g` may be calculated
from the truncations of `f` and `g`.-/
theorem coeff_mul_stable₂ (f g) (ha : n < a) (hb : n < b) :
  coeff R n (f * g) = coeff R n (trunc a f * trunc b g) :=
by
  symm
  rw [←succ_le] at ha hb
  sorry
  -- rw [coeff_stable, ←trunc_trunc_mul_trunc, trunc_trunc_of_le f ha,
  --   trunc_trunc_of_le g hb, trunc_trunc_mul_trunc, ←coeff_stable]


theorem coeff_mul_stable (f g) (h : d.succ ≤ n := by rfl) :
  coeff R d (f * g) = coeff R d (trunc n f * trunc n g)
  := sorry --coeff_mul_stable₂ f g h h


-- theorem natDegree_trunc_lt (f : R⟦X⟧) (n) : (trunc (n + 1) f).natDegree < n + 1 :=
-- by
--   rw [lt_succ_iff, natDegree_le_iff_coeff_eq_zero]
--   intros
--   rw [coeff_trunc]
--   split_ifs with h
--   · rw [lt_succ, ←not_lt] at h
--     contradiction
--   · rfl


-- @[simp]
-- lemma trunc_zero' {f : R⟦X⟧} : trunc 0 f = 0
--   := rfl



-- theorem eval₂_trunc_eq_sum_range [Semiring S] {G : R →+* S} :
--   (trunc n f).eval₂ G s = ∑ i in range n, G (coeff R i f) * s ^ i :=
-- by
--   cases n with
--   | zero =>
--     rw [trunc_zero', range_zero, sum_empty, eval₂_zero]
--   | succ n =>
--     have := natDegree_trunc_lt f n
--     rw [eval₂_eq_sum_range' (hn := this)]
--     apply sum_congr rfl
--     intro _ h
--     rw [mem_range] at h
--     congr
--     rw [coeff_trunc, if_pos h]


-- @[simp]
-- theorem trunc_X : trunc (n + 2) X = (Polynomial.X : R[X]) :=
-- by
--   ext d
--   rw [coeff_trunc, coeff_X]
--   split_ifs with h₁ h₂
--   · rw [h₂, coeff_X_one]
--   · rw [coeff_X_of_ne_one h₂]
--   · rw [coeff_X_of_ne_one]
--     intro hd
--     apply h₁
--     rw [hd]
--     exact one_lt_succ_succ n



end PowerSeries
