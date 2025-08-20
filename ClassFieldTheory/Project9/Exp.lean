import Mathlib

namespace NormedSpace

open Filter RCLike ContinuousMultilinearMap NormedField Asymptotics FormalMultilinearSeries Padic


open scoped Nat Topology ENNReal

section TopologicalAlgebra


section Ultrametric

variable (p : ℕ) [Fact p.Prime] {𝕂 : Type*} [NontriviallyNormedField 𝕂] [NormedAlgebra ℚ_[p] 𝕂]


noncomputable def r : NNReal := p^((-1/(p-1)) : ℝ)


theorem aux (n : ℕ) : ‖(n.factorial : ℚ_[p])‖ ≥ (r p) ^ n := by
  rw[norm_eq_zpow_neg_valuation, r]
  have one_lt_p : 1 < (p : ℝ) := mod_cast Nat.Prime.one_lt (Fact.elim inferInstance)
  simp only [valuation_natCast, zpow_neg, zpow_natCast, NNReal.coe_rpow, NNReal.coe_natCast,
    ge_iff_le]
  have : padicValNat p n.factorial = ((p-1)⁻¹ : ℝ) * (n - (p.digits n).sum) := by
      rw [eq_inv_mul_iff_mul_eq₀ ?_]
      have ineq :  n ≥ (p.digits n).sum := Nat.digit_sum_le p n
      have := sub_one_mul_padicValNat_factorial (p := p) n
      rify at this
      rw [Nat.cast_sub ineq, Nat.cast_sub (Nat.Prime.one_le (Fact.elim inferInstance)), Nat.cast_one] at this
      simpa using this
      linarith
  have this' : ((p : ℝ) - 1)⁻¹ * ↑(p.digits n).sum ≥ 0 := by
    apply mul_nonneg
    norm_num
    exact Nat.Prime.one_le (Fact.elim inferInstance)
    linarith
  rw [← Real.rpow_mul_natCast ?_ (-1 / (↑p - 1)) n]
  have this'' : padicValNat p n.factorial ≤ (n * ((p-1) : ℝ)⁻¹ : ℝ) := by bound
  rw[← Real.rpow_neg_one, ← Real.rpow_natCast, ← Real.rpow_mul, mul_neg_one]
  gcongr
  bound
  rw[div_eq_mul_inv] at *
  simp only [neg_mul, one_mul, neg_le_neg_iff]
  rw[mul_comm]
  exact this''
  positivity
  positivity
  exact_mod_cast Nat.factorial_ne_zero n


theorem expSeries_radius_eq : r p ≤ (expSeries ℚ_[p] 𝕂).radius := by
  apply forall_lt_imp_le_iff_le_of_dense.mp
  intro r' hr'
  have hr₁ : r' = r'.toNNReal := Eq.symm (ENNReal.coe_toNNReal (LT.lt.ne_top hr'))
  have hr₂ : r'.toNNReal < r p := ENNReal.toNNReal_lt_of_lt_coe hr'
  rw [hr₁]
  apply le_radius_of_tendsto (l := 0) (r := r'.toNNReal) (expSeries ℚ_[p] 𝕂)
  simp only [expSeries, norm_smul, norm_inv, norm_mkPiAlgebraFin, mul_one]
  have rp_pos : 0 < r p := by simpa using zero_le'.trans_lt hr'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds)
  have : Tendsto (fun n ↦ (r'.toNNReal/(r p)) ^ n) atTop (𝓝 0) := by
    apply NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    norm_cast at rp_pos
    bound
  rotate_left
  intro n
  positivity
  have seq_bound : (fun n ↦ ‖(n ! : ℚ_[p])‖⁻¹ * r'.toNNReal ^ n) ≤ fun n ↦ ((r'.toNNReal/(r p)) ^ n).toReal := by
    intro n
    simp only
    rw[div_pow, div_eq_mul_inv, mul_comm]
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv]
    gcongr
    exact aux p n
  exact seq_bound
  rw [← NNReal.tendsto_coe] at this
  norm_cast



-- Below theorem should be much easier to prove by proving that log is an isometry and simply using that exp is its inverse.

-- theorem image_of_ball_subset_ball [CompleteSpace 𝕂] [IsUltrametricDist 𝕂] (x : 𝕂) (r' : NNReal) (hr : r' < r p) (hx : ‖x‖₊ ≤ r') : ‖exp 𝕂 x - 1‖ ≤ r' := by
--   have x_mem_ball_of_convergence : x ∈ EMetric.ball 0 (expSeries ℚ_[p] 𝕂).radius := by
--     simp only [EMetric.mem_ball, edist_zero_right]
--     apply lt_of_le_of_lt (enorm_le_coe.mpr hx)
--     apply lt_of_lt_of_le (ENNReal.coe_lt_coe_of_lt hr)
--     exact expSeries_radius_eq p
--   simp only [exp_eq_tsum, smul_eq_mul]
--   rw [Summable.tsum_eq_add_tsum_ite _ 0]
--   simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, inv_one, add_sub_cancel_left]


--   · apply IsUltrametricDist.norm_tsum_le_of_forall_le
--     intro i
--     split
--     · simp
--     · simp only [norm_mul, norm_inv, norm_pow]
--       sorry


--   · apply FormalMultilinearSeries.summable at x_mem_ball_of_convergence
--     rw[expSeries_apply_eq'] at x_mem_ball_of_convergence
--     conv at x_mem_ball_of_convergence => congr; intro n; rw[Algebra.smul_def]; simp
--     trivial

end Ultrametric



end TopologicalAlgebra

end NormedSpace
