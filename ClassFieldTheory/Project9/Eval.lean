import Mathlib

variable {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f₁ : F → G} {f₂ : E → F} {g : E → G}
  {p₁ : FormalMultilinearSeries 𝕜 F G} {p₂ : FormalMultilinearSeries 𝕜 E F}
  {x : E}

/-- A version of `HasFPowerSeriesOnBall.unique` for `HasFPowerSeriesAt`. -/
theorem HasFPowerSeriesAt.unique {f g : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E} (hf : HasFPowerSeriesAt f p x)
    (hg : HasFPowerSeriesAt g p x) : ∃ r > 0, Set.EqOn f g (EMetric.ball x r) := by
  obtain ⟨rf, hf⟩ := hf
  obtain ⟨rg, hg⟩ := hg
  let r := min rf rg
  have hr : 0 < r := by simp [r, hf.r_pos, hg.r_pos]
  use r, hr
  replace hf := hf.mono hr (by simp [r])
  replace hg := hg.mono hr (by simp [r])
  exact HasFPowerSeriesOnBall.unique hf hg

theorem exists_pos_eqOn_ball_comp_of_hasFPowerSeriesAt
    (hf₁ : HasFPowerSeriesAt f₁ p₁ (f₂ x)) (hf₂ : HasFPowerSeriesAt f₂ p₂ x)
    (hg : HasFPowerSeriesAt g (p₁.comp p₂) x) :
    ∃ r > 0, (EMetric.ball x r).EqOn (f₁ ∘ f₂) g := by
  refine HasFPowerSeriesAt.unique ?_ hg
  exact HasFPowerSeriesAt.comp hf₁ hf₂

variable [CompleteSpace G]

theorem hasFPowerSeriesAt_sum (h : 0 < p₁.radius) : HasFPowerSeriesAt p₁.sum p₁ 0 := by
  refine ⟨p₁.radius, le_rfl, h, ?_⟩
  intro y hy
  rw [zero_add]
  exact FormalMultilinearSeries.hasSum p₁ hy

variable [CompleteSpace F]

theorem exists_pos_eqOn_ball_sum_comp_comp (hp₁ : 0 < p₁.radius) (hp₂ : 0 < p₂.radius) (h₀ : p₂.sum 0 = 0)
    (h_comp : HasFPowerSeriesAt (p₁.comp p₂).sum (p₁.comp p₂) 0) :
    ∃ r > 0, (EMetric.ball 0 r).EqOn (p₁.sum ∘ p₂.sum) (p₁.comp p₂).sum := by
  apply exists_pos_eqOn_ball_comp_of_hasFPowerSeriesAt (p₁ := p₁) (p₂ := p₂)
  · rw [h₀]
    exact hasFPowerSeriesAt_sum hp₁
  · exact hasFPowerSeriesAt_sum hp₂
  · exact h_comp

variable [CompleteSpace E] {f₁ : F → E} {f₂ : E → F}
  {p₁ : FormalMultilinearSeries 𝕜 F E} {p₂ : FormalMultilinearSeries 𝕜 E F}
  {x : E}

-- Here, let `p₁` and `p₂` be `exp` and `log`.
theorem exists_pos_eqOn_ball_sum_comp_id (hp₁ : 0 < p₁.radius) (hp₂ : 0 < p₂.radius)
    (h : (p₁.comp p₂).sum = id)
    (h₀ : p₂.sum 0 = 0)
    (h_comp : HasFPowerSeriesAt id (p₁.comp p₂) 0) :
    ∃ r > 0, (EMetric.ball 0 r).EqOn (p₁.sum ∘ p₂.sum) id := by
  suffices h : (p₁.comp p₂).sum = id by
    rw [← h]
    apply exists_pos_eqOn_ball_sum_comp_comp hp₁ hp₂ h₀
    rw [h]
    apply h_comp
  exact h































#exit
namespace PowerSeries

noncomputable section

variable {R S : Type*} [CommRing R] [SMul R S]
  [NormedRing S] [NormMulClass S] [CompleteSpace S]

def eval (f : R⟦X⟧) (a : S) : S := ∑' n, coeff R n f • a ^ n
#check FormalMultilinearSeries.comp
-- def mySubst (f g : R⟦X⟧) : R⟦X⟧ := f.eval g

-- def partSum (f : R⟦X⟧) (a : S) (n : Nat) : S :=
--   ∑ m ∈ Finset.range n, coeff R m f • a ^ n

-- def eval (f : R⟦X⟧) (a : S) : S :=
--   (limUnder Filter.atTop (partSum f a))

-- theorem tendsto_nhds_eval (f : R⟦X⟧) (a : S) :
--   Filter.Tendsto (f.partSum a) Filter.atTop (nhds (eval f a)) :=
--     CauchySeq.tendsto_limUnder sorry

-- #check NormedAddCommGroup.tendsto_atTop
-- #check tendsto_nhds_unique

-- variable {R S : Type*} [CommRing R] [NormedCommRing S] [Algebra R S]

-- noncomputable def subst' (a : PowerSeries R) (f : R⟦X⟧) : PowerSeries R := f.subst a

theorem eval₂_subst (f g : PowerSeries R) (a : S) :
    eval (f.subst g) a = f.eval (g.eval a) := by
  unfold eval

  -- rw [Filter.limUnder_eq_iff sorry]
  rw??

variable {𝕜 E : Type*} [Field 𝕜] [NormedField E] [Module 𝕜 E] --[ContinuousAdd E]
  [ContinuousConstSMul 𝕜 E] (p q : FormalMultilinearSeries 𝕜 E E) --(x : E)

-- def subst : FormalMultilinearSeries 𝕜 E E :=
--   p.sum fun _ => q

#check FormalMultilinearSeries.sum

#check NormedSpace.exp
#check PowerSeries.exp

variable [Algebra ℚ E] [IsTopologicalRing E] [CharZero E]
theorem bla (a : E) : NormedSpace.exp ℚ a = (PowerSeries.exp E).eval a := by
  unfold eval
  rw [NormedSpace.exp_eq_tsum]
  congr! 2 with n
  simp
  rw [← Rat.cast_smul_eq_qsmul (R := E)]
  nth_rw 2 [← Rat.cast_natCast]
  norm_cast



#check Rat.cast_natCast
