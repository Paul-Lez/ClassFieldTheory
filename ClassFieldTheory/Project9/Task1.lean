import Mathlib
import ClassFieldTheory.Project9.PowerSeriesD

variable {R : Type} [Field R] [CharZero R] -- [TopologicalSpace R] [IsTopologicalRing R]
variable {A : Type*} [CommRing A]
    [Algebra R A]  [TopologicalSpace A] [IsTopologicalRing A] [Nontrivial A]
open PowerSeries
open Nat hiding pow_zero pow_succ
open Set Fin Topology

def silly := MultilinearMap.mkPiAlgebra R Unit R

variable (A) in
noncomputable def PowerSeries.toFormalMultilinearSeries (f : R⟦X⟧)   :
    FormalMultilinearSeries R A A := fun n ↦
  (coeff R n f) • (ContinuousMultilinearMap.mkPiAlgebraFin R n A)

--

theorem find_name' {n : ℕ} : (List.ofFn (1 : Fin n → A)).prod = 1 := by
  induction n
  · simp
  · simp

theorem find_name (n : ℕ) : ContinuousMultilinearMap.mkPiAlgebraFin R n A ≠ 0 := by
  unfold ContinuousMultilinearMap.mkPiAlgebraFin
  suffices ∃ x, ContinuousMultilinearMap.mkPiAlgebraFin R n A x ≠ 0 by
    obtain ⟨x, hx⟩ := this
    exact Ne.symm (ne_of_apply_ne DFunLike.coe fun a ↦ hx (congrFun (id (Eq.symm a)) x))
  use 1
  simp [find_name']

theorem toFormalMultilinearSeries_inj : Function.Injective (toFormalMultilinearSeries (R := R) A) := by
  intro f g h
  ext n
  unfold toFormalMultilinearSeries at h
  rw [funext_iff] at h
  specialize h n
  letI :  NoZeroSMulDivisors R (ContinuousMultilinearMap R (fun (i : Fin n) ↦ A) A) := inferInstance
  have := smul_left_injective R (show ContinuousMultilinearMap.mkPiAlgebraFin R n A ≠ 0
    from find_name n) h
  exact this


theorem toFormalMultilinearSeries_comp (f g : R⟦X⟧) : (f.comp g).toFormalMultilinearSeries A =
  (f.toFormalMultilinearSeries A).comp (g.toFormalMultilinearSeries A ):= sorry


theorem toFormalMultilinearSeries_add (f g : R⟦X⟧) : (f + g).toFormalMultilinearSeries A =
  (f.toFormalMultilinearSeries A) + (g.toFormalMultilinearSeries A ):= sorry


-- def MvPowerSeries.toFormalMultilinearSeries [TopologicalSpace R] [IsTopologicalRing R] {σ : Type*} :
--     MvPowerSeries σ R → FormalMultilinearSeries R (σ → R) R := fun f n ↦
--   f n


    #exit




variable (K : Type*)
  [Field K] [ValuativeRel K]
  [UniformSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K]
  [CompleteSpace K] [ValuativeTopology K]
  [ValuativeRel.IsNontrivial K]
  [ValuativeRel.IsRankLeOne K]
  [ValuativeRel.IsDiscrete K]
  [TopologicalSpace (ValuativeRel.ValueGroupWithZero K)]
  -- [(ValuativeRel.ValueGroupWi thZero K)]


-- Filter.tendsto_atTop'
local notation "coeff"  => PowerSeries.coeff R
local notation "D"      => D R

def exp             : K⟦X⟧ := mk λ n ↦ n !⁻¹
def logOneAdd       : K⟦X⟧ := mk λ n ↦ -(-1) ^ n / n
def geometricSeries : K⟦X⟧ := mk λ n ↦ (-1) ^ n
def polylog (d : ℕ) : K⟦X⟧ := mk λ n ↦ (n⁻¹: K)^d

open Filter PowerSeries Topology ValuativeRel

theorem blha {σ : Type*} (x : σ → K) [Preorder σ] [OrderTop σ] :
    atTop.Tendsto x (𝓝 0) ↔ atTop.Tendsto (valuation K ∘ x) (𝓝 0) := by
  rw [Filter.tendsto_atTop', Filter.tendsto_atTop']
  constructor
  · intro H s hs
    rw [OrderTopology.mem_nhds_iff] at hs
    obtain ⟨y, hy⟩ := hs


theorem isTopologicallyNilpotent (x : K)
    (hx : ValuativeRel.valuation K x < 1) :
    IsTopologicallyNilpotent x := by
  unfold IsTopologicallyNilpotent
  rw [Filter.tendsto_atTop]
  rw [ValuativeTopology.mem_nhds_iff]

example (x : K) (n : ValuativeRel.ValueGroupWithZero K)
    (hx : n ≤ ValuativeRel.valuation K x) : HasEval x := by
  rw [hasEval_def]
  unfold IsTopologicallyNilpotent
  apply Valued.tendsto_zero_pow_of_v_lt_one
  -- tendsto_pow_atTop_nhds_zero_iff



  -- constructor
  -- · intro

  --   sorry
  -- · rw [ Nat.cofinite_eq_atTop]
