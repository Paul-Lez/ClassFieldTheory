import Mathlib
import ClassFieldTheory.Project9.PowerSeriesD
import Mathlib.Algebra.Group.Support

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

#check Composition

-- #synth DiscreteTopology Prop

lemma prlemma {n : ℕ} (a : Fin n → A) (x : Composition n) :
    ∏ i, ∏ j, a ((x.embedding i) j) = ∏ i, a i := by
  simpa [Finset.prod_sigma', Finset.univ_sigma_univ] using x.blocksFinEquiv.prod_comp a

variable (f g : R⟦X⟧)

lemma Finset.singleton_union {α : Type*} [DecidableEq α] (x : α) (s : Finset α) : {x} ∪ s = insert x s := by
  rfl

lemma Finset.union_singleton {α : Type*} [DecidableEq α] (x : α) (s : Finset α) : s ∪ {x} = insert x s := by
  rw [Finset.union_comm]
  rfl

theorem List.toFinset_range (x : ℕ) : Finset.range x = (List.range x).toFinset := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.range_succ, List.range_succ]
    simp [Finset.union_singleton, ih]

-- TODO(Paul): some of the hypotheses (e.g. `hf`) here might need to be tweaked for the theorem
-- to apply below but this shouldn't be a problem.
-- theorem temp {n : ℕ} (F : ℕ → (ℕ →₀ ℕ) → R) (hf : F.support ⊆ Finset.Iic n)
--     (hf' : ∀ d, ∀ l ∈ (Finset.range d).finsuppAntidiag n, ∀ j ∈ Finset.range d, l d = 0 → F n l = 0) :
--     ∑ᶠ (d : ℕ), ∑ l ∈ (Finset.range d).finsuppAntidiag n, F d l
--       = ∑ c : Composition n, F c.length c.blocks.toFinsupp := by
--   let S (d : ℕ) := (Finset.range d).finsuppAntidiag n |>.filter fun l ↦ ∀ i ∈ Finset.range d, l i > 0
--   have : (fun d ↦ ∑ l ∈ S d, F d l).support ⊆ Finset.Iic n := by
--     sorry
--   have eq₁ : ∑ᶠ (d : ℕ), ∑ l ∈ (Finset.range d).finsuppAntidiag n, F d l = ∑ᶠ (d : ℕ), ∑ l ∈ S d, F d l := by
--     sorry
--   rw [eq₁, finsum_eq_finset_sum_of_support_subset _ this]
--   -- have (C : Composition n) : ∃ m, C.blocks.toFinset ⊆ Finset.range m := sorry
--   set u : Composition n → ℕ := fun C ↦ C.length with u_def
--   let hu : ∀ C : Composition n, u C ∈ Finset.Iic n := sorry
--   rw [←Finset.sum_fiberwise_of_maps_to (s := Finset.univ (α := Composition n)) (fun C hC ↦ hu C)
--     (f := fun (c : Composition n) ↦ F c.length c.blocks.toFinsupp)]
--   apply Finset.sum_congr rfl
--   intro x hx
--   symm
--   apply Finset.sum_bij (fun (l : Composition n) _ ↦ l.blocks.toFinsupp)
--   intro a ha
--   rw [Finset.mem_filter, Finset.mem_finsuppAntidiag]
--   constructor
--   · constructor
--     · sorry
--     · sorry
--   · sorry
--   · intro a ha b hb hab
--     ext : 1
--     sorry -- Missing lemma about injectivity of convertion from list to finsupp?
--   · intro b hb
--     rw [Finset.mem_filter] at hb
--     use ⟨List.range x |>.map b, ?_, ?_⟩, ?_
--     · simp
--       sorry
--     · intro i hi
--       rw [List.mem_map] at hi
--       obtain ⟨a, ha, ha'⟩ := hi
--       rw [←ha']
--       exact hb.right a ha
--     · rw [Finset.mem_finsuppAntidiag] at hb
--       rw [← hb.left.left]
--       rw [←List.sum_toFinset]
--       rw [List.toFinset_range]
--       exact List.nodup_range
--     · simp [u_def, Composition.length]
--   · intro a ha
--     simp at ha
--     rw [←ha, u_def]

@[simp]
theorem List.filter_nezero_sum (l : List ℕ) : (List.filter (· ≠ 0) l).sum = l.sum := by
  induction l with
  | nil => simp
  | cons x xs h => aesop (add norm [List.filter_cons])

#check Finset.range
def Composition.ofFinsuppAntidiag (n : ℕ) (c : ℕ →₀ ℕ)
    (hc : c ∈ Finset.finsuppAntidiag (Finset.range n) n) : Composition n where
      blocks :=
        (List.ofFn (fun n : Fin n ↦ c n)).filter (· ≠ 0)
      blocks_pos := by grind
      blocks_sum := by
        rw [List.filter_nezero_sum]
        rw [sum_ofFn fun n_1 ↦ c ↑n_1]
        simp at hc
        rw [Fin.sum_univ_eq_sum_range]
        nth_rw 2 [← hc.1]

def Composition.ofFinsuppAntidiag_nezero (n d : ℕ) (c : ℕ →₀ ℕ)
    (hc : c ∈ Finset.finsuppAntidiag (Finset.range d) n)
    (hc0 : ∀ i : (Finset.range d), 0 < c i) : Composition n where
      blocks := List.ofFn (fun n : Fin d ↦ c n)
      blocks_pos := by aesop
      blocks_sum := by
        rw [sum_ofFn fun m ↦ c ↑m]
        simp at hc
        rw [Fin.sum_univ_eq_sum_range]
        nth_rw 1 [← hc.1]

/-
The correspondance is `c : Composition n` and
`∪ d, (c ∈ finsuppAntidiag (Finset.range d) n) ∧ (∀ i : (Finset.range d), 0 < c i)) `
-/

open Finset in
def Composition.asFinsuppAntidiag (n : ℕ) : Composition n ≃ (Finset.range (n + 1)).sigma
      fun d ↦ {c ∈ (Finset.range d).finsuppAntidiag n | ∀ i ∈ Finset.range d, 0 < c i} where
  toFun c := {
    val := ⟨c.length, c.blocks.toFinsupp⟩
    property := by
      simp_all only [Finset.mem_range, mem_sigma, mem_filter, mem_finsuppAntidiag]
      constructor
      · grind [Composition.length_le]
      · constructor
        · constructor
          · rw [Composition.length, Finset.sum_range]
            simp
          · simp [List.toFinsupp_support];
        · aesop
  }
  invFun s :=
     ⟨(List.range s.1.1).map s.1.2, by aesop, by aesop⟩
  left_inv x := by
    simp [Composition.ext_iff];
    apply List.ext_get
    · simp
    · aesop
  right_inv f := by
    simp [Subtype.ext_iff]; ext
    · simp [Composition.length]
    · simp; ext a;
      obtain ⟨val, property⟩ := f
      obtain ⟨d, f⟩ := val
      simp_all only
      by_cases ha : a < d
      · simp_all
      · simp_all
        rw [Finset.mem_sigma] at property
        simp_all
        obtain ⟨_, ⟨_, h⟩, _⟩ := property
        suffices haa : a ∉ f.support by simp_all
        by_contra!
        obtain hle := h this
        simp at hle; order



/-
theorem subst_formula (h : f.hasComp g) (c : ℕ) : coeff R c (f ∘ᶠ g)
    = ∑ C : Composition c, coeff R (C.length) f * (C.blocks.map fun i ↦ coeff R i g).prod := by
  rw [coeff_comp_eq_finsum (h := h)]
  have : ∑ᶠ (d : ℕ), (coeff R d) f * (coeff R c) (g ^ d)
    = ∑ᶠ (d : ℕ), (coeff R d) f * ∑ l ∈ (Finset.range d).finsuppAntidiag c,
      ∏ i ∈ Finset.range d, (coeff R (l i)) g := by
    apply finsum_congr
    intro x
    congr
    exact coeff_pow x c g
  rw [this]
  simp_rw [Finset.mul_sum]
  rw [temp]
  apply Finset.sum_congr rfl
  intro x _
  congr
  rw [Finset.prod_range, ← List.prod_ofFn (f := fun i ↦ (coeff R (x.blocks.toFinsupp i)) g)]
  congr
  rw [List.ofFn_eq_map]
  have : List.map (fun (i : Fin x.length)↦ (coeff R (x.blocks.toFinsupp i)) g) (List.finRange x.length)
    =  List.map ((fun i ↦ (coeff R i) g) ∘ (fun (i : Fin x.length) ↦ (x.blocks.toFinsupp i))) (List.finRange x.length) := by
    simp
  rw [this, List.comp_map]
  congr
  simp
  all_goals sorry
-/

set_option maxHeartbeats 400000 in
theorem subst_formula (h : f.hasComp g) (c : ℕ) (hassump : (constantCoeff R) g = 0) :
    coeff R c (f ∘ᶠ g) = ∑ C : Composition c, coeff R (C.length) f *
      (C.blocks.map fun i ↦ coeff R i g).prod := by
  rw [coeff_comp_eq_finsum (h := h)]
  have : ∑ᶠ (d : ℕ), (coeff R d) f * (coeff R c) (g ^ d)
    = ∑ᶠ (d : ℕ), (coeff R d) f * ∑ l ∈ (Finset.range d).finsuppAntidiag c,
      ∏ i ∈ Finset.range d, (coeff R (l i)) g := by
    apply finsum_congr
    intro x
    congr
    exact coeff_pow x c g
  rw [this]; clear this
  simp_rw [Finset.mul_sum]
  rw [finsum_eq_finset_sum_of_support_subset (s := Finset.range (c + 1)), Finset.sum_sigma']
  have myPred : ∀ x ∈ (Finset.range (c + 1)).sigma fun i ↦ (Finset.range i).finsuppAntidiag c,
      (coeff R x.fst) f * ∏ i ∈ Finset.range x.fst, (coeff R (x.snd i)) g ≠ 0 →
      ∀ i ∈ Finset.range x.1, 0 < x.2 i := by
    intro x hx heq
    contrapose! heq
    aesop (add safe Finset.prod_eq_zero)
  rw [← Finset.sum_filter_of_ne myPred]
  simp
  symm
  apply Finset.sum_bij' (fun c hs ↦ ⟨c.length, c.blocks.toFinsupp⟩)
    (fun f hf ↦ ⟨(List.range f.1).map f.2, by aesop, by aesop⟩)
  · intro a
    simp [Composition.ext_iff];
    apply List.ext_get
    · simp
    · aesop
  · intro f ha
    simp; ext
    · simp [Composition.length]
    · rw [Finset.mem_filter] at ha
      aesop
      ext a
      by_cases ha : a < fst
      · aesop
      · aesop
        suffices hsup : a ∉ snd.support by simp_all
        by_contra!
        specialize right_1 this
        simp_all; grind
  · intro a ha
    rw [← prod_univ_fun_getElem a.blocks fun i ↦ (coeff R i) g]
    aesop (add norm Finset.prod_range)
  · aesop (add norm [Composition.length, Finset.sum_range, List.toFinsupp_support, Nat.lt_succ_iff])
  · aesop
  · simp_all only [Finset.coe_range, Function.support_subset_iff, ne_eq, mem_Iio]
    intro x a
    contrapose! a
    apply Finset.sum_eq_zero
    intro f a_1
    simp_all only [Finset.mem_finsuppAntidiag, _root_.mul_eq_zero]
    obtain ⟨left, right⟩ := a_1
    right
    have : ∃ i ∈ Finset.range x, f i = 0 := by
      by_contra!
      suffices x ≤ (Finset.range x).sum f by
        subst left; grind
      nth_rw 1 [show x = (Finset.range x).sum 1 by simp]
      apply Finset.sum_le_sum
      intro i b
      simp_all only [Finset.mem_range, ne_eq, Pi.one_apply]
      specialize this i b
      grind
    aesop (add safe Finset.prod_eq_zero)


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

-- example : (1 : ℝ → ℝ) = id := by
--   simp


-- theorem toFormalMultilinearSeries_add (f g : R⟦X⟧) : (f + g).toFormalMultilinearSeries A =
--     (f.toFormalMultilinearSeries A) + (g.toFormalMultilinearSeries A) := sorry

-- #check FormalMultilinearSeries.compAlongComposition


theorem toFormalMultilinearSeries_comp (f g : R⟦X⟧) (H : f.hasComp g)
    (hfg : (constantCoeff R) g = 0) :
    (f.comp g).toFormalMultilinearSeries A =
    (f.toFormalMultilinearSeries A).comp (g.toFormalMultilinearSeries A ) := by
  ext n : 1
  unfold toFormalMultilinearSeries
  letI :  NoZeroSMulDivisors R (ContinuousMultilinearMap R (fun (i : Fin n) ↦ A) A) := inferInstance
  rw [subst_formula _ _ _ _ hfg]
  unfold FormalMultilinearSeries.comp
  rw [Finset.sum_smul (s := Finset.univ (α := Composition n)) (x := ContinuousMultilinearMap.mkPiAlgebraFin R n A)]
  apply Finset.sum_congr rfl
  intro x _
  ext a
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  simp
  have : (FormalMultilinearSeries.applyComposition
          (fun n ↦ (coeff R n) g • ContinuousMultilinearMap.mkPiAlgebraFin R n A) x a) =
    fun i ↦ (((coeff R (x.blocksFun i)) g • ContinuousMultilinearMap.mkPiAlgebraFin R (x.blocksFun i) A)
      (a ∘ (x.embedding i))) := by
    unfold FormalMultilinearSeries.applyComposition
    ext i
    rfl
  have : (List.ofFn
        (FormalMultilinearSeries.applyComposition
          (fun n ↦ (coeff R n) g • ContinuousMultilinearMap.mkPiAlgebraFin R n A) x a)).prod
    = (List.ofFn fun i ↦ (((coeff R (x.blocksFun i)) g • ContinuousMultilinearMap.mkPiAlgebraFin R (x.blocksFun i) A)
      (a ∘ (x.embedding i)))).prod := by aesop
  rw [this]
  have : (List.ofFn fun i ↦  (((coeff R (x.blocksFun i)) g • ContinuousMultilinearMap.mkPiAlgebraFin R (x.blocksFun i) A)
      (a ∘ (x.embedding i)))).prod =  (List.ofFn fun i ↦ (((coeff R (x.blocksFun i)) g))).prod •
        (List.ofFn fun i ↦ (List.ofFn (a ∘ (x.embedding i))).prod).prod := by
    aesop (add norm [List.prod_ofFn, Algebra.smul_def, Finset.prod_mul_distrib])
  rw [this]
  rw [← mul_smul]
  congr 1
  · congr 1
    congr
    have : x.blocks = List.map x.blocksFun  (List.finRange x.length) := by
      rw [← List.ofFn_eq_map, Composition.ofFn_blocksFun x]
    rw [List.ofFn_eq_map, this, ←Function.comp_apply (f := List.map (fun i ↦ (coeff R i) g)), List.map_comp_map]
    congr
  · simp [prod_ofFn, prlemma]
  · exact H

#print axioms toFormalMultilinearSeries_comp -- yay!

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
