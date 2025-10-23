import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Abelian.Basic

noncomputable section

namespace CategoryTheory.Abelian
open Limits

variable {C : Type*} [Category C] [CategoryTheory.Abelian C]

theorem image.ι_comp_eq_zero_of_comp_eq_zero {a b c : C} {f : a ⟶ b} {g : b ⟶ c}
    (H : f ≫ g = 0) : Abelian.image.ι f ≫ g = 0 :=
  Epi.left_cancellation (f := Abelian.factorThruImage f) _ _ (by simp [←Category.assoc, H])

/-- `Abelian.image` as a functor from the arrow category. -/
@[simps]
def imageFunctor : Arrow C ⥤ C where
  obj f := Abelian.image f.hom
  map {f g} u := by
    apply kernel.lift _ (Abelian.image.ι f.hom ≫ u.right)
    rw [Category.assoc]
    apply image.ι_comp_eq_zero_of_comp_eq_zero
    calc
      f.hom ≫ u.right ≫ cokernel.π g.hom = (u.left ≫ g.hom) ≫ cokernel.π g.hom := by
        simp [←Category.assoc]
      _ = u.left ≫ (g.hom ≫ cokernel.π g.hom) := by rw [←Category.assoc]
      _ = 0 := by simp

theorem kernel.ι_comp_eq_zero_of_comp_eq_zero {a b c : C} {f : a ⟶ b} {g : b ⟶ c}
    (H : f ≫ g = 0) : f ≫ Abelian.coimage.π g = 0 :=
  Mono.right_cancellation (f := Abelian.factorThruCoimage g) _ _ (by simp [H])

/-- `Abelian.coimage` as a functor from the arrow category. -/
@[simps]
def coimageFunctor : Arrow C ⥤ C where
  obj f := Abelian.coimage f.hom
  map {f g} u := by
    apply cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom)
    rw [←Category.assoc]
    apply kernel.ι_comp_eq_zero_of_comp_eq_zero (by simp)

end CategoryTheory.Abelian
