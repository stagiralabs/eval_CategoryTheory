import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.ComposableArrows
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Shift.Localization

/-! # Localization of triangulated categories

If `L : C ⥤ D` is a localization functor for a class of morphisms `W` that is compatible
with the triangulation on the category `C` and admits a left calculus of fractions,
it is shown in this file that `D` can be equipped with a pretriangulated category structure,
and that it is triangulated.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Pretriangulated Localization

variable {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasShift D ℤ] [L.CommShift ℤ]

namespace MorphismProperty

/-- Given `W` is a class of morphisms in a pretriangulated category `C`, this is the condition
that `W` is compatible with the triangulation on `C`. -/
class IsCompatibleWithTriangulation (W : MorphismProperty C)
    extends W.IsCompatibleWithShift ℤ : Prop where
  compatible_with_triangulation (T₁ T₂ : Triangle C)
    (_ : T₁ ∈ distTriang C) (_ : T₂ ∈ distTriang C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : W a) (_ : W b)
    (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
      ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (_ : W c),
        (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃)

export IsCompatibleWithTriangulation (compatible_with_triangulation)

end MorphismProperty

namespace Functor

/-- Given a functor `C ⥤ D` from a pretriangulated category, this is the set of
triangles in `D` that are in the essential image of distinguished triangles of `C`. -/
def essImageDistTriang : Set (Triangle D) :=
  fun T => ∃ (T' : Triangle C) (_ : T ≅ L.mapTriangle.obj T'), T' ∈ distTriang C

lemma essImageDistTriang_mem_of_iso {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁)
    (h : T₁ ∈ L.essImageDistTriang) : T₂ ∈ L.essImageDistTriang := by
  obtain ⟨T', e', hT'⟩ := h
  exact ⟨T', e ≪≫ e', hT'⟩

@[target] lemma contractible_mem_essImageDistTriang [EssSurj L] [HasZeroObject D]
    [HasZeroMorphisms D] [L.PreservesZeroMorphisms] (X : D) :
    contractibleTriangle X ∈ L.essImageDistTriang := by
  sorry


@[target] lemma rotate_essImageDistTriang [Preadditive D] [L.Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (T : Triangle D) :
  T ∈ L.essImageDistTriang ↔ T.rotate ∈ L.essImageDistTriang := by
  sorry


@[target] lemma complete_distinguished_essImageDistTriang_morphism
    (H : ∀ (T₁' T₂' : Triangle C) (_ : T₁' ∈ distTriang C) (_ : T₂' ∈ distTriang C)
      (a : L.obj (T₁'.obj₁) ⟶ L.obj (T₂'.obj₁)) (b : L.obj (T₁'.obj₂) ⟶ L.obj (T₂'.obj₂))
      (_ : L.map T₁'.mor₁ ≫ b = a ≫ L.map T₂'.mor₁),
      ∃ (φ : L.mapTriangle.obj T₁' ⟶ L.mapTriangle.obj T₂'), φ.hom₁ = a ∧ φ.hom₂ = b)
    (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ Functor.essImageDistTriang L) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  sorry


end Functor

namespace Triangulated

namespace Localization

variable (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasLeftCalculusOfFractions]

include W in
include W in
@[target] lemma distinguished_cocone_triangle {X Y : D} (f : X ⟶ Y) :
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ L.essImageDistTriang := by
  sorry


section
variable [W.IsCompatibleWithTriangulation]

include W in
include W in
@[target] lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle D)
    (hT₁ : T₁ ∈ L.essImageDistTriang) (hT₂ : T₂ ∈ L.essImageDistTriang)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  sorry


variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [L.Additive]

/-- The pretriangulated structure on the localized category. -/
def pretriangulated : Pretriangulated D where
  distinguishedTriangles := L.essImageDistTriang
  isomorphic_distinguished _ hT₁ _ e := L.essImageDistTriang_mem_of_iso e hT₁
  contractible_distinguished :=
    have := essSurj L W; L.contractible_mem_essImageDistTriang
  distinguished_cocone_triangle f := distinguished_cocone_triangle L W f
  rotate_distinguished_triangle := L.rotate_essImageDistTriang
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism L W

instance isTriangulated_functor :
    letI : Pretriangulated D := pretriangulated L W; L.IsTriangulated :=
  letI : Pretriangulated D := pretriangulated L W
  ⟨fun T hT => ⟨T, Iso.refl _, hT⟩⟩

end

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]

include W in
include W in
@[target] lemma isTriangulated [Pretriangulated D] [L.IsTriangulated] [IsTriangulated C] :
    IsTriangulated D := by
  sorry


variable [W.IsCompatibleWithTriangulation]

instance (n : ℤ) : (shiftFunctor (W.Localization) n).Additive := by
  rw [Localization.functor_additive_iff W.Q W]
  exact Functor.additive_of_iso (W.Q.commShiftIso n)

instance : Pretriangulated W.Localization := pretriangulated W.Q W

instance [IsTriangulated C] : IsTriangulated W.Localization := isTriangulated W.Q W

section

variable [W.HasLocalization]

instance (n : ℤ) : (shiftFunctor (W.Localization') n).Additive := by
  rw [Localization.functor_additive_iff W.Q' W]
  exact Functor.additive_of_iso (W.Q'.commShiftIso n)

instance : Pretriangulated W.Localization' := pretriangulated W.Q' W

instance [IsTriangulated C] : IsTriangulated W.Localization' := isTriangulated W.Q' W

end

end Localization

end Triangulated

namespace Functor

variable [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] [L.mapArrow.EssSurj] [L.IsTriangulated]

lemma distTriang_iff (T : Triangle D) :
    (T ∈ distTriang D) ↔ T ∈ L.essImageDistTriang := by
  constructor
  · intro hT
    let f := L.mapArrow.objPreimage T.mor₁
    obtain ⟨Z, g : f.right ⟶ Z, h : Z ⟶ f.left⟦(1 : ℤ)⟧, mem⟩ :=
      Pretriangulated.distinguished_cocone_triangle f.hom
    exact ⟨_, (exists_iso_of_arrow_iso T _ hT (L.map_distinguished _ mem)
      (L.mapArrow.objObjPreimageIso T.mor₁).symm).choose, mem⟩
  · rintro ⟨T₀, e, hT₀⟩
    exact isomorphic_distinguished _ (L.map_distinguished _ hT₀) _ e

end Functor

end CategoryTheory
