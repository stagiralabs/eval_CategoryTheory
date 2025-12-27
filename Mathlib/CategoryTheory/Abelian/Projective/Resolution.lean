import VerifiedAgora.tagger
/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison, Jakob von Raumer, Joël Riou
-/
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Tactic.SuppressCompilation

/-!
# Abelian categories with enough projectives have projective resolutions

## Main results
When the underlying category is abelian:
* `CategoryTheory.ProjectiveResolution.lift`: Given `P : ProjectiveResolution X` and
  `Q : ProjectiveResolution Y`, any morphism `X ⟶ Y` admits a lifting to a chain map
  `P.complex ⟶ Q.complex`. It is a lifting in the sense that `P.ι` intertwines the lift and
  the original morphism, see `CategoryTheory.ProjectiveResolution.lift_commutes`.
* `CategoryTheory.ProjectiveResolution.liftHomotopy`: Any two such descents are homotopic.
* `CategoryTheory.ProjectiveResolution.homotopyEquiv`: Any two projective resolutions of the same
  object are homotopy equivalent.
* `CategoryTheory.projectiveResolutions`: If every object admits a projective resolution, we can
  construct a functor `projectiveResolutions C : C ⥤ HomotopyCategory C (ComplexShape.down ℕ)`.

* `CategoryTheory.exact_d_f`: `Projective.d f` and `f` are exact.
* `CategoryTheory.ProjectiveResolution.of`: Hence, starting from an epimorphism `P ⟶ X`, where `P`
  is projective, we can apply `Projective.d` repeatedly to obtain a projective resolution of `X`.
-/

suppress_compilation

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Category Limits Projective


namespace ProjectiveResolution

section

variable [HasZeroObject C] [HasZeroMorphisms C]

/-- Auxiliary construction for `lift`. -/
/-- Auxiliary construction for `lift`. -/
def liftFZero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 0 ⟶ Q.complex.X 0 := by sorry


end

section Abelian

variable [Abelian C]

lemma exact₀ {Z : C} (P : ProjectiveResolution Z) :
    (ShortComplex.mk _ _ P.complex_d_comp_π_f_zero).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ P.isColimitCokernelCofork

/-- Auxiliary construction for `lift`. -/
/-- Auxiliary construction for `lift`. -/
def liftFOne {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex.X 1 ⟶ Q.complex.X 1 :=
  Q.exact₀.liftFromProjective (P.complex.d 1 0 ≫ liftFZero f P Q) (by sorry


@[target] theorem liftFOne_zero_comm {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) :
    liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P Q := by
  sorry


/-- Auxiliary construction for `lift`. -/
/-- Auxiliary construction for `lift`. -/
def liftFSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ'g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective
    (P.complex.d (n + 2) (n + 1) ≫ g') (by sorry


/-- A morphism in `C` lift to a chain map between projective resolutions. -/
/-- A morphism in `C` lift to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    P.complex ⟶ Q.complex := by sorry


/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
/-- The resolution maps intertwine the lift of a morphism and that morphism. -/
@[target] theorem lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y)
    (Q : ProjectiveResolution Z) : lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  sorry


@[reassoc (attr := simp)]
lemma lift_commutes_zero {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
    (lift f P Q).f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
  (HomologicalComplex.congr_hom (lift_commutes f P Q) 0).trans (by simp)

/-- An auxiliary definition for `liftHomotopyZero`. -/
/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 := by sorry


@[reassoc (attr := simp)]
lemma liftHomotopyZeroZero_comp {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 :=
  Q.exact₀.liftFromProjective_comp  _ _

/-- An auxiliary definition for `liftHomotopyZero`. -/
/-- An auxiliary definition for `liftHomotopyZero`. -/
def liftHomotopyZeroOne {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) :
    P.complex.X 1 ⟶ Q.complex.X 2 :=
  (Q.exact_succ 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm)
    (by sorry


@[reassoc (attr := by sorry


/-- Any lift of the zero morphism is homotopic to zero. -/
/-- Any lift of the zero morphism is homotopic to zero. -/
def liftHomotopyZero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (f : P.complex ⟶ Q.complex) (comm : f ≫ Q.π = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero f comm) (by sorry


/-- Two lifts of the same morphism are homotopic. -/
def liftHomotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
    (g h : P.complex ⟶ Q.complex) (g_comm : g ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f)
    (h_comm : h ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (liftHomotopyZero _ (by simp [g_comm, h_comm]))

/-- The lift of the identity morphism is homotopic to the identity chain map. -/
/-- The lift of the identity morphism is homotopic to the identity chain map. -/
def liftIdHomotopy (X : C) (P : ProjectiveResolution X) :
    Homotopy (lift (𝟙 X) P P) (𝟙 P.complex) := by
  sorry


/-- The lift of a composition is homotopic to the composition of the lifts. -/
/-- The lift of a composition is homotopic to the composition of the lifts. -/
def liftCompHomotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (P : ProjectiveResolution X)
    (Q : ProjectiveResolution Y) (R : ProjectiveResolution Z) :
    Homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) := by
  sorry

/-- Any two projective resolutions are homotopy equivalent. -/
/-- Any two projective resolutions are homotopy equivalent. -/
def homotopyEquiv {X : C} (P Q : ProjectiveResolution X) :
    HomotopyEquiv P.complex Q.complex where
  hom := lift (𝟙 X) P Q
  inv := lift (𝟙 X) Q P
  homotopyHomInvId := (liftCompHomotopy (𝟙 X) (𝟙 X) P Q P).symm.trans <| by
    sorry


@[reassoc (attr := simp)]
theorem homotopyEquiv_hom_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).hom ≫ Q.π = P.π := by simp [homotopyEquiv]

@[reassoc (attr := simp)]
theorem homotopyEquiv_inv_π {X : C} (P Q : ProjectiveResolution X) :
    (homotopyEquiv P Q).inv ≫ P.π = Q.π := by simp [homotopyEquiv]

end Abelian

end ProjectiveResolution

/-- An arbitrarily chosen projective resolution of an object. -/
/-- An arbitrarily chosen projective resolution of an object. -/
abbrev projectiveResolution (Z : C) [HasZeroObject C]
    [HasZeroMorphisms C] [HasProjectiveResolution Z] :
    ProjectiveResolution Z := by sorry


variable (C)
variable [Abelian C]

section
variable [HasProjectiveResolutions C]

/-- Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def projectiveResolutions : C ⥤ HomotopyCategory C (ComplexShape.down ℕ) where
  obj X := (HomotopyCategory.quotient _ _).obj (projectiveResolution X).complex
  map f := (HomotopyCategory.quotient _ _).map (ProjectiveResolution.lift f _ _)
  map_id X := by
    rw [← (HomotopyCategory.quotient _ _).map_id]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftIdHomotopy
  map_comp f g := by
    rw [← (HomotopyCategory.quotient _ _).map_comp]
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftCompHomotopy

variable {C}

/-- If `P : ProjectiveResolution X`, then the chosen `(projectiveResolutions C).obj X`
is isomorphic (in the homotopy category) to `P.complex`. -/
def ProjectiveResolution.iso {X : C} (P : ProjectiveResolution X) :
    (projectiveResolutions C).obj X ≅
      (HomotopyCategory.quotient _ _).obj P.complex :=
  HomotopyCategory.isoOfHomotopyEquiv (homotopyEquiv _ _)

@[reassoc]
lemma ProjectiveResolution.iso_inv_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    P.iso.inv ≫ (projectiveResolutions C).map f =
      (HomotopyCategory.quotient _ _).map φ ≫ Q.iso.inv := by
  apply HomotopyCategory.eq_of_homotopy
  apply liftHomotopy f
  all_goals
    aesop_cat

@[reassoc]
lemma ProjectiveResolution.iso_hom_naturality {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
    (φ : P.complex ⟶ Q.complex) (comm : φ.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f) :
    (projectiveResolutions C).map f ≫ Q.iso.hom =
      P.iso.hom ≫ (HomotopyCategory.quotient _ _).map φ := by
  rw [← cancel_epi (P.iso).inv, iso_inv_naturality_assoc f P Q φ comm,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

end

variable [EnoughProjectives C]

variable {C} in
variable {C} in
@[target] theorem exact_d_f {X Y : C} (f : X ⟶ Y) :
    (ShortComplex.mk (d f) f (by sorry


namespace ProjectiveResolution

/-!
Our goal is to define `ProjectiveResolution.of Z : ProjectiveResolution Z`.
The `0`-th object in this resolution will just be `Projective.over Z`,
i.e. an arbitrarily chosen projective object with a map to `Z`.
After that, we build the `n+1`-st object as `Projective.syzygies`
applied to the previously constructed morphism,
and the map from the `n`-th object as `Projective.d`.
-/

variable {C}
variable (Z : C)

-- The construction of the projective resolution `of` would be very, very slow
-- if it were not broken into separate definitions and lemmas

/-- Auxiliary definition for `ProjectiveResolution.of`. -/
/-- Auxiliary definition for `ProjectiveResolution.of`. -/
def ofComplex : ChainComplex C ℕ :=
  ChainComplex.mk' (Projective.over Z) (Projective.syzygies (Projective.π Z))
    (Projective.d (Projective.π Z)) (fun f => ⟨_, Projective.d f, by sorry


@[target] lemma ofComplex_d_1_0 :
    (ofComplex Z).d 1 0 = d (Projective.π Z) := by
  sorry


@[target] lemma ofComplex_exactAt_succ (n : ℕ) :
    (ofComplex Z).ExactAt (n + 1) := by
  sorry


instance (n : ℕ) : Projective ((ofComplex Z).X n) := by
  obtain (_ | _ | _ | n) := n <;> apply Projective.projective_over

/-- In any abelian category with enough projectives,
`ProjectiveResolution.of Z` constructs an projective resolution of the object `Z`.
-/
irreducible_def of : ProjectiveResolution Z where
  complex := ofComplex Z
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨Projective.π Z, by
          rw [ofComplex_d_1_0, assoc, kernel.condition, comp_zero]⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨exact_d_f (Projective.π Z), by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [ofComplex]) (by simp)
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt']
      · apply ofComplex_exactAt_succ
      · apply ChainComplex.exactAt_succ_single_obj⟩

instance (priority := 100) (Z : C) : HasProjectiveResolution Z where out := ⟨of Z⟩

instance (priority := 100) : HasProjectiveResolutions C where out _ := inferInstance

end ProjectiveResolution

end CategoryTheory
