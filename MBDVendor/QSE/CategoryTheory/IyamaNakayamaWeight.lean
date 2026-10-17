import Mathlib.Algebra.BigOperators.Fin
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtNormalForm
import MBDVendor.QSE.CategoryTheory.IyamaNakayamaPair

/-!
# Weight transport along Iyama's invertible ladders

An isomorphism-invariant, binary-biproduct-additive integer weight preserves
source-minus-target weight across any invertible-ladder step at which the
right-mesh Euler identity holds.  A global Euler hypothesis then gives
constancy along a whole ladder and equality at the two boundary maps of a
Nakayama pair.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

/-- An isomorphism-invariant integral weight additive on binary
biproducts. -/
structure AdditiveObjectWeight (C : Type u) [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] where
  weight : C → ℤ
  iso_invariant :
    ∀ {X Y : C}, Nonempty (X ≅ Y) → weight X = weight Y
  biprod_additive :
    ∀ X Y : C, weight (biprod X Y) = weight X + weight Y

namespace AdditiveObjectWeight

variable {T : FiniteTauCategoryData C Ind}

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- An additive object weight vanishes on every zero object. -/
theorem weight_eq_zero_of_isZero
    (W : AdditiveObjectWeight C) {X : C} (hX : IsZero X) :
    W.weight X = 0 := by
  have h : W.weight X = W.weight (biprod X X) :=
    W.iso_invariant ⟨isoBiprodZero hX⟩
  rw [W.biprod_additive] at h
  omega

omit [IsIdempotentComplete C] in
/-- A binary-additive object weight is additive on `Fin`-indexed
biproducts. -/
theorem weight_finBiproduct (W : AdditiveObjectWeight C) :
    ∀ (n : ℕ) (F : Fin n → C),
      W.weight (⨁ F) = ∑ i, W.weight (F i) := by
  intro n
  induction n with
  | zero =>
      intro F
      have hzero : IsZero (⨁ F) := by
        rw [IsZero.iff_id_eq_zero]
        apply biproduct.hom_ext
        intro i
        exact Fin.elim0 i
      rw [W.weight_eq_zero_of_isZero hzero]
      simp
  | succ n ih =>
      intro F
      have hcons :
          W.weight (⨁ F) =
            W.weight (biprod (F 0) (⨁ fun i : Fin n ↦ F i.succ)) :=
        W.iso_invariant ⟨finBiproductConsIso F⟩
      rw [hcons, W.biprod_additive, ih]
      exact (Fin.sum_univ_succ fun i ↦ W.weight (F i)).symm

omit [IsIdempotentComplete C] in
/-- A binary-additive object weight is additive on every finite
biproduct. -/
theorem weight_biproduct
    (W : AdditiveObjectWeight C) {J : Type w} [Fintype J]
    (F : J → C) :
    W.weight (⨁ F) = ∑ j, W.weight (F j) := by
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let G : Fin (Fintype.card J) → C := fun i ↦ F (e.symm i)
  let factors : ∀ j : J, G (e j) ≅ F j := fun j ↦
    eqToIso (by simp [G, e])
  let reindex : (⨁ F) ≅ ⨁ G :=
    biproduct.whiskerEquiv e factors
  calc
    W.weight (⨁ F) = W.weight (⨁ G) :=
      W.iso_invariant ⟨reindex⟩
    _ = ∑ i, W.weight (G i) := W.weight_finBiproduct _ _
    _ = ∑ j, W.weight (F j) := by
      simpa only [G, e, Equiv.symm_apply_apply] using
        (Equiv.sum_comp e (fun i ↦ W.weight (G i))).symm

/-- Source-minus-target weight of a morphism. -/
def morphismWeight (W : AdditiveObjectWeight C)
    {X Y : C} (_f : X ⟶ Y) : ℤ :=
  W.weight X - W.weight Y

/-- The Euler identity for the chosen right mesh ending at `Y`. -/
def IsRightMeshEulerAt (W : AdditiveObjectWeight C)
    (T : FiniteTauCategoryData C Ind) (Y : C) : Prop :=
  W.weight (T.rightMesh Y).X₁ - W.weight (T.rightMesh Y).X₂ +
      W.weight (T.rightMesh Y).X₃ = 0

/-- The Euler identity holds at every chosen right mesh.  This global
condition is a convenient sufficient hypothesis; right-additive functions
in Iyama's sense only provide it away from the projective boundary. -/
def IsRightMeshEuler (W : AdditiveObjectWeight C)
    (T : FiniteTauCategoryData C Ind) : Prop :=
  ∀ Y : C, W.IsRightMeshEulerAt T Y

/-- Iyama right-additivity gives the Euler identity on objects with no
projective indecomposable summand. -/
def IsRightMeshEulerOffProjectives (W : AdditiveObjectWeight C)
    (T : FiniteTauCategoryData C Ind) : Prop :=
  ∀ Y : C, T.SupportedOnNonprojectives Y →
    W.IsRightMeshEulerAt T Y

/-- Euler identities on the chosen nonprojective indecomposables propagate
to every object supported on nonprojectives. -/
theorem isRightMeshEulerOffProjectives_of_obj
    (W : AdditiveObjectWeight C)
    (hobj : ∀ x : Ind, ¬ T.IsProjective x →
      W.IsRightMeshEulerAt T (T.obj x)) :
    W.IsRightMeshEulerOffProjectives T := by
  intro Y hY
  obtain ⟨n, label, ⟨eY⟩, hnonprojective⟩ := hY
  obtain ⟨eMesh⟩ :=
    T.nonempty_rightMesh_iso_shortComplexBiproduct_of_iso
      (fun i ↦ T.obj (label i)) Y eY
  have h₁ :
      W.weight (T.rightMesh Y).X₁ =
        W.weight
          (shortComplexBiproduct
            (fun i ↦ T.rightMesh (T.obj (label i)))).X₁ :=
    W.iso_invariant ⟨ShortComplex.π₁.mapIso eMesh⟩
  have h₂ :
      W.weight (T.rightMesh Y).X₂ =
        W.weight
          (shortComplexBiproduct
            (fun i ↦ T.rightMesh (T.obj (label i)))).X₂ :=
    W.iso_invariant ⟨ShortComplex.π₂.mapIso eMesh⟩
  have h₃ :
      W.weight (T.rightMesh Y).X₃ =
        W.weight
          (shortComplexBiproduct
            (fun i ↦ T.rightMesh (T.obj (label i)))).X₃ :=
    W.iso_invariant ⟨ShortComplex.π₃.mapIso eMesh⟩
  dsimp only [IsRightMeshEulerAt]
  rw [h₁, h₂, h₃]
  change
    W.weight (⨁ fun i ↦ (T.rightMesh (T.obj (label i))).X₁) -
        W.weight (⨁ fun i ↦ (T.rightMesh (T.obj (label i))).X₂) +
        W.weight (⨁ fun i ↦ (T.rightMesh (T.obj (label i))).X₃) = 0
  rw [W.weight_finBiproduct, W.weight_finBiproduct,
    W.weight_finBiproduct]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  exact hobj (label i) (hnonprojective i)

omit [HasFiniteBiproducts C] [IsIdempotentComplete C] in
/-- Arrow isomorphisms preserve source-minus-target weight. -/
theorem morphismWeight_eq_of_arrowIso
    (W : AdditiveObjectWeight C)
    {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) :
    W.morphismWeight f = W.morphismWeight g := by
  have hleft : W.weight X = W.weight X' :=
    W.iso_invariant ⟨Arrow.leftFunc.mapIso e⟩
  have hright : W.weight Y = W.weight Y' :=
    W.iso_invariant ⟨Arrow.rightFunc.mapIso e⟩
  simp only [morphismWeight]
  rw [hleft, hright]

/-- One invertible ladder square preserves source-minus-target weight. -/
theorem morphismWeight_eq_of_invertibleLadderStep
    (W : AdditiveObjectWeight C)
    {XPrev YPrev XNext YNext : C}
    {aPrev : XPrev ⟶ YPrev} {aNext : XNext ⟶ YNext}
    (hstep : NakayamaLadder.InvertibleLadderStep T aPrev aNext)
    (hEuler : W.IsRightMeshEulerAt T YPrev) :
    W.morphismWeight aPrev = W.morphismWeight aNext := by
  obtain ⟨f, g, comm, ⟨eRight⟩, _⟩ := hstep
  have h₁ : W.weight (T.rightMesh YPrev).X₁ = W.weight XNext :=
    W.iso_invariant ⟨ShortComplex.π₁.mapIso eRight⟩
  have h₂ :
      W.weight (T.rightMesh YPrev).X₂ =
        W.weight (biprod YNext XPrev) :=
    W.iso_invariant ⟨ShortComplex.π₂.mapIso eRight⟩
  have h₃ : W.weight (T.rightMesh YPrev).X₃ = W.weight YPrev :=
    W.iso_invariant ⟨ShortComplex.π₃.mapIso eRight⟩
  dsimp only [IsRightMeshEulerAt] at hEuler
  rw [h₁, h₂, h₃, W.biprod_additive] at hEuler
  simp only [morphismWeight]
  omega

/-- Every two vertical arrows in a finite invertible ladder have the same
source-minus-target weight. -/
theorem morphismWeight_eq_of_invertibleLadderOfDistance
    (W : AdditiveObjectWeight C) (hEuler : W.IsRightMeshEuler T) (n : ℕ)
    {X₀ Y₀ Xₙ Yₙ : C} {start : X₀ ⟶ Y₀} {finish : Xₙ ⟶ Yₙ}
    (h : NakayamaLadder.InvertibleLadderOfDistance T n start finish) :
    W.morphismWeight start = W.morphismWeight finish := by
  obtain ⟨X, Y, a, ⟨eStart⟩, ⟨eFinish⟩, hstep⟩ := h
  have hstart : W.morphismWeight start = W.morphismWeight (a 0) :=
    W.morphismWeight_eq_of_arrowIso eStart
  have hfinish :
      W.morphismWeight (a (Fin.last n)) = W.morphismWeight finish :=
    W.morphismWeight_eq_of_arrowIso eFinish
  have hchain :
      ∀ i : Fin (n + 1),
        W.morphismWeight (a 0) = W.morphismWeight (a i) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
        exact ih.trans
          (W.morphismWeight_eq_of_invertibleLadderStep
            (hstep i) (hEuler _))
  exact hstart.trans ((hchain (Fin.last n)).trans hfinish)

/-- Source-minus-target weight is constant along any finite invertible
ladder. -/
theorem morphismWeight_eq_of_invertibleLadder
    (W : AdditiveObjectWeight C) (hEuler : W.IsRightMeshEuler T)
    {X₀ Y₀ Xₙ Yₙ : C} {start : X₀ ⟶ Y₀} {finish : Xₙ ⟶ Yₙ}
    (h : NakayamaLadder.InvertibleLadder T start finish) :
    W.morphismWeight start = W.morphismWeight finish := by
  obtain ⟨n, hn⟩ := h
  exact W.morphismWeight_eq_of_invertibleLadderOfDistance hEuler n hn

/-- The exact right-additive version of finite-ladder transport.  Euler
equality is required only on nonprojective-supported right endpoints, and
`hSupport` is precisely Iyama's projective-free prefix theorem. -/
theorem morphismWeight_eq_of_invertibleLadderOfDistance_offProjectives
    (W : AdditiveObjectWeight C)
    (hEuler : W.IsRightMeshEulerOffProjectives T)
    (hSupport : NakayamaLadder.HasNonprojectiveRightSupport T)
    (n : ℕ)
    {X₀ Y₀ Xₙ Yₙ : C} {start : X₀ ⟶ Y₀} {finish : Xₙ ⟶ Yₙ}
    (h : NakayamaLadder.InvertibleLadderOfDistance T n start finish) :
    W.morphismWeight start = W.morphismWeight finish := by
  obtain ⟨X, Y, a, ⟨eStart⟩, ⟨eFinish⟩, hstep⟩ := h
  have hstart : W.morphismWeight start = W.morphismWeight (a 0) :=
    W.morphismWeight_eq_of_arrowIso eStart
  have hfinish :
      W.morphismWeight (a (Fin.last n)) = W.morphismWeight finish :=
    W.morphismWeight_eq_of_arrowIso eFinish
  have hchain :
      ∀ i : Fin (n + 1),
        W.morphismWeight (a 0) = W.morphismWeight (a i) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
        exact ih.trans
          (W.morphismWeight_eq_of_invertibleLadderStep
            (hstep i) (hEuler _ (hSupport X Y a hstep i)))
  exact hstart.trans ((hchain (Fin.last n)).trans hfinish)

/-- Source-minus-target weight is constant along a finite ladder under the
precise off-projective Euler and support hypotheses. -/
theorem morphismWeight_eq_of_invertibleLadder_offProjectives
    (W : AdditiveObjectWeight C)
    (hEuler : W.IsRightMeshEulerOffProjectives T)
    (hSupport : NakayamaLadder.HasNonprojectiveRightSupport T)
    {X₀ Y₀ Xₙ Yₙ : C} {start : X₀ ⟶ Y₀} {finish : Xₙ ⟶ Yₙ}
    (h : NakayamaLadder.InvertibleLadder T start finish) :
    W.morphismWeight start = W.morphismWeight finish := by
  obtain ⟨n, hn⟩ := h
  exact W.morphismWeight_eq_of_invertibleLadderOfDistance_offProjectives
    hEuler hSupport n hn

/-- The two endpoint maps of a genuine Nakayama pair have equal
source-minus-target weight. -/
theorem morphismWeight_muMinus_eq_muPlus_of_nakayamaPair
    (W : AdditiveObjectWeight C) (hEuler : W.IsRightMeshEuler T) {A B : Ind}
    (h : T.NakayamaPair A B) :
    W.morphismWeight (T.muMinus A) =
      W.morphismWeight (T.muPlus B) :=
  W.morphismWeight_eq_of_invertibleLadder hEuler h

/-- A genuine Nakayama pair has equal endpoint weights under Iyama's exact
off-projective hypotheses. -/
theorem morphismWeight_muMinus_eq_muPlus_of_nakayamaPair_offProjectives
    (W : AdditiveObjectWeight C)
    (hEuler : W.IsRightMeshEulerOffProjectives T)
    (hSupport : NakayamaLadder.HasNonprojectiveRightSupport T)
    {A B : Ind} (h : T.NakayamaPair A B) :
    W.morphismWeight (T.muMinus A) =
      W.morphismWeight (T.muPlus B) :=
  W.morphismWeight_eq_of_invertibleLadder_offProjectives
    hEuler hSupport h

end AdditiveObjectWeight

end MBDVendor.QSE.Iyama
