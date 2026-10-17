import Mathlib.Algebra.BigOperators.Fin
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtDirectFinite
import MBDVendor.QSE.CategoryTheory.IyamaNakayamaWeight

/-!
# Label weights in a finite Krull--Schmidt category

Isomorphic displayed decompositions into the chosen indecomposable skeleton
have equal sums under every commutative-monoid-valued label weight.  It
follows that an arbitrary integer-valued label weight extends to an
isomorphism-invariant, biproduct-additive weight on all objects.

This is the classification-free weight extension used in Iyama's strictness
argument.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w z

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

namespace FiniteRightTauCategoryData

variable (T : FiniteRightTauCategoryData C Ind)

/-- Isomorphic displayed decompositions have the same total under every
commutative-monoid-valued label weight. -/
theorem sum_weight_eq_of_nonempty_iso_finBiproduct_obj
    {M : Type z} [AddCommMonoid M] (weight : Ind → M) :
    ∀ (n m : ℕ) (source : Fin n → Ind) (target : Fin m → Ind),
      Nonempty
        ((⨁ fun i ↦ T.obj (source i)) ≅
          ⨁ fun j ↦ T.obj (target j)) →
        (∑ i, weight (source i)) = ∑ j, weight (target j) := by
  intro n
  induction n with
  | zero =>
      intro m source target e
      cases m with
      | zero => simp
      | succ m =>
          obtain ⟨e⟩ := e
          have hzeroSource : IsZero (⨁ fun i ↦ T.obj (source i)) := by
            rw [IsZero.iff_id_eq_zero]
            apply biproduct.hom_ext
            intro i
            exact Fin.elim0 i
          have hzeroTarget : IsZero
              (⨁ fun j ↦ T.obj (target j)) :=
            hzeroSource.of_iso e.symm
          have hzeroHead : IsZero (T.obj (target 0)) := by
            rw [IsZero.iff_id_eq_zero]
            calc
              𝟙 (T.obj (target 0)) =
                  biproduct.ι (fun j ↦ T.obj (target j)) 0 ≫
                    biproduct.π (fun j ↦ T.obj (target j)) 0 := by simp
              _ = 0 := by
                rw [hzeroTarget.eq_of_tgt
                  (biproduct.ι (fun j ↦ T.obj (target j)) 0) 0,
                  zero_comp]
          exact (T.obj_indec (target 0)).1 hzeroHead |>.elim
  | succ n ih =>
      intro m source target e
      cases m with
      | zero =>
          obtain ⟨e⟩ := e
          have hzeroTarget : IsZero (⨁ fun j ↦ T.obj (target j)) := by
            rw [IsZero.iff_id_eq_zero]
            apply biproduct.hom_ext
            intro j
            exact Fin.elim0 j
          have hzeroSource : IsZero
              (⨁ fun i ↦ T.obj (source i)) :=
            hzeroTarget.of_iso e
          have hzeroHead : IsZero (T.obj (source 0)) := by
            rw [IsZero.iff_id_eq_zero]
            calc
              𝟙 (T.obj (source 0)) =
                  biproduct.ι (fun i ↦ T.obj (source i)) 0 ≫
                    biproduct.π (fun i ↦ T.obj (source i)) 0 := by simp
              _ = 0 := by
                rw [hzeroSource.eq_of_tgt
                  (biproduct.ι (fun i ↦ T.obj (source i)) 0) 0,
                  zero_comp]
          exact (T.obj_indec (source 0)).1 hzeroHead |>.elim
      | succ m =>
          obtain ⟨e⟩ := e
          let f : T.obj (source 0) ⟶
              ⨁ fun j ↦ T.obj (target j) :=
            biproduct.ι (fun i ↦ T.obj (source i)) 0 ≫ e.hom
          let g : (⨁ fun j ↦ T.obj (target j)) ⟶
              T.obj (source 0) :=
            e.inv ≫ biproduct.π (fun i ↦ T.obj (source i)) 0
          have hfg : f ≫ g = 𝟙 (T.obj (source 0)) := by
            simp [f, g, Category.assoc]
          obtain ⟨j, hj⟩ :=
            T.exists_isIso_component_of_retraction_finBiproduct
              (source 0) (m + 1) target f g hfg
          have hlabel : source 0 = target j :=
            T.obj_skeletal
              ⟨asIso (f ≫ biproduct.π
                (fun k ↦ T.obj (target k)) j)⟩
          let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 j
          let targetObj : Fin (m + 1) → C :=
            fun k ↦ T.obj (target k)
          let eReindex :
              (⨁ fun k ↦ targetObj (σ k)) ≅ ⨁ targetObj :=
            biproduct.whiskerEquiv σ (fun _ ↦ Iso.refl _)
          let eBinary :
              T.obj (source 0) ⊞
                  (⨁ fun i : Fin n ↦ T.obj (source i.succ)) ≅
                targetObj (σ 0) ⊞
                  (⨁ fun k : Fin m ↦ targetObj (σ k.succ)) :=
            (finBiproductConsIso (fun i ↦ T.obj (source i))).symm.trans
              (e.trans
                (eReindex.symm.trans
                  (finBiproductConsIso
                    (fun k ↦ targetObj (σ k)))))
          have htop : IsIso
              (biprod.inl ≫ eBinary.hom ≫ biprod.fst) := by
            have hcomponent := hj
            change IsIso
              (f ≫ biproduct.π
                (fun j ↦ T.obj (target j)) j) at hcomponent
            have hσ0 : σ 0 = j := by simp [σ]
            have hcomponent' : IsIso
                (f ≫ biproduct.π targetObj (σ 0)) := by
              rw [hσ0]
              simpa only [targetObj] using hcomponent
            have hsourceHead :
                biprod.inl ≫
                    (finBiproductConsIso
                      (fun i ↦ T.obj (source i))).symm.hom =
                  biproduct.ι (fun i ↦ T.obj (source i)) 0 := by
              dsimp only [finBiproductConsIso]
              simp
            have htargetHead :
                eReindex.symm.hom ≫
                    (finBiproductConsIso
                      (fun k ↦ targetObj (σ k))).hom ≫ biprod.fst =
                  biproduct.π targetObj (σ 0) := by
              dsimp only [finBiproductConsIso]
              rw [biprod.lift_fst]
              dsimp only [eReindex]
              change
                (biproduct.whiskerEquiv σ
                    (fun x ↦ Iso.refl (targetObj (σ x)))).inv ≫
                    biproduct.π (fun k ↦ targetObj (σ k)) 0 =
                  biproduct.π targetObj (σ 0)
              rw [biproduct.whiskerEquiv_inv_eq_lift]
              simp
            have heq :
                biprod.inl ≫ eBinary.hom ≫ biprod.fst =
                  f ≫ biproduct.π targetObj (σ 0) := by
              dsimp only [eBinary]
              simp only [Iso.trans_hom, Category.assoc]
              rw [← Category.assoc, hsourceHead]
              rw [htargetHead]
              dsimp only [f]
              exact (Category.assoc _ _ _).symm
            rw [heq]
            exact hcomponent'
          letI : IsIso
              (biprod.inl ≫ eBinary.hom ≫ biprod.fst) := htop
          let eTail :
              (⨁ fun i : Fin n ↦ T.obj (source i.succ)) ≅
                ⨁ fun k : Fin m ↦ targetObj (σ k.succ) :=
            Biprod.isoElim eBinary
          have htail :
              (∑ i : Fin n, weight (source i.succ)) =
                ∑ k : Fin m, weight (target (σ k.succ)) :=
            ih m (fun i ↦ source i.succ)
              (fun k ↦ target (σ k.succ)) ⟨eTail⟩
          have hσ0 : σ 0 = j := by simp [σ]
          have hhead : weight (source 0) = weight (target (σ 0)) := by
            rw [hσ0, hlabel]
          calc
            (∑ i, weight (source i)) =
                weight (source 0) +
                  ∑ i : Fin n, weight (source i.succ) :=
              Fin.sum_univ_succ _
            _ = weight (target (σ 0)) +
                  ∑ k : Fin m, weight (target (σ k.succ)) := by
              rw [hhead, htail]
            _ = ∑ k : Fin (m + 1), weight (target (σ k)) :=
              (Fin.sum_univ_succ
                (fun k : Fin (m + 1) ↦ weight (target (σ k)))).symm
            _ = ∑ k : Fin (m + 1), weight (target k) :=
              Equiv.sum_comp σ (fun k ↦ weight (target k))

/-- In particular, every chosen indecomposable label occurs with the same
multiplicity in two isomorphic displayed decompositions. -/
theorem label_multiplicity_eq_of_nonempty_iso_finBiproduct_obj
    [DecidableEq Ind] (p : Ind) (n m : ℕ)
    (source : Fin n → Ind) (target : Fin m → Ind)
    (e : Nonempty
      ((⨁ fun i ↦ T.obj (source i)) ≅
        ⨁ fun j ↦ T.obj (target j))) :
    (∑ i, if source i = p then 1 else 0) =
      ∑ j, if target j = p then 1 else 0 := by
  exact T.sum_weight_eq_of_nonempty_iso_finBiproduct_obj
    (M := ℕ) (fun q ↦ if q = p then 1 else 0) n m source target e

/-- Number of factors in one noncomputably chosen decomposition. -/
noncomputable def chosenDecompositionSize (X : C) : ℕ :=
  (T.obj_decomposition X).choose

/-- Labels in one noncomputably chosen decomposition. -/
noncomputable def chosenDecompositionLabel (X : C) :
    Fin (T.chosenDecompositionSize X) → Ind :=
  (T.obj_decomposition X).choose_spec.choose

/-- The isomorphism exhibiting the chosen decomposition. -/
noncomputable def chosenDecompositionIso (X : C) :
    X ≅ ⨁ fun i ↦ T.obj (T.chosenDecompositionLabel X i) :=
  (T.obj_decomposition X).choose_spec.choose_spec.some

/-- Sum a label weight over the chosen finite decomposition of an object. -/
noncomputable def chosenLabelWeight (weight : Ind → ℤ) (X : C) : ℤ :=
  ∑ i, weight (T.chosenDecompositionLabel X i)

/-- Chosen label weight is invariant under object isomorphism. -/
theorem chosenLabelWeight_iso_invariant (weight : Ind → ℤ)
    {X Y : C} (e : Nonempty (X ≅ Y)) :
    T.chosenLabelWeight weight X = T.chosenLabelWeight weight Y := by
  obtain ⟨e⟩ := e
  apply T.sum_weight_eq_of_nonempty_iso_finBiproduct_obj weight
  exact ⟨(T.chosenDecompositionIso X).symm.trans
    (e.trans (T.chosenDecompositionIso Y))⟩

/-- Chosen label weight is additive under binary biproducts. -/
theorem chosenLabelWeight_biprod_additive (weight : Ind → ℤ)
    (X Y : C) :
    T.chosenLabelWeight weight (biprod X Y) =
      T.chosenLabelWeight weight X + T.chosenLabelWeight weight Y := by
  classical
  let n := T.chosenDecompositionSize X
  let m := T.chosenDecompositionSize Y
  let labelX : Fin n → Ind := T.chosenDecompositionLabel X
  let labelY : Fin m → Ind := T.chosenDecompositionLabel Y
  let F : Fin n → C := fun i ↦ T.obj (labelX i)
  let G : Fin m → C := fun j ↦ T.obj (labelY j)
  let combined : Fin (n + m) → Ind := Fin.append labelX labelY
  let flattenFactors :
      ∀ s : Fin n ⊕ Fin m,
        T.obj (combined (finSumFinEquiv s)) ≅ Sum.elim F G s := by
    intro s
    rcases s with i | j
    · apply eqToIso
      simp [combined, F, finSumFinEquiv_apply_left]
    · apply eqToIso
      simp [combined, G, finSumFinEquiv_apply_right]
  let eFlatten :
      (⨁ Sum.elim F G) ≅ ⨁ fun k ↦ T.obj (combined k) :=
    biproduct.whiskerEquiv finSumFinEquiv flattenFactors
  let eCombined :
      biprod X Y ≅ ⨁ fun k ↦ T.obj (combined k) :=
    (biprod.mapIso (T.chosenDecompositionIso X)
      (T.chosenDecompositionIso Y)).trans
        ((finBiproductBiprodIsoSum F G).trans eFlatten)
  have hchosen :
      T.chosenLabelWeight weight (biprod X Y) =
        ∑ k : Fin (n + m), weight (combined k) := by
    apply T.sum_weight_eq_of_nonempty_iso_finBiproduct_obj weight
    exact ⟨(T.chosenDecompositionIso (biprod X Y)).symm.trans eCombined⟩
  rw [hchosen, Fin.sum_univ_add]
  simp only [combined, Fin.append_left, Fin.append_right]
  rfl

/-- Every integer-valued weight on the chosen indecomposable labels extends
canonically (up to the irrelevant decomposition choice) to an
isomorphism-invariant additive object weight. -/
noncomputable def additiveObjectWeightOfLabelWeight
    (weight : Ind → ℤ) : AdditiveObjectWeight C where
  weight := T.chosenLabelWeight weight
  iso_invariant := T.chosenLabelWeight_iso_invariant weight
  biprod_additive := T.chosenLabelWeight_biprod_additive weight

@[simp]
theorem additiveObjectWeightOfLabelWeight_obj
    (weight : Ind → ℤ) (A : Ind) :
    (T.additiveObjectWeightOfLabelWeight weight).weight (T.obj A) =
      weight A := by
  let eOne : T.obj A ≅ ⨁ fun _ : Fin 1 ↦ T.obj A :=
    (biproductUniqueIso (fun _ : Fin 1 ↦ T.obj A)).symm
  change T.chosenLabelWeight weight (T.obj A) = weight A
  have h := T.sum_weight_eq_of_nonempty_iso_finBiproduct_obj weight
    (T.chosenDecompositionSize (T.obj A)) 1
    (T.chosenDecompositionLabel (T.obj A)) (fun _ ↦ A)
    ⟨(T.chosenDecompositionIso (T.obj A)).symm.trans eOne⟩
  simpa [chosenLabelWeight, Fin.sum_univ_succ] using h

end FiniteRightTauCategoryData

end MBDVendor.QSE.Iyama
