import Mathlib.Logic.Equiv.Fin.Basic
import MBDVendor.QSE.CategoryTheory.IyamaKrullSchmidtNormalForm
import MBDVendor.QSE.CategoryTheory.IyamaNakayamaBoundary

/-!
# Finite Krull--Schmidt cancellation and direct finiteness

Displayed decompositions into the chosen indecomposable skeleton have a
well-defined total number of summands.  Consequently every split-monic
endomorphism is invertible.  This is the categorical direct-finiteness input
used in Iyama's ladder comparison.
-/

set_option autoImplicit false

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace MBDVendor.QSE.Iyama

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  [IsIdempotentComplete C]
variable {Ind : Type w} [Fintype Ind]

namespace FiniteRightTauCategoryData

variable (T : FiniteRightTauCategoryData C Ind)

/-- A retraction of a chosen indecomposable from a finite biproduct has an
invertible coordinate. -/
theorem exists_isIso_component_of_retraction_finBiproduct
    (p : Ind) (n : ℕ) (label : Fin n → Ind)
    (f : T.obj p ⟶ ⨁ fun i ↦ T.obj (label i))
    (g : (⨁ fun i ↦ T.obj (label i)) ⟶ T.obj p)
    (hfg : f ≫ g = 𝟙 (T.obj p)) :
    ∃ i : Fin n,
      IsIso (f ≫ biproduct.π (fun j ↦ T.obj (label j)) i) := by
  classical
  let c : Fin n → End (T.obj p) := fun i ↦
    ((f ≫ biproduct.π (fun j ↦ T.obj (label j)) i) ≫
      (biproduct.ι (fun j ↦ T.obj (label j)) i ≫ g) :
        End (T.obj p))
  have hsum : ∑ i : Fin n, c i = 𝟙 (T.obj p) := by
    change
      ∑ i : Fin n,
        ((f ≫ biproduct.π (fun j ↦ T.obj (label j)) i) ≫
          (biproduct.ι (fun j ↦ T.obj (label j)) i ≫ g) :
            End (T.obj p)) =
        (𝟙 (T.obj p) : End (T.obj p))
    calc
      ∑ i : Fin n,
          ((f ≫ biproduct.π (fun j ↦ T.obj (label j)) i) ≫
            (biproduct.ι (fun j ↦ T.obj (label j)) i ≫ g) :
              End (T.obj p)) =
          f ≫ (∑ i : Fin n,
            biproduct.π (fun j ↦ T.obj (label j)) i ≫
              biproduct.ι (fun j ↦ T.obj (label j)) i) ≫ g := by
        simp only [Category.assoc, Preadditive.comp_sum,
          Preadditive.sum_comp]
      _ = f ≫ g := by
        rw [biproduct.total]
        simp
      _ = 𝟙 (T.obj p) := hfg
  letI : IsLocalRing (End (T.obj p)) := T.obj_end_local p
  have hunit : IsUnit (∑ i : Fin n, c i) := by
    rw [hsum]
    exact isUnit_one
  obtain ⟨i, _, hi⟩ :=
    IsLocalRing.exists_of_isUnit_sum
      (s := Finset.univ) (f := c) hunit
  let a : T.obj p ⟶ T.obj (label i) :=
    f ≫ biproduct.π (fun j ↦ T.obj (label j)) i
  let b : T.obj (label i) ⟶ T.obj p :=
    biproduct.ι (fun j ↦ T.obj (label j)) i ≫ g
  have habI : IsIso (a ≫ b) := by
    apply (isUnit_iff_isIso (a ≫ b)).1
    simpa only [c, a, b] using hi
  letI : IsIso (a ≫ b) := habI
  have haSplit : IsSplitMono a := by
    apply IsSplitMono.mk'
    refine
      { retraction := b ≫ inv (a ≫ b)
        id := ?_ }
    rw [← Category.assoc, IsIso.hom_inv_id]
  letI : IsSplitMono a := haSplit
  have haIso : IsIso a :=
    FiniteRightTauCategoryData.isIso_of_isSplitMono_obj_obj T a
  exact ⟨i, by simpa only [a] using haIso⟩

/-- Two displayed finite biproducts of the chosen indecomposables can be
isomorphic only when they have the same number of summands. -/
theorem eq_of_nonempty_iso_finBiproduct_obj :
    ∀ (n m : ℕ) (source : Fin n → Ind) (target : Fin m → Ind),
      Nonempty
        ((⨁ fun i ↦ T.obj (source i)) ≅
          ⨁ fun j ↦ T.obj (target j)) →
        n = m := by
  intro n
  induction n with
  | zero =>
      intro m source target e
      cases m with
      | zero => rfl
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
            FiniteRightTauCategoryData.exists_isIso_component_of_retraction_finBiproduct T
              (source 0) (m + 1) target f g hfg
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
          have hnm : n = m :=
            ih m (fun i ↦ source i.succ)
              (fun k ↦ target (σ k.succ)) ⟨eTail⟩
          exact congrArg Nat.succ hnm

/-- A binary biproduct of two finite biproducts is the biproduct indexed by
the sum of their index types. -/
noncomputable def finBiproductBiprodIsoSum
    {n m : ℕ} (F : Fin n → C) (G : Fin m → C) :
    (⨁ F) ⊞ (⨁ G) ≅ ⨁ Sum.elim F G := by
  classical
  let eF (i : Fin n) : (Sum.elim F G) (Sum.inl i) ≅ F i :=
    eqToIso (by rfl)
  let eG (j : Fin m) : (Sum.elim F G) (Sum.inr j) ≅ G j :=
    eqToIso (by rfl)
  let b : Bicone (Sum.elim F G) :=
    { pt := (⨁ F) ⊞ (⨁ G)
      π := fun s ↦ match s with
        | Sum.inl i => biprod.fst ≫ biproduct.π F i ≫ (eF i).inv
        | Sum.inr j => biprod.snd ≫ biproduct.π G j ≫ (eG j).inv
      ι := fun s ↦ match s with
        | Sum.inl i => (eF i).hom ≫ biproduct.ι F i ≫ biprod.inl
        | Sum.inr j => (eG j).hom ≫ biproduct.ι G j ≫ biprod.inr
      ι_π := by
        intro s t
        rcases s with i | j <;> rcases t with i' | j'
        · by_cases h : i = i'
          · subst i'
            simp [eF, Category.assoc]
          · simp [eF, Category.assoc, h]
            rfl
        · simp [eF, eG, Category.assoc]
          rfl
        · simp [eF, eG, Category.assoc]
          rfl
        · by_cases h : j = j'
          · subst j'
            simp [eG, Category.assoc]
          · simp [eG, Category.assoc, h]
            rfl
      }
  have hleft :
      ∑ i : Fin n,
          ((biprod.fst : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ F) ≫
              biproduct.π F i ≫ (eF i).inv) ≫
            ((eF i).hom ≫ biproduct.ι F i ≫
              (biprod.inl : (⨁ F) ⟶ (⨁ F) ⊞ (⨁ G))) =
        (biprod.fst : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ F) ≫
          (biprod.inl : (⨁ F) ⟶ (⨁ F) ⊞ (⨁ G)) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    calc
      ∑ i : Fin n,
          (biprod.fst : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ F) ≫
            biproduct.π F i ≫ biproduct.ι F i ≫
              (biprod.inl : (⨁ F) ⟶ (⨁ F) ⊞ (⨁ G)) =
          (biprod.fst : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ F) ≫
          (∑ i : Fin n, biproduct.π F i ≫ biproduct.ι F i) ≫
            (biprod.inl : (⨁ F) ⟶ (⨁ F) ⊞ (⨁ G)) := by
        simp only [Category.assoc, Preadditive.comp_sum,
          Preadditive.sum_comp]
      _ = (biprod.fst : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ F) ≫
          (biprod.inl : (⨁ F) ⟶ (⨁ F) ⊞ (⨁ G)) := by
        rw [biproduct.total]
        simp
  have hright :
      ∑ j : Fin m,
          ((biprod.snd : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ G) ≫
              biproduct.π G j ≫ (eG j).inv) ≫
            ((eG j).hom ≫ biproduct.ι G j ≫
              (biprod.inr : (⨁ G) ⟶ (⨁ F) ⊞ (⨁ G))) =
        (biprod.snd : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ G) ≫
          (biprod.inr : (⨁ G) ⟶ (⨁ F) ⊞ (⨁ G)) := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    calc
      ∑ j : Fin m,
          (biprod.snd : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ G) ≫
            biproduct.π G j ≫ biproduct.ι G j ≫
              (biprod.inr : (⨁ G) ⟶ (⨁ F) ⊞ (⨁ G)) =
          (biprod.snd : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ G) ≫
          (∑ j : Fin m, biproduct.π G j ≫ biproduct.ι G j) ≫
            (biprod.inr : (⨁ G) ⟶ (⨁ F) ⊞ (⨁ G)) := by
        simp only [Category.assoc, Preadditive.comp_sum,
          Preadditive.sum_comp]
      _ = (biprod.snd : (⨁ F) ⊞ (⨁ G) ⟶ ⨁ G) ≫
          (biprod.inr : (⨁ G) ⟶ (⨁ F) ⊞ (⨁ G)) := by
        rw [biproduct.total]
        simp
  have htotal : ∑ s, b.π s ≫ b.ι s = 𝟙 b.pt := by
    rw [Fintype.sum_sum_type]
    change
      (∑ i : Fin n,
          (biprod.fst ≫ biproduct.π F i ≫ (eF i).inv) ≫
            ((eF i).hom ≫ biproduct.ι F i ≫ biprod.inl)) +
        (∑ j : Fin m,
          (biprod.snd ≫ biproduct.π G j ≫ (eG j).inv) ≫
            ((eG j).hom ≫ biproduct.ι G j ≫ biprod.inr)) =
          𝟙 ((⨁ F) ⊞ (⨁ G))
    rw [hleft, hright, biprod.total]
  let hb : b.IsBilimit := isBilimitOfTotal b htotal
  change b.pt ≅ ⨁ Sum.elim F G
  exact hb.isLimit.conePointUniqueUpToIso
    (biproduct.isLimit (Sum.elim F G))

include T in
/-- A split-monic endomorphism is invertible in the finite Krull--Schmidt
category recorded by `FiniteTauCategoryData`. -/
theorem isIso_of_isSplitMono_end
    {X : C} (f : X ⟶ X) [IsSplitMono f] : IsIso f := by
  classical
  let d := MBDVendor.QSE.splitMonoComplement f
  let eSplit : X ≅ X ⊞ d.complement :=
    d.isBilimitBinaryBicone.isLimit.conePointUniqueUpToIso
      (BinaryBiproduct.isLimit _ _)
  obtain ⟨n, label, ⟨eX⟩⟩ := T.obj_decomposition X
  obtain ⟨m, labelD, ⟨eD⟩⟩ := T.obj_decomposition d.complement
  let F : Fin n → C := fun i ↦ T.obj (label i)
  let G : Fin m → C := fun j ↦ T.obj (labelD j)
  let combined : Fin (n + m) → Ind := Fin.append label labelD
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
  let eBig :
      (⨁ fun i ↦ T.obj (label i)) ≅
        ⨁ fun k ↦ T.obj (combined k) :=
    eX.symm.trans
      (eSplit.trans
        ((biprod.mapIso eX eD).trans
          ((finBiproductBiprodIsoSum F G).trans eFlatten)))
  have hlength : n = n + m :=
    FiniteRightTauCategoryData.eq_of_nonempty_iso_finBiproduct_obj T
      n (n + m) label combined ⟨eBig⟩
  have hm : m = 0 := by
    have h : n + 0 = n + m := by simpa using hlength
    exact (Nat.add_left_cancel h).symm
  subst m
  have hzeroSum : IsZero (⨁ fun j : Fin 0 ↦ T.obj (labelD j)) := by
    rw [IsZero.iff_id_eq_zero]
    apply biproduct.hom_ext
    intro j
    exact Fin.elim0 j
  have hzeroD : IsZero d.complement := hzeroSum.of_iso eD
  apply IsIso.mk
  refine ⟨retraction f, IsSplitMono.id f, ?_⟩
  rw [← d.total]
  have hp : d.projection = 0 := hzeroD.eq_of_tgt _ _
  have hi : d.inclusion = 0 := hzeroD.eq_of_src _ _
  rw [hp, hi, zero_comp, add_zero]

end FiniteRightTauCategoryData

end MBDVendor.QSE.Iyama
