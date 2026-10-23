module

public import MultiplicativeBasisDeformations.Foundations.CoverCategory

/-!
# Lemma 4.10: the support poset of a thin module

`lem:thin-module-incidence` (`scalar-normalization.tex`): "Let `T` be a
finite directed category, and let `M` be a covariant or contravariant `k`-linear
functor from `T` to vector spaces with `dim M(y) ≤ 1` for every object `y`. Let
`R` be the category obtained from `T` by passing to the quotient by the
annihilator of `M` and discarding the objects `y` with `M(y) = 0`. Then `R` is
the incidence category of a finite poset. If `T` is representation-finite,
then so is `R`."

For `M = T(s, -)` (a source, covariant) and `M = T(-, t)` (a sink,
contravariant) in the graded covering category, the passage to `R` is the
surjective algebra map from the category algebra of the support (Lemma 4.7) to
the incidence algebra, sending a morphism to its action on `M`
(`qSrc`, `qSnk`). Hence the incidence algebra is representation-finite
(Lemma 4.6 applied to the quotient).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory Opposite

namespace MultiplicativeBasisDeformations

universe u v

/-- The incidence algebra of a finite poset is finite-dimensional. -/
theorem incidence_finiteDimensional {k : Type u} [Field k] {P : Type*} [PartialOrder P]
    [Fintype P] [DecidableEq P] [LocallyFiniteOrder P] :
    FiniteDimensional k (IncidenceAlgebra k P) := by
  let f : IncidenceAlgebra k P →ₗ[k] (P → P → k) :=
    { toFun := fun a ↦ ⇑a
      map_add' := fun a b ↦ rfl
      map_smul' := fun c a ↦ rfl }
  exact Module.Finite.of_injective f fun a b h ↦ DFunLike.coe_injective h

namespace CatAlg

variable {k : Type u} [Field k] [Infinite k] {𝒞 : Type v} [Category.{u} 𝒞] [Preadditive 𝒞]
  [Linear k 𝒞] {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G]
  [DecidableEq G] {D : HomGrading (k := k) F G} (H : HeightData D)
  [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ)

/-! ### Sources -/

section Source

variable (s : CovObj D) (P : Finset (CovObj D)) (fv : ∀ y : CovObj D, s ⟶ y)
  (hfv : ∀ y ∈ P, fv y ≠ 0)

/-- The objects of the support, as objects of the graded covering category. -/
abbrev labSrc : Thin.SupP s P fv → ι × G := fun y ↦ y.1

/-- An entry of an element of the covering algebra of the support, as a morphism
of the graded covering category. -/
def entry (a : cov D (labSrc s P fv)) (y z : Thin.SupP s P fv) : y.1 ⟶ z.1 :=
  ⟨(a : (Alg (F ∘ lab (labSrc s P fv)))ᵐᵒᵖ).unop y z,
    (HomGrading.mem_part_iff (D := D)).2 (a.2 y z)⟩

include hfv in
/-- The action on `M = T(s, -)`. -/
def qSrcFun (a : cov D (labSrc s P fv)) :
    Thin.SupP s P fv → Thin.SupP s P fv → k := fun z y ↦
  Thin.coef (isThin H hF) (fv z.1) (fv y.1 ≫ entry s P fv a y z)

theorem entry_add (a b : cov D (labSrc s P fv)) (y z : Thin.SupP s P fv) :
    entry s P fv (a + b) y z = entry s P fv a y z + entry s P fv b y z := rfl

theorem entry_smul (c : k) (a : cov D (labSrc s P fv)) (y z : Thin.SupP s P fv) :
    entry s P fv (c • a) y z = c • entry s P fv a y z := rfl

theorem entry_mul (a b : cov D (labSrc s P fv)) (y w : Thin.SupP s P fv) :
    entry s P fv (a * b) y w = ∑ z, entry s P fv b y z ≫ entry s P fv a z w := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  rfl

theorem entry_one (y z : Thin.SupP s P fv) :
    entry s P fv 1 y z = if h : y = z then eqToHom (by rw [h]) else 0 := by
  apply Subtype.ext
  change idTo (F := F ∘ lab (labSrc s P fv)) y z = _
  by_cases h : y = z
  · subst h; simp [idTo]
  · simp [idTo, h]

variable {s P fv}

theorem coef_entry_eq_zero {y z : Thin.SupP s P fv}
    (h : ¬ Thin.supLe y z) (a : cov D (labSrc s P fv)) :
    fv y.1 ≫ entry s P fv a y z = 0 := by
  by_contra h'
  exact h (Or.inr ⟨_, h'⟩)

variable (s P fv)

include hfv in
/-- **Lemma 4.10 for a source**: the incidence algebra of the dual support poset
is representation-finite, through the algebra map given by the action on
`T(s, -)`. -/
theorem supRepFinite_src : Thin.SupRepFinite (isThin H hF) hfv := by
  classical
  have hT := isThin H hF
  unfold Thin.SupRepFinite
  letI : PartialOrder (Thin.SupP s P fv) := Thin.supOrder (isThin H hF) hfv
  letI : LocallyFiniteOrder (Thin.SupP s P fv) := Fintype.toLocallyFiniteOrder
  right
  have hz : ∀ (a : cov D (labSrc s P fv)) (y z : Thin.SupP s P fv), ¬ y ≤ z →
      qSrcFun H hF s P fv a z y = 0 := fun a y z h ↦ by
    unfold qSrcFun
    rw [coef_entry_eq_zero h a]
    exact Thin.coef_zero hT (hfv _ z.2)
  let qf : cov D (labSrc s P fv) → IncidenceAlgebra k (Thin.SupP s P fv)ᵒᵈ := fun a ↦
    ⟨fun z' y' ↦ qSrcFun H hF s P fv a (OrderDual.ofDual z') (OrderDual.ofDual y'),
      fun z' y' h ↦ hz a _ _ h⟩
  have hqf : ∀ a z' y', qf a z' y' =
      qSrcFun H hF s P fv a (OrderDual.ofDual z') (OrderDual.ofDual y') := fun _ _ _ ↦ rfl
  have hadd : ∀ a b, qf (a + b) = qf a + qf b := fun a b ↦ by
    apply IncidenceAlgebra.ext; intro z' y' _
    rw [IncidenceAlgebra.add_apply, hqf, hqf, hqf]
    unfold qSrcFun
    rw [entry_add, Preadditive.comp_add, Thin.coef_add hT (hfv _ (OrderDual.ofDual z').2)]
  have hsmul : ∀ (c : k) a, qf (c • a) = c • qf a := fun c a ↦ by
    apply IncidenceAlgebra.ext; intro z' y' _
    rw [IncidenceAlgebra.constSMul_apply, hqf, hqf]
    unfold qSrcFun
    rw [entry_smul, Linear.comp_smul, Thin.coef_smul hT (hfv _ (OrderDual.ofDual z').2), smul_eq_mul]
  have hone : qf 1 = 1 := by
    apply IncidenceAlgebra.ext; intro z' y' _
    rw [hqf, IncidenceAlgebra.one_apply]
    unfold qSrcFun
    rw [entry_one]
    by_cases h : OrderDual.ofDual y' = OrderDual.ofDual z'
    · have h' : z' = y' := by
        apply OrderDual.ofDual.injective; exact h.symm
      subst h'
      simp only [dif_pos rfl, if_pos rfl, eqToHom_refl, Category.comp_id]
      exact Thin.coef_self hT (hfv _ (OrderDual.ofDual z').2)
    · have h' : ¬ z' = y' := fun h' ↦ h (by rw [h'])
      simp only [dif_neg h, if_neg h', Limits.comp_zero]
      exact Thin.coef_zero hT (hfv _ (OrderDual.ofDual z').2)
  have hmul : ∀ a b, qf (a * b) = qf a * qf b := fun a b ↦ by
    apply IncidenceAlgebra.ext; intro z' y' _
    rw [IncidenceAlgebra.mul_apply, hqf]
    unfold qSrcFun
    rw [entry_mul, Preadditive.comp_sum, Thin.coef_sum hT (hfv _ (OrderDual.ofDual z').2)]
    symm
    rw [Finset.sum_subset (Finset.subset_univ (Finset.Icc z' y')) (fun x' _ hx ↦ by
      rw [Finset.mem_Icc, not_and_or] at hx
      rw [hqf, hqf]
      rcases hx with hx | hx
      · rw [hz a (OrderDual.ofDual x') (OrderDual.ofDual z') hx, zero_mul]
      · rw [hz b (OrderDual.ofDual y') (OrderDual.ofDual x') hx, mul_zero])]
    refine Finset.sum_congr rfl fun x' _ ↦ ?_
    rw [hqf, hqf]
    unfold qSrcFun
    rw [mul_comm]
    exact (Thin.coef_comp hT (hfv _ (OrderDual.ofDual y').2) (hfv _ (OrderDual.ofDual x').2)
      _ _ (hfv _ (OrderDual.ofDual z').2)).symm
  let q : cov D (labSrc s P fv) →ₐ[k] IncidenceAlgebra k (Thin.SupP s P fv)ᵒᵈ :=
    { toFun := qf
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have := hsmul 0 0; rwa [zero_smul, zero_smul] at this
      map_add' := hadd
      commutes' := fun c ↦ by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hsmul, hone] }
  -- surjectivity: normalized morphisms along the order
  have hnm : ∀ y z : Thin.SupP s P fv, y ≤ z → ∃ n : y.1 ⟶ z.1, fv y.1 ≫ n = fv z.1 := by
    intro y z hyz
    rcases hyz with rfl | ⟨g, hg⟩
    · exact ⟨𝟙 _, Category.comp_id _⟩
    · generalize hcd : Thin.coef hT (fv z.1) (fv y.1 ≫ g) = c
      have hc : fv y.1 ≫ g = c • fv z.1 := hcd ▸ Thin.coef_spec hT (hfv _ z.2) (fv y.1 ≫ g)
      have hc0 : c ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc; exact hg hc
      refine ⟨c⁻¹ • g, ?_⟩
      rw [Linear.comp_smul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  choose nm hnm using hnm
  have hsurj : Function.Surjective q := by
    intro i
    let A : Alg (F ∘ lab (labSrc s P fv)) := fun y z ↦
      if h : y ≤ z then (i (OrderDual.toDual z) (OrderDual.toDual y) • nm y z h).1 else 0
    have hA : MulOpposite.op A ∈ cov D (labSrc s P fv) := by
      intro y z
      change D.IsHom _ (A y z)
      simp only [A]
      split_ifs with h
      · exact D.isHom_smul _ ((HomGrading.mem_part_iff (D := D)).1 (nm y z h).2)
      · exact D.isHom_zero _
    refine ⟨⟨_, hA⟩, ?_⟩
    apply IncidenceAlgebra.ext; intro z' y' hzy
    change qf _ z' y' = _
    rw [hqf]
    unfold qSrcFun
    have hle : OrderDual.ofDual y' ≤ OrderDual.ofDual z' := hzy
    have hent : entry s P fv ⟨_, hA⟩ (OrderDual.ofDual y') (OrderDual.ofDual z') =
        i z' y' • nm _ _ hle := by
      apply Subtype.ext
      change A _ _ = _
      simp only [A, dif_pos hle]
      rfl
    rw [hent, Linear.comp_smul, hnm, Thin.coef_smul hT (hfv _ (OrderDual.ofDual z').2),
      Thin.coef_self hT (hfv _ (OrderDual.ofDual z').2), mul_one]
  haveI : FiniteDimensional k (IncidenceAlgebra k (Thin.SupP s P fv)ᵒᵈ) :=
    incidence_finiteDimensional
  exact splitRepresentationTransfer_of (C := ⊤) (q := q.comp (Subalgebra.val ⊤)) q.toLinearMap
    (fun c c' b ↦ by simp [map_mul]) (fun d ↦ by
      obtain ⟨a, ha⟩ := hsurj d; exact ⟨⟨a, trivial⟩, ha⟩) (fun c ↦ rfl)
    (isRepresentationFinite_cov D (labSrc s P fv) hF)

end Source

/-! ### Sinks -/

section Sink

attribute [local instance] Thin.opLinear

variable (t : CovObj D) (P : Finset (CovObj D)ᵒᵖ) (fv : ∀ Y : (CovObj D)ᵒᵖ, op t ⟶ Y)
  (hfv : ∀ Y ∈ P, fv Y ≠ 0)

/-- The objects of the support of `T(-, t)`. -/
abbrev labSnk : Thin.SupP (op t) P fv → ι × G := fun Y ↦ unop Y.1

/-- An entry of an element of the covering algebra. -/
def entryK (a : cov D (labSnk t P fv)) (Y Z : Thin.SupP (op t) P fv) :
    (unop Y.1 : CovObj D) ⟶ unop Z.1 :=
  ⟨(a : (Alg (F ∘ lab (labSnk t P fv)))ᵐᵒᵖ).unop Y Z,
    (HomGrading.mem_part_iff (D := D)).2 (a.2 Y Z)⟩

theorem entryK_add (a b : cov D (labSnk t P fv)) (Y Z : Thin.SupP (op t) P fv) :
    entryK t P fv (a + b) Y Z = entryK t P fv a Y Z + entryK t P fv b Y Z := rfl

theorem entryK_smul (c : k) (a : cov D (labSnk t P fv)) (Y Z : Thin.SupP (op t) P fv) :
    entryK t P fv (c • a) Y Z = c • entryK t P fv a Y Z := rfl

theorem entryK_mul (a b : cov D (labSnk t P fv)) (Y W : Thin.SupP (op t) P fv) :
    entryK t P fv (a * b) Y W = ∑ Z, entryK t P fv b Y Z ≫ entryK t P fv a Z W := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  rfl

theorem entryK_one (Y Z : Thin.SupP (op t) P fv) :
    entryK t P fv 1 Y Z = if h : Y = Z then eqToHom (by rw [h]) else 0 := by
  apply Subtype.ext
  change idTo (F := F ∘ lab (labSnk t P fv)) Y Z = _
  by_cases h : Y = Z
  · subst h; simp [idTo]
  · simp [idTo, h]

/-- The map `φ_Y : Y → t`. -/
def φK (Y : Thin.SupP (op t) P fv) : (unop Y.1 : CovObj D) ⟶ t := (fv Y.1).unop

/-- The action on `M = T(-, t)`. -/
def qSnkFun (a : cov D (labSnk t P fv)) :
    Thin.SupP (op t) P fv → Thin.SupP (op t) P fv → k := fun Y Z ↦
  Thin.coef (isThin H hF) (φK t P fv Z) (entryK t P fv a Z Y ≫ φK t P fv Y)

include hfv in
theorem φK_ne (Y : Thin.SupP (op t) P fv) : φK t P fv Y ≠ 0 := fun h ↦
  hfv _ Y.2 (Quiver.Hom.unop_inj h)

variable {t P fv}

theorem le_of_comp_ne {Y Z : Thin.SupP (op t) P fv} (h : (unop Z.1 : CovObj D) ⟶ unop Y.1)
    (hne : h ≫ φK t P fv Y ≠ 0) : Thin.supLe Y Z :=
  Or.inr ⟨h.op, fun h0 ↦ hne (by
    have := congrArg Quiver.Hom.unop h0
    exact this)⟩

theorem comp_ne_of_le {Y Z : Thin.SupP (op t) P fv} (g : Y.1 ⟶ Z.1) (hg : fv Y.1 ≫ g ≠ 0) :
    g.unop ≫ φK t P fv Y ≠ 0 := fun h0 ↦ hg (Quiver.Hom.unop_inj h0)

variable (t P fv)

include hfv in
/-- **Lemma 4.10 for a sink**: the incidence algebra of the support poset of
`T(-, t)` (as a source of the opposite category) is representation-finite. -/
theorem supRepFinite_snk : Thin.SupRepFinite (Thin.isThin_op (isThin H hF)) hfv := by
  classical
  have hT := isThin H hF
  unfold Thin.SupRepFinite
  letI : PartialOrder (Thin.SupP (op t) P fv) := Thin.supOrder (Thin.isThin_op (isThin H hF)) hfv
  letI : LocallyFiniteOrder (Thin.SupP (op t) P fv) := Fintype.toLocallyFiniteOrder
  left
  have hφ := φK_ne t P fv hfv
  have hz : ∀ (a : cov D (labSnk t P fv)) (Y Z : Thin.SupP (op t) P fv), ¬ Y ≤ Z →
      qSnkFun H hF t P fv a Y Z = 0 := fun a Y Z h ↦ by
    unfold qSnkFun
    by_cases h0 : entryK t P fv a Z Y ≫ φK t P fv Y = 0
    · rw [h0]; exact Thin.coef_zero hT (hφ Z)
    · exact absurd (le_of_comp_ne _ h0) h
  let qf : cov D (labSnk t P fv) → IncidenceAlgebra k (Thin.SupP (op t) P fv) := fun a ↦
    ⟨fun Y Z ↦ qSnkFun H hF t P fv a Y Z, fun Y Z h ↦ hz a Y Z h⟩
  have hqf : ∀ a Y Z, qf a Y Z = qSnkFun H hF t P fv a Y Z := fun _ _ _ ↦ rfl
  have hadd : ∀ a b, qf (a + b) = qf a + qf b := fun a b ↦ by
    apply IncidenceAlgebra.ext; intro Y Z _
    rw [IncidenceAlgebra.add_apply, hqf, hqf, hqf]
    unfold qSnkFun
    rw [entryK_add, Preadditive.add_comp, Thin.coef_add hT (hφ Z)]
  have hsmul : ∀ (c : k) a, qf (c • a) = c • qf a := fun c a ↦ by
    apply IncidenceAlgebra.ext; intro Y Z _
    rw [IncidenceAlgebra.constSMul_apply, hqf, hqf]
    unfold qSnkFun
    rw [entryK_smul, Linear.smul_comp, Thin.coef_smul hT (hφ Z), smul_eq_mul]
  have hone : qf 1 = 1 := by
    apply IncidenceAlgebra.ext; intro Y Z _
    rw [hqf, IncidenceAlgebra.one_apply]
    unfold qSnkFun
    rw [entryK_one]
    by_cases h : Z = Y
    · subst h
      simp only [dif_pos rfl, if_pos rfl, eqToHom_refl, Category.id_comp]
      exact Thin.coef_self hT (hφ Z)
    · have h' : ¬ Y = Z := fun h' ↦ h h'.symm
      simp only [dif_neg h, if_neg h', Limits.zero_comp]
      exact Thin.coef_zero hT (hφ Z)
  have hmul : ∀ a b, qf (a * b) = qf a * qf b := fun a b ↦ by
    apply IncidenceAlgebra.ext; intro Y W _
    rw [IncidenceAlgebra.mul_apply, hqf]
    unfold qSnkFun
    rw [entryK_mul, Preadditive.sum_comp, Thin.coef_sum hT (hφ W)]
    symm
    rw [Finset.sum_subset (Finset.subset_univ (Finset.Icc Y W)) (fun Z _ hZ ↦ by
      rw [Finset.mem_Icc, not_and_or] at hZ
      rw [hqf, hqf]
      rcases hZ with hZ | hZ
      · rw [hz a Y Z hZ, zero_mul]
      · rw [hz b Z W hZ, mul_zero])]
    refine Finset.sum_congr rfl fun Z _ ↦ ?_
    rw [hqf, hqf]
    unfold qSnkFun
    rw [Category.assoc]
    exact (Thin.coef_comp_right hT (hφ Z) (hφ W) _ _).symm
  let q : cov D (labSnk t P fv) →ₐ[k] IncidenceAlgebra k (Thin.SupP (op t) P fv) :=
    { toFun := qf
      map_one' := hone
      map_mul' := hmul
      map_zero' := by
        have := hsmul 0 0; rwa [zero_smul, zero_smul] at this
      map_add' := hadd
      commutes' := fun c ↦ by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, hsmul, hone] }
  have hnm : ∀ Y Z : Thin.SupP (op t) P fv, Y ≤ Z →
      ∃ n : (unop Z.1 : CovObj D) ⟶ unop Y.1, n ≫ φK t P fv Y = φK t P fv Z := by
    intro Y Z hYZ
    rcases hYZ with rfl | ⟨g, hg⟩
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · have hg' := comp_ne_of_le g hg
      generalize hcd : Thin.coef hT (φK t P fv Z) (g.unop ≫ φK t P fv Y) = c
      have hc : g.unop ≫ φK t P fv Y = c • φK t P fv Z :=
        hcd ▸ Thin.coef_spec hT (hφ Z) _
      have hc0 : c ≠ 0 := by
        intro h0; rw [h0, zero_smul] at hc; exact hg' hc
      refine ⟨c⁻¹ • g.unop, ?_⟩
      rw [Linear.smul_comp, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  choose nm hnm using hnm
  have hsurj : Function.Surjective q := by
    intro i
    let A : Alg (F ∘ lab (labSnk t P fv)) := fun p r ↦
      if h : r ≤ p then (i r p • nm r p h).1 else 0
    have hA : MulOpposite.op A ∈ cov D (labSnk t P fv) := by
      intro p r
      change D.IsHom _ (A p r)
      simp only [A]
      split_ifs with h
      · exact D.isHom_smul _ ((HomGrading.mem_part_iff (D := D)).1 (nm r p h).2)
      · exact D.isHom_zero _
    refine ⟨⟨_, hA⟩, ?_⟩
    apply IncidenceAlgebra.ext; intro Y Z hYZ
    change qf _ Y Z = _
    rw [hqf]
    unfold qSnkFun
    have hent : entryK t P fv ⟨_, hA⟩ Z Y = i Y Z • nm Y Z hYZ := by
      apply Subtype.ext
      change A _ _ = _
      simp only [A, dif_pos hYZ]
    rw [hent, Linear.smul_comp, hnm, Thin.coef_smul hT (hφ Z), Thin.coef_self hT (hφ Z), mul_one]
  haveI : FiniteDimensional k (IncidenceAlgebra k (Thin.SupP (op t) P fv)) :=
    incidence_finiteDimensional
  exact splitRepresentationTransfer_of (C := ⊤) (q := q.comp (Subalgebra.val ⊤)) q.toLinearMap
    (fun c c' b ↦ by simp [map_mul]) (fun d ↦ by
      obtain ⟨a, ha⟩ := hsurj d; exact ⟨⟨a, trivial⟩, ha⟩) (fun c ↦ rfl)
    (isRepresentationFinite_cov D (labSnk t P fv) hF)

end Sink

end CatAlg

end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations.CatAlg

open CategoryTheory Opposite

universe u v

variable {k : Type u} [Field k] [Infinite k] {𝒞 : Type v} [Category.{u} 𝒞] [Preadditive 𝒞]
  [Linear k 𝒞] {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G]
  [DecidableEq G] {D : HomGrading (k := k) F G} (H : HeightData D)
  [∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] (hF : IsRepresentationFinite k (Alg F)ᵐᵒᵖ)

attribute [local instance] Thin.opLinear

include H hF in
/-- **Lemma 4.12** for the graded covering category: it has a multiplicative
basis. -/
theorem cov_exists_multBasis [Countable G] :
    ∃ β : ∀ o o' : CovObj D, o ⟶ o', Thin.MultBasis Set.univ β := by
  classical
  have hT := isThin H hF
  by_cases hne : Nonempty (CovObj D)
  · haveI : Countable (CovObj D) := inferInstanceAs (Countable (ι × G))
    obtain ⟨e, he⟩ := exists_surjective_nat (CovObj D)
    exact Thin.exists_multBasis hT (hgtC H) (fun o o' h ↦ hgt_lt H h)
      (fun s S ↦ supRepFinite_src H hF s (Thin.supp s S) (Thin.fvec s) _)
      (fun t S ↦ supRepFinite_snk H hF t (Thin.supp (op t) (S.map Thin.opEmb)) (Thin.fvec (op t)) _)
      (fun o ↦ succ_finite o) e he
  · rw [not_nonempty_iff] at hne
    exact ⟨fun o _ ↦ isEmptyElim o, ⟨fun o ↦ isEmptyElim o, fun o ↦ isEmptyElim o,
      fun o ↦ isEmptyElim o⟩⟩

end MultiplicativeBasisDeformations.CatAlg
