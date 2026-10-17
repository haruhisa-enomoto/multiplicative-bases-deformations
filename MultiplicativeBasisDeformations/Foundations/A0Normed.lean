import MultiplicativeBasisDeformations.Foundations.ScalarNormalization
import MultiplicativeBasisDeformations.Foundations.GradedLayers

/-!
# `A₀` has a normed multiplicative basis

Proposition 4.14 (`scalar-normalization.tex:644–646`): "The endpoint chains and
Corollary 3.3 show that the intersection of the resulting basis with each radical
power is a basis of that power."

The path-length grading of the scalar mesh category grades `A₀ = (Alg F₀)ᵒᵖ`
(`lenA0`); the basis of Proposition 4.14 consists of homogeneous elements of
corners, so by the layer argument (`GradedLayers.lean`) it is adapted to every
radical power, and `A₀` has a normed multiplicative basis (`hasNormedBasis_A0`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

section RadicalPow

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

theorem algebraRadicalPow_mul_left {n : ℕ} (hn : 1 ≤ n) (a : A) {z : A}
    (hz : z ∈ algebraRadicalPow k A n) : a * z ∈ algebraRadicalPow k A n := by
  induction n, hn using Nat.le_induction generalizing a z with
  | base =>
      rw [algebraRadicalPow, pow_one] at hz ⊢
      exact Ideal.mul_mem_left (Ring.jacobson A) a hz
  | succ n hn ih =>
      rw [algebraRadicalPow, pow_succ] at hz ⊢
      refine Submodule.mul_induction_on hz (fun x hx y hy ↦ ?_) (fun x y hx hy ↦ ?_)
      · rw [← mul_assoc]; exact Submodule.mul_mem_mul (ih a hx) hy
      · rw [mul_add]; exact Submodule.add_mem _ hx hy

theorem algebraRadicalPow_mul_right {n : ℕ} (hn : 1 ≤ n) (a : A) {z : A}
    (hz : z ∈ algebraRadicalPow k A n) : z * a ∈ algebraRadicalPow k A n := by
  have hbase : ∀ {y : A}, y ∈ algebraRadical k A → y * a ∈ algebraRadical k A := fun {y} hy ↦ by
    change y * a ∈ Ring.jacobson A
    haveI : (Ring.jacobson A).IsTwoSided := inferInstance
    exact Ideal.mul_mem_right a (Ring.jacobson A) hy
  induction n, hn using Nat.le_induction generalizing z with
  | base =>
      rw [algebraRadicalPow, pow_one] at hz ⊢
      exact hbase hz
  | succ n hn ih =>
      rw [algebraRadicalPow, pow_succ] at hz ⊢
      refine Submodule.mul_induction_on hz (fun x hx y hy ↦ ?_) (fun x y hx hy ↦ ?_)
      · rw [mul_assoc]; exact Submodule.mul_mem_mul hx (hbase hy)
      · rw [add_mul]; exact Submodule.add_mem _ hx hy

end RadicalPow

namespace ScalarMeshCategory

variable {k : Type u} [Field k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)

theorem degProj_of_mem {d e : ℕ} {x y : V} {g : obj c x ⟶ obj c y} (hg : g ∈ degreePart c e x y) :
    degProj c d x y g = if e = d then g else 0 := by
  obtain ⟨F, hF, rfl⟩ := hg
  change degProj c d x y ((RelationCategory.functor k (meshRelations c)).map F) = _
  rw [degProj_apply, LinearPaths.proj_of_mem hF]
  split_ifs <;> simp

theorem degProj_mem (d : ℕ) {x y : V} (f : obj c x ⟶ obj c y) :
    degProj c d x y f ∈ degreePart c d x y := by
  obtain ⟨F, rfl⟩ := (RelationCategory.functor k (meshRelations c)).map_surjective f
  rw [degProj_apply]
  exact ⟨_, LinearPaths.proj_mem F, rfl⟩

theorem comp_mem_degreePart' {d e : ℕ} {x y z : V} {f : obj c x ⟶ obj c y}
    {g : obj c y ⟶ obj c z} (hf : f ∈ degreePart c d x y) (hg : g ∈ degreePart c e y z) :
    f ≫ g ∈ degreePart c (d + e) x z := by
  obtain ⟨F, hF, rfl⟩ := hf
  obtain ⟨G, hG, rfl⟩ := hg
  refine ⟨F ≫ G, LinearPaths.comp_mem_degreePart hF hG, ?_⟩
  change (RelationCategory.functor k (meshRelations c)).map (F ≫ G) = _
  rw [Functor.map_comp]
  rfl

theorem eq_sum_degProj {N : ℕ} (hN : ∀ d x y, N ≤ d → degreePart c d x y = ⊥) {x y : V}
    (f : obj c x ⟶ obj c y) : f = ∑ d ∈ Finset.range N, degProj c d x y f := by
  obtain ⟨F, rfl⟩ := (RelationCategory.functor k (meshRelations c)).map_surjective f
  obtain ⟨M, hM⟩ := LinearPaths.eq_sum_proj_of_le (k := k) F
  conv_lhs => rw [hM (max M N) (le_max_left _ _)]
  rw [Functor.map_sum]
  simp_rw [← degProj_apply]
  have hzero : ∀ d, N ≤ d →
      degProj c d x y ((RelationCategory.functor k (meshRelations c)).map F) = 0 := fun d hd ↦ by
    have := degProj_mem c d ((RelationCategory.functor k (meshRelations c)).map F)
    rwa [hN d x y hd, Submodule.mem_bot] at this
  rw [← Finset.sum_range_add_sum_Ico _ (le_max_right M N)]
  rw [Finset.sum_eq_zero (s := Finset.Ico N (max M N)) fun d hd ↦ hzero d (Finset.mem_Ico.1 hd).1,
    add_zero]

theorem degreePart_zero_eq {x : V} {f : obj c x ⟶ obj c x} (hf : f ∈ degreePart c 0 x x) :
    ∃ t : k, f = t • 𝟙 (obj c x) := by
  obtain ⟨F, hF, rfl⟩ := hf
  refine ⟨LinearPaths.toFinsupp F Quiver.Path.nil, ?_⟩
  conv_lhs => rw [LinearPaths.degreePart_zero_self hF]
  rw [map_smul]
  congr 1

theorem exists_degreePart_eq_bot [Finite V]
    (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)) :
    ∃ N : ℕ, ∀ d x y, N ≤ d → degreePart c d x y = ⊥ := by
  obtain ⟨N, hN⟩ := exists_pathMor_eq_zero c hfin
  refine ⟨N, fun d x y hd ↦ ?_⟩
  rw [degreePart_eq_span, eq_bot_iff, Submodule.span_le]
  rintro _ ⟨p, hp, rfl⟩
  exact hN x y p (hp ▸ hd)

end ScalarMeshCategory

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))

/-- The degree-`d` part of an element of `A₀`. -/
def projA0 (d : ℕ) : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ where
  toFun a := MulOpposite.op (fun p q ↦ degProj c d p.1 q.1 (a.unop p q))
  map_add' a b := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    exact map_add _ _ _
  map_smul' t a := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    change degProj c d p.1 q.1 (t • a.unop p q) = t • degProj c d p.1 q.1 (a.unop p q)
    exact map_smul _ _ _

theorem projA0_apply (d : ℕ) (a : (Alg D.F0)ᵐᵒᵖ) (p q : D.PV) :
    (projA0 D d a).unop p q = degProj c d p.1 q.1 (a.unop p q) := rfl

include hfin in
/-- **The length grading of `A₀`.** -/
def lenA0 : LenGrading k (Alg D.F0)ᵐᵒᵖ where
  proj := projA0 D
  N := Classical.choose (exists_degreePart_eq_bot c hfin)
  proj_proj d e a := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    rw [projA0_apply, projA0_apply, degProj_of_mem c (degProj_mem c e _)]
    split_ifs <;> rfl
  proj_ge d hd := by
    ext a
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    have := degProj_mem c d (a.unop p q)
    rw [Classical.choose_spec (exists_degreePart_eq_bot c hfin) d _ _ hd, Submodule.mem_bot] at this
    exact this
  sum a := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    rw [Finset.unop_sum, CatAlg.sum_apply]
    exact eq_sum_degProj c (Classical.choose_spec (exists_degreePart_eq_bot c hfin)) _
  mul_hom d e a b := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    rw [projA0_apply, MulOpposite.unop_mul, mul_apply, map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hmem : (projA0 D e b).unop p r ≫ (projA0 D d a).unop r q ∈
        degreePart c (d + e) p.1 q.1 := by
      rw [add_comm]
      exact comp_mem_degreePart' c (degProj_mem c e _) (degProj_mem c d _)
    rw [degProj_of_mem c hmem, if_pos rfl]

theorem idTo_mem_degreePart (p x : D.PV) :
    idTo (F := D.F0) p x ∈ degreePart c 0 p.1 x.1 := by
  by_cases h : p = x
  · subst h
    rw [idTo_self]
    have := pathMor_mem_degreePart c (Quiver.Path.nil : Quiver.Path p.1 p.1)
    rwa [pathMor_nil] at this
  · rw [idTo_ne h]; exact Submodule.zero_mem _

include hfin in
theorem unitM_isHom {d : ℕ} {x y : D.PV} {f : D.F0 x ⟶ D.F0 y} (hf : f ∈ degreePart c d x.1 y.1) :
    (lenA0 D hfin).IsHom d (MulOpposite.op (unitM x y f)) := by
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  change degProj c d p.1 q.1 (idTo (F := D.F0) p x ≫ f ≫ idTo (F := D.F0) y q) = _
  have hmem : idTo (F := D.F0) p x ≫ f ≫ idTo (F := D.F0) y q ∈ degreePart c d p.1 q.1 := by
    have := comp_mem_degreePart' c (idTo_mem_degreePart D p x)
      (comp_mem_degreePart' c hf (idTo_mem_degreePart D y q))
    rwa [zero_add, add_zero] at this
  rw [degProj_of_mem c hmem, if_pos rfl]
  rfl

theorem deck_part_le (v₀ : V) (g : Deck Q v₀) (x y : V) :
    (deckGrading Q c v₀).part g x y ≤ degreePart c (hgt Q v₀ g).toNat x y := by
  intro f hf
  rw [HomGrading.mem_part_iff, isHom_iff] at hf
  refine Submodule.span_le.2 ?_ (wPart_le_span Q c v₀ g x y hf)
  rintro _ ⟨p, hp, rfl⟩
  have := pathMor_mem_degreePart c p
  have hl := hgt_degW Q v₀ p
  rw [hp] at hl
  rwa [show (hgt Q v₀ g).toNat = p.length by omega]

/-! ### The normed basis -/

section Normed

variable [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

variable {D} in
theorem op_unitM_corner_mul (x y : D.PV) (f : D.F0 x ⟶ D.F0 y) :
    MulOpposite.op (unitM y y (𝟙 (D.F0 y))) * MulOpposite.op (unitM x y f) *
      MulOpposite.op (unitM x x (𝟙 (D.F0 x))) = MulOpposite.op (unitM x y f) := by
  rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, unitM_mul, Category.comp_id, unitM_mul,
    Category.id_comp]

/-- **`A₀` has a normed multiplicative basis** (Proposition 4.14 with
Corollary 3.3). -/
theorem hasNormedBasis_A0 (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ) :
    HasNormedMultiplicativeBasis k (Alg D.F0)ᵐᵒᵖ := by
  have hfin' : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y) := fun x y ↦ hfd x y
  obtain ⟨bv, hmem, hspan, hne, hid, hmul⟩ := exists_deckVectors (Q := Q) (c := c) (v₀ := v₀) hF
  have hid0 : ∀ x : D.PV, 𝟙 (D.F0 x) ≠ 0 := fun x ↦ id_ne_zero (L := L) x.1
  set B := basisA0 bv hmem hspan hne
  have hloc : ∀ (x : D.PV) (φ : D.F0 x ⟶ D.F0 x), φ ≫ φ = φ → φ = 0 ∨ φ = 𝟙 (D.F0 x) := by
    intro x φ hφ
    haveI := L.end_isLocalRing x.1
    exact idem_eq_zero_or_one (R := End (meshFam Q c x.1)) (p := φ) hφ
  set eι := Fintype.equivFin D.PV
  let Fp : PrimitiveIdempotents (Alg D.F0)ᵐᵒᵖ :=
    { m := Fintype.card D.PV
      e := fun i ↦ B (idIdx bv hmem hid hid0 (eι.symm i))
      complete := (CompleteOrthogonalIdempotents.equiv eι.symm).2
        (idIdx_complete bv hmem hspan hne hid hid0)
      primitive := fun i ↦ idIdx_primitive bv hmem hspan hne hid hid0 hloc _ }
  have hFe : ∀ x : D.PV, Fp.e (eι x) = MulOpposite.op (unitM x x (𝟙 (D.F0 x))) := fun x ↦ by
    change B (idIdx bv hmem hid hid0 (eι.symm (eι x))) = _
    rw [Equiv.symm_apply_apply, basisA0_idIdx]
  set G := lenA0 D hfin'
  have hone0 : ∀ x : D.PV, 𝟙 (D.F0 x) ∈ degreePart c 0 x.1 x.1 := fun x ↦ by
    have := pathMor_mem_degreePart c (Quiver.Path.nil : Quiver.Path x.1 x.1)
    rwa [pathMor_nil] at this
  have he0 : ∀ i, G.IsHom 0 (Fp.e i) := fun i ↦ by
    obtain ⟨x, rfl⟩ := eι.surjective i
    rw [hFe]
    exact unitM_isHom D hfin' (hone0 x)
  have hcorner0 : ∀ (i : Fin Fp.m) (a : (Alg D.F0)ᵐᵒᵖ), a ∈ Fp.corner (k := k) i i →
      G.IsHom 0 a → ∃ t : k, a = t • Fp.e i := by
    intro i a ha h0
    obtain ⟨x, rfl⟩ := eι.surjective i
    rw [Fp.mem_corner_iff', hFe] at ha
    rw [hFe]
    obtain ⟨a', rfl⟩ : ∃ a' : Alg D.F0, MulOpposite.op a' = a := ⟨a.unop, rfl⟩
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, MulOpposite.op_inj] at ha
    set E := unitM x x (𝟙 (D.F0 x))
    have hEE : E * E = E := by rw [unitM_mul, Category.comp_id]
    have h1 : a' * E = a' := by
      calc a' * E = E * (a' * E) * E := by rw [ha]
        _ = E * (a' * (E * E)) := by simp only [mul_assoc]
        _ = a' := by rw [hEE, ha]
    have h2 : E * a' = a' := by
      calc E * a' = E * (E * (a' * E)) := by rw [ha]
        _ = E * E * (a' * E) := by rw [mul_assoc]
        _ = a' := by rw [hEE, ha]
    have heq := eq_unitM_of_corner h1 h2
    have hdeg : a' x x ∈ degreePart c 0 x.1 x.1 := by
      have := congrArg (fun z : (Alg D.F0)ᵐᵒᵖ ↦ z.unop x x) h0
      change degProj c 0 x.1 x.1 (a' x x) = a' x x at this
      rw [← this]
      exact degProj_mem c 0 _
    obtain ⟨t, ht⟩ := degreePart_zero_eq c hdeg
    refine ⟨t, ?_⟩
    rw [heq, ht, unitM_smul, MulOpposite.op_smul]
  have hb : ∀ t : Idx (D0 Q c v₀ D), ∃ i j d, B t ∈ Fp.corner (k := k) i j ∧ G.IsHom d (B t) := by
    rintro ⟨⟨x, y, g⟩, ht⟩
    refine ⟨eι y, eι x, (hgt Q v₀ g).toNat, ?_, ?_⟩
    · rw [basisA0_apply, Fp.mem_corner_iff', hFe, hFe]
      exact op_unitM_corner_mul x y _
    · rw [basisA0_apply]
      exact unitM_isHom D hfin' (deck_part_le v₀ g x.1 y.1 (hmem x y g))
  -- the basis, reindexed in the universe of the algebra
  let B' := B.reindex (Equiv.ulift (α := Idx (D0 Q c v₀ D))).symm
  have hB' : ∀ i, B' i = B i.down := fun i ↦ by
    simp [B', Module.Basis.reindex_apply]
  refine ⟨ULift (Idx (D0 Q c v₀ D)), B', ⟨?_, ?_, ?_⟩⟩
  · intro i j
    rw [hB', hB']
    rcases basisA0_isMultiplicative bv hmem hspan hne hmul i.down j.down with h | ⟨l, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨ULift.up l, by rw [hB']; exact hl⟩
  · let E : Finset (ULift (Idx (D0 Q c v₀ D))) :=
      Finset.univ.image fun x : D.PV ↦ ULift.up (idIdx bv hmem hid hid0 x)
    have hinj : Function.Injective fun x : D.PV ↦ ULift.up (idIdx bv hmem hid hid0 x) := by
      intro x y h
      have := congrArg (fun t : ULift (Idx (D0 Q c v₀ D)) ↦ t.down.1.1) h
      exact this
    let φ : D.PV ≃ E := Equiv.ofBijective (fun x ↦ ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩)
      ⟨fun x y h ↦ hinj (congrArg Subtype.val h), fun ⟨t, ht⟩ ↦ by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
        exact ⟨x, rfl⟩⟩
    refine ⟨E, (CompleteOrthogonalIdempotents.equiv φ).1 ?_, fun t ht ↦ ?_⟩
    · have := idIdx_complete bv hmem hspan hne hid hid0
      have hfun : ((fun i : E ↦ B' i) ∘ φ) = fun x ↦ B (idIdx bv hmem hid hid0 x) :=
        funext fun x ↦ hB' _
      rw [hfun]
      exact this
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ht
      rw [hB']
      exact idIdx_primitive bv hmem hspan hne hid hid0 hloc x
  · intro n hn
    have := Fp.span_basis_ideal G he0 hcorner0 hF B hb (algebraRadicalPow k _ n)
      (fun a z hz ↦ algebraRadicalPow_mul_left hn a hz)
      (fun a z hz ↦ algebraRadicalPow_mul_right hn a hz)
    refine Eq.trans ?_ this
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i.down, ?_, (hB' i).symm⟩
      rw [← hB']
      exact hi
    · rintro ⟨i, hi, rfl⟩
      refine ⟨ULift.up i, ?_, hB' _⟩
      rw [hB']
      exact hi

end Normed

end MeshWalk

end MultiplicativeBasisDeformations
