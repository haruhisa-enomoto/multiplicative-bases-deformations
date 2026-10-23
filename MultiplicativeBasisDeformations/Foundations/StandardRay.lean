module

public import MultiplicativeBasisDeformations.Foundations.StandardConverse
public import MultiplicativeBasisDeformations.Foundations.Prop103
public import MultiplicativeBasisDeformations.Foundations.TableOfBasis

/-!
# `A ≅ k ray A` implies that `A` is standard in characteristic two (Theorem 11.8(2))

`main-theorems.tex`: "Proposition 8.3(2) and (3) give the initial-form comparison […]
Combine them with Proposition 4.14 and Corollary 4.15 to obtain (1) and (2)."

A multiplicative ray transversal killing the zero ray products (`A ≅ k ray A`) is a basis whose
table presents `A` (`selfPres`). Proposition 8.3(2) presents `A` by the table `P` of `A₀`;
Lemma 3.6 matches the two tables (`IsRayPres.matchFn`, `IsRayPres.mul_iff`), so `A ≅ kP ≅ A₀`
(`algEquivA0_of_rayBasis`), and `A` is standard by the converse of Corollary 4.15
(`isStandard_of_algEquiv`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

variable {V R V' R' : Type} [Fintype V] [DecidableEq V]
  [Fintype R] [DecidableEq R] [Fintype V'] [DecidableEq V'] [Fintype R'] [DecidableEq R']

/-- **An isomorphism of tables** gives an isomorphism of linearizations. -/
theorem nonempty_algEquiv_of_match (T : Mult V R) (T' : Mult V' R') (m : R ≃ R') (ν : V ≃ V')
    (hmul : ∀ r s, T'.mul (m r) (m s) = (T.mul r s).map m) (he : ∀ x, m (T.e x) = T'.e (ν x))
    (k : Type u) [Field k] : Nonempty (T.Lin k ≃ₐ[k] T'.Lin k) := by
  let M : Mor T T' :=
    { f := fun r ↦ some (m r)
      hmul := fun r s ↦ by
        simp only [Option.bind_some, hmul]
        cases T.mul r s <;> rfl
      hid := fun x ↦ Or.inr ⟨ν x, by rw [he]⟩
      hid' := fun x' ↦ ⟨ν.symm x', by simp [he], fun x hx ↦ by
        have := Option.some_injective _ hx
        rw [he] at this
        have h2 := congrArg T'.src this
        rw [T'.src_e, T'.src_e] at h2
        rw [← h2, Equiv.symm_apply_apply]⟩ }
  have hsurj : Function.Surjective (M.alg k) :=
    M.alg_surjective k fun r' ↦ ⟨m.symm r', by simp [M]⟩
  have hdim : Module.finrank k (T.Lin k) = Module.finrank k (T'.Lin k) := by
    rw [Module.finrank_eq_card_basis (T.basis k), Module.finrank_eq_card_basis (T'.basis k)]
    exact Fintype.card_congr m
  have hinj : Function.Injective (M.alg k) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := (M.alg k).toLinearMap)).2
      hsurj
  exact ⟨AlgEquiv.ofBijective (M.alg k) ⟨hinj, hsurj⟩⟩

/-- `nonempty_algEquiv_of_match` with the instances of the target as ordinary implicit
arguments, to be found by unification. -/
theorem nonempty_algEquiv_of_match' {V R V' R' : Type} [Fintype V] [DecidableEq V]
    [Fintype R] [DecidableEq R] {iV' : Fintype V'} {dV' : DecidableEq V'} {iR' : Fintype R'}
    {dR' : DecidableEq R'} (T : Mult V R) (T' : Mult V' R') (m : R ≃ R') (ν : V ≃ V')
    (hmul : ∀ r s, T'.mul (m r) (m s) = (T.mul r s).map m) (he : ∀ x, m (T.e x) = T'.e (ν x))
    (k : Type u) [Field k] :
    Nonempty (T.Lin k ≃ₐ[k] @Mult.Lin V' R' iV' dV' iR' dR' T' k _ _) :=
  @nonempty_algEquiv_of_match V R V' R' _ _ _ _ iV' dV' iR' dR' T T' m ν hmul he k _

end RaySys

namespace PrimitiveIdempotents

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [Ring A] [Algebra k A]
  [FiniteDimensional k A] (F : PrimitiveIdempotents A)
  {b : Module.Basis (F.NonzeroRay k) k A} (hm : IsMultiplicativeBasis b)
  (ht : F.IsRayTransversal b) (hz : F.KillsZeroRayProducts b)
  {R : Type} [Fintype R] [DecidableEq R] (c : R ≃ F.NonzeroRay k)

include ht in
theorem selfSpec (r : R) : ∃ x y, b (c r) ∈ F.corner (k := k) x y ∧ b (c r) ≠ 0 ∧
    (c r).1 = F.ray (k := k) x y (b (c r)) :=
  F.transversal_spec ht (c r)

/-- The source of a ray. -/
def selfSrc (r : R) : Fin F.m := (F.selfSpec ht c r).choose

/-- The target of a ray. -/
def selfTgt (r : R) : Fin F.m := (F.selfSpec ht c r).choose_spec.choose

theorem selfSpec' (r : R) : b (c r) ∈ F.corner (k := k) (F.selfSrc ht c r) (F.selfTgt ht c r) ∧
    b (c r) ≠ 0 :=
  ⟨(F.selfSpec ht c r).choose_spec.choose_spec.1, (F.selfSpec ht c r).choose_spec.choose_spec.2.1⟩

/-- The identity ray at `x`. -/
def idRay (x : Fin F.m) : F.NonzeroRay k :=
  ⟨F.ray (k := k) x x (F.e x), x, x, F.e x, F.e_mem_corner x, (F.primitive x).2.1, rfl⟩

include ht in
theorem b_idRay (x : Fin F.m) : b (F.idRay x) = F.e x :=
  ht.2 (F.idRay x) x (F.mem_ray_self (F.e_mem_corner x))

/-- The identity rays, as indices. -/
def selfE (x : Fin F.m) : R := c.symm (F.idRay x)

include ht in
theorem b_selfE (x : Fin F.m) : b (c (F.selfE c x)) = F.e x := by
  rw [selfE, Equiv.apply_symm_apply]; exact F.b_idRay ht x

theorem selfSrc_E (x : Fin F.m) : F.selfSrc ht c (F.selfE c x) = x :=
  (F.corner_unique (F.selfSpec' ht c _).1 (by rw [F.b_selfE ht c]; exact F.e_mem_corner x)
    (F.selfSpec' ht c _).2).1

theorem selfTgt_E (x : Fin F.m) : F.selfTgt ht c (F.selfE c x) = x :=
  (F.corner_unique (F.selfSpec' ht c _).1 (by rw [F.b_selfE ht c]; exact F.e_mem_corner x)
    (F.selfSpec' ht c _).2).2

/-- **The table of the basis.** -/
def selfTable : RaySys.Mult (Fin F.m) R :=
  RaySys.OfBasis.multOfBasis (b.reindex c.symm) (fun r s ↦ by
      simp only [Module.Basis.reindex_apply, Equiv.symm_symm]
      rcases hm (c r) (c s) with h | ⟨l, hl⟩
      · exact Or.inl h
      · exact Or.inr ⟨c.symm l, by simp [hl]⟩)
    (F.selfE c) (by
      convert F.complete using 1
      funext x
      simp [F.b_selfE ht c])
    (F.selfSrc ht c) (F.selfTgt ht c) (fun r ↦ by
      simp only [Module.Basis.reindex_apply, Equiv.symm_symm, F.b_selfE ht c]
      exact (F.mem_corner_iff').1 (F.selfSpec' ht c r).1)
    (F.selfSrc_E ht c) (F.selfTgt_E ht c)

theorem selfTable_mul {r s t : R} (h : (F.selfTable hm ht c).mul r s = some t) :
    b (c r) * b (c s) = b (c t) := by
  have := (RaySys.OfBasis.mulB_eq_some (b.reindex c.symm)).1 h
  simpa using this

theorem selfTable_mul_none {r s : R} (h : (F.selfTable hm ht c).mul r s = none) :
    b (c r) * b (c s) = 0 := by
  have := RaySys.OfBasis.b_mul_b (b.reindex c.symm) (fun r s ↦ by
      simp only [Module.Basis.reindex_apply, Equiv.symm_symm]
      rcases hm (c r) (c s) with h | ⟨l, hl⟩
      · exact Or.inl h
      · exact Or.inr ⟨c.symm l, by simp [hl]⟩) r s
  change _ = ((F.selfTable hm ht c).mul r s).elim 0 _ at this
  rw [h] at this
  simpa using this

include hz in
/-- **A multiplicative ray transversal killing zero ray products presents `A` by its table.** -/
theorem selfPres : F.IsRayPres (k := k) (F.selfTable hm ht c) (Equiv.refl _) (b ∘ c) := by
  refine ⟨fun r ↦ (F.selfSpec' ht c r).1, fun r ↦ (F.selfSpec' ht c r).2, fun r s hrs ↦ ?_,
    fun x y f hf hf0 ↦ ?_, fun r s t hrst ↦ ?_, fun r s hrs hmid ↦ ?_⟩
  · -- injectivity
    simp only [Equiv.refl_apply, Function.comp_apply] at hrs
    change b (c r) ∈ F.ray (k := k) (F.selfSrc ht c s) (F.selfTgt ht c s) (b (c s)) at hrs
    have hcs := (F.selfSpec' ht c s).1
    have hcr := F.ray_subset_corner hcs hrs
    obtain ⟨h1, h2⟩ := F.corner_unique (F.selfSpec' ht c r).1 hcr (F.selfSpec' ht c r).2
    apply c.injective
    apply Subtype.ext
    rw [F.transversal_ray ht (c r) (F.selfSpec' ht c r).1,
      F.transversal_ray ht (c s) hcs, h1, h2, F.ray_eq_of_mem hcs hrs]
  · -- surjectivity
    set r : F.NonzeroRay k := ⟨F.ray (k := k) x y f, x, y, f, hf, hf0, rfl⟩
    have hbr : b r ∈ F.ray (k := k) x y f := ht.1 r
    have hcr := F.ray_subset_corner hf hbr
    have hspec := F.selfSpec' ht c (c.symm r)
    rw [Equiv.apply_symm_apply] at hspec
    obtain ⟨h1, h2⟩ := F.corner_unique hspec.1 hcr hspec.2
    refine ⟨c.symm r, h1, h2, ?_⟩
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact F.ray_symm hf hbr
  · -- products of rays
    have hp := F.selfTable_mul hm ht c hrst
    simp only [Equiv.refl_apply, Function.comp_apply]
    refine ⟨fun hM ↦ ?_, ?_⟩
    · have hmid := (F.selfTable hm ht c).mul_mid r s t hrst
      have h0 := hz (c r) (c s) _ _ _ (F.selfSpec' ht c r).1
        (by rw [show (F.selfTable hm ht c).tgt r = F.selfTgt ht c r from rfl] at hmid
            rw [hmid]; exact (F.selfSpec' ht c s).1) hM
      rw [hp] at h0
      exact (F.selfSpec' ht c t).2 h0
    · rw [hp]
      exact F.mem_ray_self (F.selfSpec' ht c t).1
  · -- zero products
    simp only [Equiv.refl_apply, Function.comp_apply]
    rw [F.selfTable_mul_none hm ht c hrs]
    exact Submodule.zero_mem _

/-- `k(table) ≅ A`. -/
def selfLin : (F.selfTable hm ht c).Lin k ≃ₐ[k] A :=
  RaySys.OfBasis.linEquiv (b.reindex c.symm) (fun r s ↦ by
      simp only [Module.Basis.reindex_apply, Equiv.symm_symm]
      rcases hm (c r) (c s) with h | ⟨l, hl⟩
      · exact Or.inl h
      · exact Or.inr ⟨c.symm l, by simp [hl]⟩)
    (F.selfE c) (by
      convert F.complete using 1
      funext x
      simp [F.b_selfE ht c])
    (F.selfSrc ht c) (F.selfTgt ht c) (fun r ↦ by
      simp only [Module.Basis.reindex_apply, Equiv.symm_symm, F.b_selfE ht c]
      exact (F.mem_corner_iff').1 (F.selfSpec' ht c r).1)
    (F.selfSrc_E ht c) (F.selfTgt_E ht c)

end PrimitiveIdempotents

namespace IndSkeleton

variable {k : Type u} [Field k] [IsAlgClosed k] {A : Type u} [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b' : S.ArrowBases)

/-- **A trivial algebra is standard**: there are no indecomposable modules. -/
theorem isStandard_of_subsingleton [Subsingleton A] : S.IsStandard := by
  have hn : S.n = 0 := by
    by_contra h
    have i : Fin S.n := ⟨0, by omega⟩
    apply (S.isFiniteIndecomposable i).2.1
    haveI : Subsingleton (S.obj i) := ⟨fun m m' ↦ by
      rw [← one_smul Aᵐᵒᵖ m, ← one_smul Aᵐᵒᵖ m', Subsingleton.elim (1 : Aᵐᵒᵖ) 0, zero_smul,
        zero_smul]⟩
    exact ModuleCat.isZero_of_subsingleton _
  obtain ⟨b⟩ := S.nonempty_arrowBases
  haveI : IsEmpty S.ARVertex := by
    change IsEmpty (Fin S.n)
    rw [hn]
    infer_instance
  exact S.isStandard_of_derivativesSurjective b fun m hm g hg ↦
    ⟨0, fun _ ↦ zero_mem _, funext fun x ↦ (IsEmpty.false x.1).elim⟩

/-- **`A ≅ k ray A` gives `A ≅ A₀`** in characteristic two (Proposition 8.3(2) with Lemma 3.6). -/
theorem algEquivA0_of_rayBasis [CharP k 2] (hbasic : IsBasicAlgebra A)
    (hA : IsRepresentationFinite k A) (hn : Nontrivial A) (F : PrimitiveIdempotents A)
    {b : Module.Basis (F.NonzeroRay k) k A} (hm : IsMultiplicativeBasis b)
    (ht : F.IsRayTransversal b) (hz : F.KillsZeroRayProducts b) :
    Nonempty (A ≃ₐ[k] S.A0 b') := by
  classical
  haveI : ∀ x y : S.ARVertex, Subsingleton (x ⟶ y) := S.hasAtMostOneArrow
  haveI : ∀ x y : S.ARVertex, FiniteDimensional k
      (MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b') x ⟶
        MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b') y) :=
    fun x y ↦ S.finiteDimensional_meshHom b' x y
  obtain ⟨n, e, he, hprim, hbas⟩ := id hbasic
  obtain ⟨v₀, hF, F₁, -, -, -, ι₁, β₁, h₁⟩ := S.exists_normedRayBasis_char2 b'
    CharTwo.two_eq_zero hA he hprim hbas (ne_zero_of_complete he)
    ((cor105Hyp k) A hbasic hA (lift2_all CharTwo.two_eq_zero (cor105Hyp k) _) S b')
  haveI : Finite (F.NonzeroRay k) := Module.Finite.finite_basis b
  letI : Fintype (F.NonzeroRay k) := Fintype.ofFinite _
  let c := (Fintype.equivFin (F.NonzeroRay k)).symm
  have hT := F.selfPres hm ht hz c
  obtain ⟨ψ', σ, hψ'⟩ := exists_algEquiv_idempotents (k := k) hbasic F F₁
  have hT₁ := hT.map ψ' F₁ σ hψ'
  let T := F.selfTable hm ht c
  let P := S.A0MultAR b' v₀ hF
  let m : Fin (Fintype.card (F.NonzeroRay k)) ≃ S.rayA0AR b' v₀ :=
    ⟨hT₁.matchFn h₁, h₁.matchFn hT₁, hT₁.matchFn_left_inv h₁, h₁.matchFn_left_inv hT₁⟩
  let ν : Fin F.m ≃ (S.arMeshData b').PV := ((Equiv.refl _).trans σ).trans ι₁.symm
  have hmul : ∀ r s, P.mul (m r) (m s) = (T.mul r s).map m := by
    intro r s
    cases h : T.mul r s with
    | some t =>
      exact hT₁.mul_iff hA h₁ (hT₁.matchFn_spec h₁ r) (hT₁.matchFn_spec h₁ s)
        (hT₁.matchFn_spec h₁ t) h
    | none =>
      cases h' : P.mul (m r) (m s) with
      | none => rfl
      | some t' =>
        exfalso
        have := h₁.mul_iff hA hT₁ (h₁.matchFn_spec hT₁ (m r)) (h₁.matchFn_spec hT₁ (m s))
          (h₁.matchFn_spec hT₁ t') h'
        change T.mul (h₁.matchFn hT₁ (hT₁.matchFn h₁ r)) (h₁.matchFn hT₁ (hT₁.matchFn h₁ s)) = _
          at this
        rw [hT₁.matchFn_left_inv h₁, hT₁.matchFn_left_inv h₁, h] at this
        cases this
  have he' : ∀ x, m (T.e x) = P.e (ν x) := by
    intro x
    have hs : P.src (m (T.e x)) = ν x := by
      have := (hT₁.matchFn_spec h₁ (T.e x)).1
      rw [T.src_e] at this
      apply ι₁.injective
      refine this.trans ?_
      simp [ν]
    have htg : P.tgt (m (T.e x)) = ν x := by
      have := (hT₁.matchFn_spec h₁ (T.e x)).2.1
      rw [T.tgt_e] at this
      apply ι₁.injective
      refine this.trans ?_
      simp [ν]
    have hr₀ : T.src (m.symm (P.e (ν x))) = x := by
      have := (h₁.matchFn_spec hT₁ (P.e (ν x))).1
      rw [P.src_e] at this
      simp only [ν, Equiv.trans_apply, Equiv.refl_apply, Equiv.apply_symm_apply] at this
      exact σ.injective this
    have h1 := hmul (T.e x) (m.symm (P.e (ν x)))
    have h2 := T.e_mul (m.symm (P.e (ν x)))
    rw [hr₀] at h2
    rw [h2, Option.map_some, Equiv.apply_symm_apply] at h1
    have h3 := P.mul_e (m (T.e x))
    rw [htg, h1] at h3
    exact (Option.some_injective _ h3).symm
  exact ⟨(F.selfLin hm ht c).symm.trans
    ((Classical.choice (RaySys.nonempty_algEquiv_of_match' T P m ν hmul he' k)).trans
      (MeshWalk.thetaA0 (S.arMeshData b') v₀ hF))⟩

end IndSkeleton

end MultiplicativeBasisDeformations
