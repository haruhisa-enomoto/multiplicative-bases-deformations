import MultiplicativeBasisDeformations.Foundations.ProjectiveEvaluation

/-!
# Global dimension at most two (proof of Proposition 2.10)

`graded-category.tex:509–520`: "At a nonprojective label `X`, the exact right
mesh … give `0 → R_{τX} → ⊕_{Y→X} R_Y → R_X → L_X → 0`. At a projective label
`P`, the same lemma gives a resolution `0 → R_{rad P} → R_P → L_P → 0` of length
at most one. Hence `gl.dim Λ ≤ 2`." The proof of Lemma 2.9 uses this in the form
"its kernel is a second syzygy and hence projective".

We derive this consequence: every finite-dimensional module has a projective
resolution of length two by modules `R_Z` (the simple resolutions and the
horseshoe construction, along a composition series); by Schanuel's lemma every
second syzygy is projective; a finite-dimensional projective module is some
`R_W` (tops and Nakayama's lemma).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}

/-- `r ↦ (column algebra element)`, a section of `a ↦ a 1_x`. -/
def colAlgL (x : ι) : Rep F (F x) →ₗ[Alg F] Alg F where
  toFun := colAlg x
  map_add' := colAlg_add x
  map_smul' a r := colAlg_smul x a r

/-- **`R_x` is projective**: a retract of `Λ`. -/
instance projective_rep (x : ι) : Module.Projective (Alg F) (Rep F (F x)) :=
  Module.Projective.of_split (colAlgL x) (LinearMap.toSpanSingleton (Alg F) _ (unit x))
    (LinearMap.ext fun r ↦ colAlg_smul_unit x r)

instance projective_pi {κ : Type} [Fintype κ] [DecidableEq κ] (Z : κ → ι) :
    Module.Projective (Alg F) (∀ j, Rep F (F (Z j))) :=
  Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := Alg F)
    (M := fun j ↦ Rep F (F (Z j))))

section Schanuel

variable {R : Type*} [Ring R] {M P P' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P]
  [Module R P] [AddCommGroup P'] [Module R P']

/-- A surjection onto a projective module splits: `X ≅ ker π × P`. -/
def splitEquiv {X : Type*} [AddCommGroup X] [Module R X] [Module.Projective R P] (π : X →ₗ[R] P)
    (hπ : Function.Surjective π) : X ≃ₗ[R] LinearMap.ker π × P := by
  choose s hs using Module.projective_lifting_property π LinearMap.id hπ
  exact
    { toFun := fun x ↦ (⟨x - s (π x), by
          rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply π s, hs, LinearMap.id_apply,
            sub_self]⟩, π x)
      map_add' := fun x y ↦ by ext <;> simp; abel
      map_smul' := fun c x ↦ by ext <;> simp [smul_sub]
      invFun := fun p ↦ (p.1 : X) + s p.2
      left_inv := fun x ↦ by simp
      right_inv := fun p ↦ by
        ext
        · simp only
          rw [map_add, p.1.2, zero_add, ← LinearMap.comp_apply π s, hs, LinearMap.id_apply,
            add_sub_cancel_right]
        · simp only
          rw [map_add, p.1.2, zero_add, ← LinearMap.comp_apply π s, hs, LinearMap.id_apply] }

/-- **Schanuel's lemma**: for surjections `e : P → M`, `e' : P' → M` from projective
modules, `ker e × P' ≅ ker e' × P`. -/
theorem schanuel [Module.Projective R P] [Module.Projective R P'] (e : P →ₗ[R] M) (e' : P' →ₗ[R] M)
    (he : Function.Surjective e) (he' : Function.Surjective e') :
    Nonempty ((LinearMap.ker e × P') ≃ₗ[R] (LinearMap.ker e' × P)) := by
  -- the pullback
  set X := LinearMap.ker (e.coprod (-e'))
  have hX : ∀ a b, (a, b) ∈ X ↔ e a = e' b := by
    intro a b
    rw [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg,
      sub_eq_zero]
  set π₁ : X →ₗ[R] P := (LinearMap.fst R P P').comp X.subtype
  set π₂ : X →ₗ[R] P' := (LinearMap.snd R P P').comp X.subtype
  have hπ₂ : Function.Surjective π₂ := by
    intro b
    obtain ⟨a, ha⟩ := he (e' b)
    exact ⟨⟨(a, b), (hX a b).2 ha⟩, rfl⟩
  have hπ₁ : Function.Surjective π₁ := by
    intro a
    obtain ⟨b, hb⟩ := he' (e a)
    exact ⟨⟨(a, b), (hX a b).2 hb.symm⟩, rfl⟩
  have mem : ∀ x : X, e (x : P × P').1 = e' (x : P × P').2 := fun x ↦ (hX _ _).1 x.2
  have k₂ : LinearMap.ker π₂ ≃ₗ[R] LinearMap.ker e :=
    { toFun := fun x ↦ ⟨(x.1 : P × P').1, by
        have h2 : ((x.1 : P × P').2) = 0 := x.2
        rw [LinearMap.mem_ker, mem x.1, h2, map_zero]⟩
      map_add' := fun x y ↦ rfl
      map_smul' := fun c x ↦ rfl
      invFun := fun a ↦ ⟨⟨(a.1, 0), (hX _ _).2 (by rw [map_zero]; exact a.2)⟩, rfl⟩
      left_inv := fun x ↦ by
        apply Subtype.ext; apply Subtype.ext
        have h2 : ((x.1 : P × P').2) = 0 := x.2
        ext
        · rfl
        · exact h2.symm
      right_inv := fun a ↦ rfl }
  have k₁ : LinearMap.ker π₁ ≃ₗ[R] LinearMap.ker e' :=
    { toFun := fun x ↦ ⟨(x.1 : P × P').2, by
        have h2 : ((x.1 : P × P').1) = 0 := x.2
        rw [LinearMap.mem_ker, ← mem x.1, h2, map_zero]⟩
      map_add' := fun x y ↦ rfl
      map_smul' := fun c x ↦ rfl
      invFun := fun b ↦ ⟨⟨(0, b.1), (hX _ _).2 (by rw [map_zero]; exact b.2.symm)⟩, rfl⟩
      left_inv := fun x ↦ by
        apply Subtype.ext; apply Subtype.ext
        have h2 : ((x.1 : P × P').1) = 0 := x.2
        ext
        · exact h2.symm
        · rfl
      right_inv := fun b ↦ rfl }
  exact ⟨((k₂.symm.prodCongr (LinearEquiv.refl R P')).trans (splitEquiv π₂ hπ₂).symm).trans
    ((splitEquiv π₁ hπ₁).trans (k₁.prodCongr (LinearEquiv.refl R P)))⟩

/-- **One horseshoe step.** Let `0 → A' → A → A'' → 0` be exact
(`i` injective, `p` surjective, `ker p = range i`) and let `e' : P' → A'`,
`e'' : P'' → A''` be surjections with `P''` projective. Then
`e : P' × P'' → A`, `(a, b) ↦ i (e' a) + λ b` with `p λ = e''`, is surjective,
and its kernel is an extension of `ker e''` by `ker e'`. -/
theorem horseshoe_step {A' A A'' : Type*} [AddCommGroup A'] [Module R A'] [AddCommGroup A]
    [Module R A] [AddCommGroup A''] [Module R A''] [Module.Projective R P']
    (i : A' →ₗ[R] A) (p : A →ₗ[R] A'') (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.ker p = LinearMap.range i) (e' : P →ₗ[R] A') (e'' : P' →ₗ[R] A'')
    (he' : Function.Surjective e') (he'' : Function.Surjective e'') :
    ∃ e : (P × P') →ₗ[R] A, Function.Surjective e ∧
      ∃ (j : LinearMap.ker e' →ₗ[R] LinearMap.ker e) (q : LinearMap.ker e →ₗ[R] LinearMap.ker e''),
        Function.Injective j ∧ Function.Surjective q ∧ LinearMap.ker q = LinearMap.range j := by
  obtain ⟨lam, hlam⟩ := Module.projective_lifting_property p e'' hp
  set e : (P × P') →ₗ[R] A := (i.comp e').coprod lam
  have he_apply : ∀ a b, e (a, b) = i (e' a) + lam b := fun a b ↦ rfl
  have hpe : ∀ x, p (e x) = e'' x.2 := by
    rintro ⟨a, b⟩
    rw [he_apply, map_add, ← LinearMap.comp_apply p lam, hlam]
    have : p (i (e' a)) = 0 := by
      rw [← LinearMap.mem_ker, hex]; exact LinearMap.mem_range_self i _
    rw [this, zero_add]
  have hsurj : Function.Surjective e := by
    intro m
    obtain ⟨b, hb⟩ := he'' (p m)
    have hm : m - lam b ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply p lam, hlam, hb, sub_self]
    rw [hex] at hm
    obtain ⟨a', ha'⟩ := hm
    obtain ⟨a, ha⟩ := he' a'
    exact ⟨(a, b), by rw [he_apply, ha, ha', sub_add_cancel]⟩
  refine ⟨e, hsurj, ?_⟩
  set j : LinearMap.ker e' →ₗ[R] LinearMap.ker e :=
    { toFun := fun a ↦ ⟨(a.1, 0), by
        rw [LinearMap.mem_ker, he_apply, a.2, map_zero, map_zero, add_zero]⟩
      map_add' := fun a b ↦ by apply Subtype.ext; simp
      map_smul' := fun c a ↦ by apply Subtype.ext; simp }
  set q : LinearMap.ker e →ₗ[R] LinearMap.ker e'' :=
    { toFun := fun x ↦ ⟨(x.1 : P × P').2, by
        rw [LinearMap.mem_ker, ← hpe, x.2, map_zero]⟩
      map_add' := fun a b ↦ rfl
      map_smul' := fun c a ↦ rfl }
  refine ⟨j, q, fun a b h ↦ ?_, fun b ↦ ?_, ?_⟩
  · apply Subtype.ext
    have := congrArg (fun x : LinearMap.ker e ↦ (x : P × P').1) h
    exact this
  · -- `λ b ∈ ker p = range i`, and `i` of it comes from `P`
    have hb : lam b.1 ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply p lam, hlam]; exact b.2
    rw [hex] at hb
    obtain ⟨a', ha'⟩ := hb
    obtain ⟨a, ha⟩ := he' a'
    refine ⟨⟨(-a, b.1), ?_⟩, rfl⟩
    rw [LinearMap.mem_ker, he_apply, map_neg, ha, map_neg, ha', neg_add_cancel]
  · ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx
      have h2 : (x.1 : P × P').2 = 0 := congrArg Subtype.val hx
      have h1 : i (e' (x.1 : P × P').1) = 0 := by
        have := x.2
        rw [LinearMap.mem_ker] at this
        have e1 : e x.1 = i (e' (x.1 : P × P').1) + lam (x.1 : P × P').2 := rfl
        rw [e1, h2, map_zero, add_zero] at this
        exact this
      have h3 : e' (x.1 : P × P').1 = 0 := hi (by rw [h1, map_zero])
      refine ⟨⟨(x.1 : P × P').1, h3⟩, ?_⟩
      apply Subtype.ext
      ext
      · rfl
      · exact h2.symm
    · rintro ⟨a, rfl⟩
      rfl

end Schanuel

/-- An extension of a projective module by a projective module is projective. -/
theorem projective_of_ses {R : Type*} [Ring R] {A' A A'' : Type*} [AddCommGroup A'] [Module R A']
    [AddCommGroup A] [Module R A] [AddCommGroup A''] [Module R A''] [Module.Projective R A']
    [Module.Projective R A''] (i : A' →ₗ[R] A) (p : A →ₗ[R] A'') (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : LinearMap.ker p = LinearMap.range i) :
    Module.Projective R A := by
  have e1 : LinearMap.ker p ≃ₗ[R] A' :=
    (LinearEquiv.ofEq _ _ hex).trans (LinearEquiv.ofInjective i hi).symm
  exact Module.Projective.of_equiv' ((e1.prodCongr (LinearEquiv.refl R A'')).symm.trans
    (splitEquiv p hp).symm)

/-- A resolution of length two: `P₁ → P₀ → M → 0` with projective `P₀, P₁` and
projective kernel of `P₁ → ker (P₀ → M)`. -/
def ExRes (R : Type w) [Ring R] (M : Type w) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (P₀ : Type w) (_ : AddCommGroup P₀) (_ : Module R P₀) (_ : Module.Projective R P₀)
    (e₀ : P₀ →ₗ[R] M) (_ : Function.Surjective e₀)
    (P₁ : Type w) (_ : AddCommGroup P₁) (_ : Module R P₁) (_ : Module.Projective R P₁)
    (e₁ : P₁ →ₗ[R] LinearMap.ker e₀) (_ : Function.Surjective e₁),
    Module.Projective R (LinearMap.ker e₁)

theorem ExRes.of_equiv {R : Type w} [Ring R] {M N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) (h : ExRes R M) : ExRes R N := by
  obtain ⟨P₀, _, _, _, e₀, he₀, P₁, _, _, _, e₁, he₁, hK⟩ := h
  set k₀ : LinearMap.ker e₀ ≃ₗ[R] LinearMap.ker (e.toLinearMap.comp e₀) :=
    LinearEquiv.ofEq _ _ (by
      ext x; simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.map_eq_zero_iff])
  refine ⟨P₀, _, _, inferInstance, e.toLinearMap.comp e₀, e.surjective.comp he₀, P₁, _, _,
    inferInstance, k₀.toLinearMap.comp e₁, k₀.surjective.comp he₁, ?_⟩
  have : LinearMap.ker (k₀.toLinearMap.comp e₁) = LinearMap.ker e₁ := by
    ext x; simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
  rw [this]; exact hK

/-- **Horseshoe**: resolutions of length two pass to extensions. -/
theorem ExRes.extension {R : Type w} [Ring R] {M' M M'' : Type w} [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M] [AddCommGroup M''] [Module R M''] (i : M' →ₗ[R] M)
    (p : M →ₗ[R] M'') (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.ker p = LinearMap.range i) (h' : ExRes R M') (h'' : ExRes R M'') :
    ExRes R M := by
  obtain ⟨P₀', _, _, _, e₀', he₀', P₁', _, _, _, e₁', he₁', hK'⟩ := h'
  obtain ⟨P₀'', _, _, _, e₀'', he₀'', P₁'', _, _, _, e₁'', he₁'', hK''⟩ := h''
  obtain ⟨e₀, he₀, j₀, q₀, hj₀, hq₀, hex₀⟩ := horseshoe_step i p hi hp hex e₀' e₀'' he₀' he₀''
  obtain ⟨e₁, he₁, j₁, q₁, hj₁, hq₁, hex₁⟩ := horseshoe_step j₀ q₀ hj₀ hq₀ hex₀ e₁' e₁'' he₁' he₁''
  exact ⟨P₀' × P₀'', _, _, inferInstance, e₀, he₀, P₁' × P₁'', _, _, inferInstance, e₁, he₁,
    projective_of_ses j₁ q₁ hj₁ hq₁ hex₁⟩

theorem projective_of_subsingleton {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    [Subsingleton M] : Module.Projective R M :=
  Module.Projective.of_basis (Module.Basis.empty (ι := Empty) M)

theorem ExRes.of_subsingleton {R : Type w} [Ring R] {M : Type w} [AddCommGroup M] [Module R M]
    [Subsingleton M] : ExRes R M := by
  refine ⟨PUnit, _, _, projective_of_subsingleton, 0, fun m ↦ ⟨PUnit.unit, Subsingleton.elim _ _⟩,
    PUnit, _, _, projective_of_subsingleton, 0, fun x ↦ ⟨PUnit.unit, ?_⟩,
    projective_of_subsingleton⟩
  apply Subtype.ext
  exact Subsingleton.elim (α := PUnit) _ _

variable {L : LocalFamily (k := k) F} (D : MeshData F L)

namespace MeshData

include D in
/-- The simple tops have resolutions of length two (the exact right meshes). -/
theorem exRes_top (x : ι) : ExRes (Alg F) (L.Top x) := by
  set e₀ := (L.radRep x).mkQ
  have hker₀ : LinearMap.ker e₀ = L.radRep x := Submodule.ker_mkQ _
  have hrange : ∀ s, D.meshMap x s ∈ LinearMap.ker e₀ := fun s ↦ by
    rw [hker₀]; exact D.meshMap_mem_rad x s
  set e₁ := LinearMap.codRestrict (LinearMap.ker e₀) (D.meshMap x) hrange
  have he₁ : Function.Surjective e₁ := by
    rintro ⟨r, hr⟩
    rw [hker₀, ← D.range_meshMap] at hr
    obtain ⟨s, rfl⟩ := hr
    exact ⟨s, rfl⟩
  have hker₁ : LinearMap.ker e₁ = LinearMap.ker (D.meshMap x) := LinearMap.ker_codRestrict _ _ _
  refine ⟨Rep F (F x), _, _, inferInstance, e₀, Submodule.mkQ_surjective _,
    ∀ a : D.Mid x, Rep F (F (D.mid x a)), _, _, inferInstance, e₁, he₁, ?_⟩
  rw [hker₁]
  by_cases hx : D.proj x
  · rw [LinearMap.ker_eq_bot.2 (D.meshMap_injective x hx)]
    exact projective_of_subsingleton
  · rw [← D.range_tauMap x hx]
    exact Module.Projective.of_equiv' (LinearEquiv.ofInjective _ (D.tauMap_injective x hx))

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

include D in
/-- **Every finite-dimensional module has a resolution of length two.** -/
theorem exRes_of_finiteDimensional (M : Type w) [AddCommGroup M] [Module k M] [Module (Alg F) M]
    [IsScalarTower k (Alg F) M] [FiniteDimensional k M] : ExRes (Alg F) M := by
  induction hn : Module.finrank k M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    by_cases hM : Subsingleton M
    · exact ExRes.of_subsingleton
    have hne : (⊤ : Submodule (Alg F) M) ≠ ⊥ := by
      intro h
      apply hM
      refine ⟨fun a b ↦ ?_⟩
      have ha : a ∈ (⊥ : Submodule (Alg F) M) := h ▸ Submodule.mem_top
      have hb : b ∈ (⊥ : Submodule (Alg F) M) := h ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at ha hb
      rw [ha, hb]
    obtain ⟨S, hS, -⟩ := exists_atom_le (k := k) hne
    haveI : IsSimpleModule (Alg F) S := (isSimpleModule_iff_isAtom).2 hS
    obtain ⟨x, ⟨eS⟩⟩ := L.exists_iso_top (S := S)
    have hlt : Module.finrank k (M ⧸ S) < n := by
      have h1 := Submodule.finrank_quotient_add_finrank (S.restrictScalars k)
      have h2 : 0 < Module.finrank k (S.restrictScalars k) := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        haveI : Nontrivial S := IsSimpleModule.nontrivial (Alg F) S
        obtain ⟨s, hs⟩ := exists_ne (0 : S)
        exact ⟨⟨s, s.2⟩, fun h ↦ hs (Subtype.ext (congrArg Subtype.val h))⟩
      have e : Module.finrank k (M ⧸ S) = Module.finrank k (M ⧸ S.restrictScalars k) := rfl
      omega
    exact ExRes.extension S.subtype S.mkQ Subtype.val_injective (Submodule.mkQ_surjective S)
      ((Submodule.ker_mkQ S).trans (Submodule.range_subtype S).symm)
      ((D.exRes_top x).of_equiv eS.symm) (ih _ hlt (M ⧸ S) rfl)

include D in
/-- **Second syzygies are projective** (`gl.dim Λ ≤ 2`). -/
theorem syzygy_projective (M : Type w) [AddCommGroup M] [Module k M] [Module (Alg F) M]
    [IsScalarTower k (Alg F) M] [FiniteDimensional k M] {P₀ P₁ : Type w} [AddCommGroup P₀]
    [Module (Alg F) P₀] [Module.Projective (Alg F) P₀] [AddCommGroup P₁] [Module (Alg F) P₁]
    [Module.Projective (Alg F) P₁] (e₀ : P₀ →ₗ[Alg F] M) (he₀ : Function.Surjective e₀)
    (e₁ : P₁ →ₗ[Alg F] LinearMap.ker e₀) (he₁ : Function.Surjective e₁) :
    Module.Projective (Alg F) (LinearMap.ker e₁) := by
  obtain ⟨Q₀, _, _, _, f₀, hf₀, Q₁, _, _, _, f₁, hf₁, hK⟩ := D.exRes_of_finiteDimensional M
  obtain ⟨σ⟩ := schanuel e₀ f₀ he₀ hf₀
  -- two surjections onto `ker e₀ × Q₀`
  set g := e₁.prodMap (LinearMap.id : Q₀ →ₗ[Alg F] Q₀)
  set g' := σ.symm.toLinearMap.comp (f₁.prodMap (LinearMap.id : P₀ →ₗ[Alg F] P₀))
  have hg : Function.Surjective g := fun y ↦ by
    obtain ⟨a, ha⟩ := he₁ y.1
    exact ⟨(a, y.2), by simp [g, ha]⟩
  have hg' : Function.Surjective g' := fun y ↦ by
    obtain ⟨a, ha⟩ := hf₁ (σ y).1
    refine ⟨(a, (σ y).2), ?_⟩
    simp only [g', LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply, ha,
      LinearEquiv.coe_coe, Prod.mk.eta, LinearEquiv.symm_apply_apply]
  obtain ⟨τ⟩ := schanuel g g' hg hg'
  have kg : LinearMap.ker g ≃ₗ[Alg F] LinearMap.ker e₁ :=
    { toFun := fun x ↦ ⟨(x.1 : P₁ × Q₀).1, by
        have := x.2
        rw [LinearMap.mem_ker] at this ⊢
        exact congrArg Prod.fst this⟩
      map_add' := fun x y ↦ rfl
      map_smul' := fun c x ↦ rfl
      invFun := fun a ↦ ⟨(a.1, 0), by
        rw [LinearMap.mem_ker]
        simp only [g, LinearMap.prodMap_apply, LinearMap.id_apply]
        rw [show e₁ a.1 = 0 from a.2]; rfl⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        have := x.2
        rw [LinearMap.mem_ker] at this
        have h2 : (x.1 : P₁ × Q₀).2 = 0 := congrArg Prod.snd this
        ext
        · rfl
        · exact h2.symm
      right_inv := fun a ↦ rfl }
  have kg' : LinearMap.ker g' ≃ₗ[Alg F] LinearMap.ker f₁ :=
    { toFun := fun x ↦ ⟨(x.1 : Q₁ × P₀).1, by
        have := x.2
        rw [LinearMap.mem_ker] at this ⊢
        simp only [g', LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.map_eq_zero_iff] at this
        exact congrArg Prod.fst this⟩
      map_add' := fun x y ↦ rfl
      map_smul' := fun c x ↦ rfl
      invFun := fun a ↦ ⟨(a.1, 0), by
        rw [LinearMap.mem_ker]
        simp only [g', LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
          LinearEquiv.coe_coe]
        rw [show f₁ a.1 = 0 from a.2]
        simp⟩
      left_inv := fun x ↦ by
        apply Subtype.ext
        have := x.2
        rw [LinearMap.mem_ker] at this
        simp only [g', LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.map_eq_zero_iff] at this
        have h2 : (x.1 : Q₁ × P₀).2 = 0 := congrArg Prod.snd this
        ext
        · rfl
        · exact h2.symm
      right_inv := fun a ↦ rfl }
  -- `ker e₁` is a retract of a projective module
  set ρ : (LinearMap.ker e₁ × (Q₁ × P₀)) ≃ₗ[Alg F] (LinearMap.ker f₁ × (P₁ × Q₀)) :=
    ((kg.symm.prodCongr (LinearEquiv.refl _ _)).trans τ).trans
      (kg'.prodCongr (LinearEquiv.refl _ _))
  exact Module.Projective.of_split
    (ρ.toLinearMap.comp (LinearMap.inl (Alg F) _ _))
    ((LinearMap.fst (Alg F) _ _).comp ρ.symm.toLinearMap)
    (LinearMap.ext fun x ↦ by simp)

end MeshData

namespace LocalFamily

variable (L) [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

/-- An endomorphism of `R_x` inducing the identity on the top is invertible. -/
theorem bijective_of_top {x : ι} (ψ : Rep F (F x) →ₗ[Alg F] Rep F (F x))
    (hψ : (L.radRep x).mkQ.comp ψ = (L.radRep x).mkQ) : Function.Bijective ψ := by
  set u : End (F x) := (ψ (unit x)) x
  have hψu : ψ = repMap u := eq_repMap ψ
  have hu : u ∉ L.rad x x := by
    intro hu
    have h1 := LinearMap.congr_fun hψ (unit x)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply] at h1
    rw [eq_comm, Submodule.Quotient.eq] at h1
    have h2 := h1 x
    rw [Rep.sub_apply'] at h2
    have h3 : (unit x) x = 𝟙 (F x) := by simp [unit]
    rw [h3] at h2
    exact L.id_not_mem x (by
      have := Submodule.add_mem _ h2 hu
      rwa [sub_add_cancel] at this)
  obtain ⟨v, hv⟩ := (L.isUnit_of_not_mem hu)
  have hinv : ∀ m, repMap (F := F) (((v⁻¹ : (End (F x))ˣ) : End (F x))) (repMap u m) = m := by
    intro m
    ext y
    simp only [repMap_apply, Category.assoc]
    have : u ≫ ((v⁻¹ : (End (F x))ˣ) : End (F x)) = 𝟙 _ := by
      rw [← hv]; exact v.inv_mul
    rw [this, Category.comp_id]
  have hinv' : ∀ m, repMap (F := F) u (repMap (((v⁻¹ : (End (F x))ˣ) : End (F x))) m) = m := by
    intro m
    ext y
    simp only [repMap_apply, Category.assoc]
    have : ((v⁻¹ : (End (F x))ˣ) : End (F x)) ≫ u = 𝟙 _ := by
      rw [← hv]; exact v.mul_inv
    rw [this, Category.comp_id]
  rw [hψu]
  exact ⟨fun a b h ↦ by rw [← hinv a, h, hinv b], fun m ↦ ⟨_, hinv' m⟩⟩

/-- A split surjection: `P ≅ ker r × Q` for `r ∘ h = id`. -/
def splitEquivOf {R : Type*} [Ring R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q]
    [Module R Q] (r : P →ₗ[R] Q) (h : Q →ₗ[R] P) (hrh : ∀ q, r (h q) = q) :
    P ≃ₗ[R] LinearMap.ker r × Q where
  toFun x := (⟨x - h (r x), by rw [LinearMap.mem_ker, map_sub, hrh, sub_self]⟩, r x)
  map_add' x y := by ext <;> simp; abel
  map_smul' c x := by ext <;> simp [smul_sub]
  invFun p := (p.1 : P) + h p.2
  left_inv x := by simp
  right_inv p := by
    ext
    · simp only
      rw [map_add, p.1.2, zero_add, hrh, add_sub_cancel_right]
    · simp only
      rw [map_add, p.1.2, zero_add, hrh]

include L in
/-- **A finite-dimensional projective module is `R_W` for a family `W`.** -/
theorem exists_equiv_RZ (P : Type w) [AddCommGroup P] [Module k P] [Module (Alg F) P]
    [IsScalarTower k (Alg F) P] [FiniteDimensional k P] [Module.Projective (Alg F) P] :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (W : κ → ι),
      Nonempty (P ≃ₗ[Alg F] ∀ j, Rep F (F (W j))) := by
  induction hn : Module.finrank k P using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    by_cases hP : Subsingleton P
    · exact ⟨Empty, inferInstance, inferInstance, Empty.elim, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
    haveI : Nontrivial P := not_subsingleton_iff_nontrivial.1 hP
    haveI : Module.Finite (Alg F) P := Module.Finite.of_restrictScalars_finite k (Alg F) P
    obtain hb | ⟨N, hN, -⟩ := eq_top_or_exists_le_coatom (⊥ : Submodule (Alg F) P)
    · exact absurd hb bot_ne_top
    haveI : IsSimpleModule (Alg F) (P ⧸ N) := (isSimpleModule_iff_isCoatom).2 hN
    obtain ⟨x, ⟨eS⟩⟩ := L.exists_iso_top (S := P ⧸ N)
    set π : P →ₗ[Alg F] L.Top x := eS.toLinearMap.comp N.mkQ
    have hπ : Function.Surjective π := eS.surjective.comp (Submodule.mkQ_surjective N)
    obtain ⟨g, hg⟩ := Module.projective_lifting_property (L.radRep x).mkQ π
      (Submodule.mkQ_surjective _)
    obtain ⟨h, hh⟩ := Module.projective_lifting_property π (L.radRep x).mkQ hπ
    have hψ : (L.radRep x).mkQ.comp (g.comp h) = (L.radRep x).mkQ := by
      rw [← LinearMap.comp_assoc, hg, hh]
    set ψe := LinearEquiv.ofBijective (g.comp h) (L.bijective_of_top _ hψ)
    set r : P →ₗ[Alg F] Rep F (F x) := ψe.symm.toLinearMap.comp g
    have hrh : ∀ q, r (h q) = q := fun q ↦ by
      simp only [r, LinearMap.comp_apply, LinearEquiv.coe_coe]
      exact ψe.symm_apply_apply q
    set σ := splitEquivOf r h hrh
    haveI : Module.Projective (Alg F) (LinearMap.ker r) :=
      Module.Projective.of_split (LinearMap.ker r).subtype
        ((LinearMap.fst (Alg F) _ _).comp σ.toLinearMap) (LinearMap.ext fun y ↦ by
          apply Subtype.ext
          simp [σ, splitEquivOf])
    haveI : FiniteDimensional k (LinearMap.ker r) :=
      Module.Finite.of_injective ((LinearMap.ker r).subtype.restrictScalars k) Subtype.val_injective
    have hlt : Module.finrank k (LinearMap.ker r) < n := by
      have e1 := LinearEquiv.finrank_eq (σ.restrictScalars k)
      rw [Module.finrank_prod] at e1
      have hpos : 0 < Module.finrank k (Rep F (F x)) := by
        rw [Module.finrank_pos_iff_exists_ne_zero]
        exact ⟨unit x, fun h0 ↦ L.unit_not_mem x (h0 ▸ zero_mem _)⟩
      omega
    obtain ⟨κ, _, _, W, ⟨eW⟩⟩ := ih _ hlt (LinearMap.ker r) rfl
    refine ⟨Option κ, inferInstance, inferInstance, fun j ↦ j.elim x W, ⟨?_⟩⟩
    exact σ.trans (((eW.prodCongr (LinearEquiv.refl _ _)).trans
      (LinearEquiv.prodComm (Alg F) _ _)).trans (LinearEquiv.piOptionEquivProd (R := Alg F)
        (M := fun j : Option κ ↦ Rep F (F (j.elim x W)))).symm)

end LocalFamily

namespace MeshData

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]

include D in
/-- **Kernels of maps between families are families** (`gl.dim Λ ≤ 2`). -/
theorem ker_bigMap_equiv {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {Z : κ → ι} {Z' : κ' → ι} (f : Mat F Z Z') :
    ∃ (μ : Type) (_ : Fintype μ) (_ : DecidableEq μ) (W : μ → ι),
      Nonempty (LinearMap.ker (bigMap f) ≃ₗ[Alg F] RZ F W) := by
  set N := LinearMap.range (bigMap (F := F) f)
  set e₀ := N.mkQ
  have hker₀ : LinearMap.ker e₀ = N := Submodule.ker_mkQ N
  set e₁ : RZ F Z →ₗ[Alg F] LinearMap.ker e₀ :=
    (LinearEquiv.ofEq _ _ hker₀.symm).toLinearMap.comp (bigMap f).rangeRestrict
  have he₁ : Function.Surjective e₁ :=
    (LinearEquiv.ofEq _ _ hker₀.symm).surjective.comp (LinearMap.surjective_rangeRestrict _)
  have hker₁ : LinearMap.ker e₁ = LinearMap.ker (bigMap f) := by
    ext m
    simp only [e₁, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff]
    rw [← LinearMap.mem_ker, LinearMap.ker_rangeRestrict, LinearMap.mem_ker]
  haveI := D.syzygy_projective (RZ F Z' ⧸ N) e₀ (Submodule.mkQ_surjective N) e₁ he₁
  haveI : Module.Projective (Alg F) (LinearMap.ker (bigMap f)) :=
    Module.Projective.of_equiv' (LinearEquiv.ofEq _ _ hker₁)
  haveI : FiniteDimensional k (LinearMap.ker (bigMap f)) :=
    Module.Finite.of_injective ((LinearMap.ker (bigMap f)).subtype.restrictScalars k)
      Subtype.val_injective
  exact L.exists_equiv_RZ (LinearMap.ker (bigMap f))

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
