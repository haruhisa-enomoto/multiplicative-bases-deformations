import MultiplicativeBasisDeformations.Foundations.LocalMesh

/-!
# Lemma 2.9: vanishing on modules killed by `e`

`lem:projective-evaluation-criterion` (`graded-category.tex`): "Assume
`Hom_Λ(T, Λ) = Ext¹_Λ(T, Λ) = 0` whenever `Te = 0`. … It suffices to check the
two vanishings on the simple `Λ`-modules killed by `e`. … composition series and
the long exact sequences extend the two vanishings from the simples to every
module killed by `e`." In the proof of Proposition 2.10 the simples killed by
`e` are the tops `L_x` at nonprojective labels, where the vanishings come from
the exact right meshes (`MeshData.hom_top_eq_zero`, `MeshData.extend_top`).

Here `e` is the sum of the idempotents at the projective labels; a module is
killed by `e` when every projective idempotent acts by zero. `Ext¹ = 0` is used
in extension form: maps into `R_w` extend from a submodule with quotient
killed by `e`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}
  [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)]
  {L : LocalFamily (k := k) F} (D : MeshData F L)

instance (X : 𝒞) [∀ y : ι, FiniteDimensional k (F y ⟶ X)] : FiniteDimensional k (Rep F X) :=
  inferInstanceAs (FiniteDimensional k (∀ y : ι, F y ⟶ X))

namespace MeshData

/-- A submodule with quotient killed by the projective idempotents. -/
def KilledSub {M : Type*} [AddCommGroup M] [Module (Alg F) M] (U : Submodule (Alg F) M) : Prop :=
  ∀ x, D.proj x → ∀ m : M, idem (F := F) x • m ∈ U

theorem exists_atom_le {T : Type*} [AddCommGroup T] [Module k T] [Module (Alg F) T]
    [IsScalarTower k (Alg F) T] [FiniteDimensional k T] {N : Submodule (Alg F) T} (hN : N ≠ ⊥) :
    ∃ S, IsAtom S ∧ S ≤ N := by
  have hA : IsArtinian (Alg F) T := isArtinian_of_tower k inferInstance
  haveI : IsAtomic (Submodule (Alg F) T) := isAtomic_of_orderBot_wellFounded_lt hA.wf
  obtain h | ⟨S, hS, hSN⟩ := eq_bot_or_exists_atom_le N
  · exact absurd h hN
  · exact ⟨S, hS, hSN⟩

theorem top_mk_ne_zero (x : ι) : (L.radRep x).mkQ (unit x) ≠ 0 := by
  rw [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]
  exact L.unit_not_mem x

theorem idem_smul_top_mk (x : ι) :
    idem (F := F) x • (L.radRep x).mkQ (unit x) = (L.radRep x).mkQ (unit x) := by
  rw [← map_smul]
  congr 1
  exact colAlg_smul_unit x (unit x)

/-- A simple module on which the projective idempotents act by zero is a top at
a nonprojective label. -/
theorem exists_iso_top_nonproj {S : Type*} [AddCommGroup S] [Module (Alg F) S]
    [IsSimpleModule (Alg F) S] (hS : ∀ x, D.proj x → ∀ s : S, idem (F := F) x • s = 0) :
    ∃ x, ¬ D.proj x ∧ Nonempty (S ≃ₗ[Alg F] L.Top x) := by
  obtain ⟨x, ⟨e⟩⟩ := L.exists_iso_top (S := S)
  refine ⟨x, fun hx ↦ ?_, ⟨e⟩⟩
  have h := hS x hx (e.symm ((L.radRep x).mkQ (unit x)))
  rw [← map_smul, idem_smul_top_mk, LinearEquiv.map_eq_zero_iff] at h
  exact top_mk_ne_zero x h

/-- **`Hom(T, R_w) = 0` for `T` killed by `e`**. -/
theorem hom_eq_zero_of_killed {T : Type*} [AddCommGroup T] [Module k T] [Module (Alg F) T]
    [IsScalarTower k (Alg F) T] [FiniteDimensional k T]
    (hT : ∀ x, D.proj x → ∀ t : T, idem (F := F) x • t = 0) (w : ι)
    (θ : T →ₗ[Alg F] Rep F (F w)) : θ = 0 := by
  by_contra hθ
  have hr : LinearMap.range θ ≠ ⊥ := fun h ↦ hθ (LinearMap.range_eq_bot.1 h)
  obtain ⟨S, hS, hSr⟩ := exists_atom_le (k := k) hr
  haveI : IsSimpleModule (Alg F) S := (isSimpleModule_iff_isAtom).2 hS
  obtain ⟨x, hx, ⟨e⟩⟩ := D.exists_iso_top_nonproj (S := S) (fun y hy s ↦ by
    obtain ⟨t, ht⟩ := hSr s.2
    apply Subtype.ext
    rw [Submodule.coe_smul, ← ht, ← map_smul, hT y hy t, map_zero]
    rfl)
  have h0 := D.hom_top_eq_zero x hx w (S.subtype.comp e.symm.toLinearMap)
  have := LinearMap.congr_fun h0 ((L.radRep x).mkQ (unit x))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
    LinearMap.zero_apply] at this
  have h1 : e.symm ((L.radRep x).mkQ (unit x)) = 0 := Subtype.ext this
  rw [LinearEquiv.map_eq_zero_iff] at h1
  exact top_mk_ne_zero x h1

variable {M : Type*} [AddCommGroup M] [Module k M] [Module (Alg F) M] [IsScalarTower k (Alg F) M]

/-- Maps into `R_w` extend from `U` to `V`. -/
def ExtP (w : ι) (U V : Submodule (Alg F) M) (h : U ≤ V) : Prop :=
  ∀ g : U →ₗ[Alg F] Rep F (F w), ∃ g' : V →ₗ[Alg F] Rep F (F w), g'.comp (Submodule.inclusion h) = g

theorem ExtP.trans {w : ι} {U V W : Submodule (Alg F) M} {h₁ : U ≤ V} {h₂ : V ≤ W}
    (e₁ : ExtP (F := F) w U V h₁) (e₂ : ExtP (F := F) w V W h₂) :
    ExtP (F := F) w U W (h₁.trans h₂) := by
  intro g
  obtain ⟨g₁, hg₁⟩ := e₁ g
  obtain ⟨g₂, hg₂⟩ := e₂ g₁
  refine ⟨g₂, ?_⟩
  rw [← hg₁, ← hg₂, LinearMap.comp_assoc]
  rfl

theorem extP_refl (w : ι) (U : Submodule (Alg F) M) : ExtP (F := F) w U U le_rfl := fun g ↦
  ⟨g, by ext u; rfl⟩

/-- One step: a simple quotient at a nonprojective label. -/
theorem extP_of_top (w : ι) {U V : Submodule (Alg F) M} (h : U ≤ V) (x : ι) (hx : ¬ D.proj x)
    (e : (V ⧸ U.comap V.subtype) ≃ₗ[Alg F] L.Top x) : ExtP (F := F) w U V h := by
  intro g
  obtain ⟨f, hf⟩ := D.extend_top x hx w (U.comap V.subtype) e
    (g.comp (Submodule.comapSubtypeEquivOfLe h).toLinearMap)
  refine ⟨f, ?_⟩
  ext u
  have := LinearMap.congr_fun hf ((Submodule.comapSubtypeEquivOfLe h).symm u)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
  rw [← this]
  rfl

/-- **`Ext¹(T, R_w) = 0` for `T` killed by `e`**, in extension form. -/
theorem extP_top_of_killed [FiniteDimensional k M] (w : ι) (U : Submodule (Alg F) M)
    (hU : D.KilledSub U) : ExtP (F := F) w U ⊤ le_top := by
  induction hn : Module.finrank k M - Module.finrank k (U.restrictScalars k) using
    Nat.strong_induction_on generalizing U with
  | _ n ih =>
    by_cases htop : U = ⊤
    · subst htop; exact extP_refl w ⊤
    -- a simple submodule of `M / U`
    have hne : (⊤ : Submodule (Alg F) (M ⧸ U)) ≠ ⊥ := by
      intro h
      apply htop
      rw [eq_top_iff]
      intro m _
      have : U.mkQ m ∈ (⊥ : Submodule (Alg F) (M ⧸ U)) := h ▸ Submodule.mem_top
      rwa [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨S, hS, -⟩ := exists_atom_le (k := k) hne
    haveI : IsSimpleModule (Alg F) S := (isSimpleModule_iff_isAtom).2 hS
    set V := S.comap U.mkQ
    have hUV : U ≤ V := fun m hm ↦ by
      simp only [V, Submodule.mem_comap, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero U).2 hm]
      exact zero_mem _
    have hUV' : U < V := by
      refine lt_of_le_of_ne hUV fun hEq ↦ hS.1 ?_
      rw [eq_bot_iff]
      intro s hs
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective U s
      have : m ∈ V := hs
      rw [← hEq] at this
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact this
    -- `V / U ≅ S ≅ L_x` with `x` nonprojective
    set φ : V →ₗ[Alg F] S := (U.mkQ.comp V.subtype).codRestrict S fun v ↦ v.2
    have hφ : Function.Surjective φ := by
      intro s
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective U (s : M ⧸ U)
      have hmV : m ∈ V := by
        change U.mkQ m ∈ S
        rw [hm]; exact s.2
      exact ⟨⟨m, hmV⟩, Subtype.ext hm⟩
    have hker : LinearMap.ker φ = U.comap V.subtype := by
      ext v
      simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · intro h
        have := congrArg Subtype.val h
        change U.mkQ (v : M) = 0 at this
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      · intro h
        apply Subtype.ext
        change U.mkQ (v : M) = 0
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact h
    obtain ⟨x, hx, ⟨eS⟩⟩ := D.exists_iso_top_nonproj (S := S) (fun y hy s ↦ by
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective U (s : M ⧸ U)
      apply Subtype.ext
      rw [Submodule.coe_smul, ← hm, ← map_smul, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero U).2 (hU y hy m)]
      rfl)
    have e₁ : ExtP (F := F) w U V hUV :=
      D.extP_of_top w hUV x hx
        ((Submodule.quotEquivOfEq _ _ hker.symm).trans ((φ.quotKerEquivOfSurjective hφ).trans eS))
    have hV : D.KilledSub V := fun y hy m ↦ hUV (hU y hy m)
    have hlt : Module.finrank k M - Module.finrank k (V.restrictScalars k) < n := by
      have h1 : Module.finrank k (U.restrictScalars k) < Module.finrank k (V.restrictScalars k) :=
        Submodule.finrank_lt_finrank_of_lt
          ((Submodule.restrictScalarsEmbedding k (Alg F) M).strictMono hUV')
      have h2 : Module.finrank k (V.restrictScalars k) ≤ Module.finrank k M :=
        Submodule.finrank_le _
      omega
    exact e₁.trans (ih _ hlt V hV rfl)

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
