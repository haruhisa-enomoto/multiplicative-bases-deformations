import MultiplicativeBasisDeformations.Foundations.EssentialSurjectivity
import MultiplicativeBasisDeformations.Foundations.DualRepresentables

/-!
# Injective labels and essential surjectivity (Proposition 2.10)

`graded-category.tex`: "Write `S_x = P_x/rad P_x` … Since
`dim C(P_y, S_x) = dim Hom_A(P_y, S_x) = δ_{xy}`, its evaluation is the simple
`A₀`-module `S_x⁰`. For the original injective `I_x = D_k(Ae_x)`, put
`N_x = ev(R_{I_x})`. … full faithfulness gives
`dim Hom_{A₀}(S_y⁰, N_x) = dim C(S_y, I_x) = δ_{xy}`. Thus `soc N_x = S_x⁰`. Also
`dim N_x e_y = dim C(P_y, I_x) = … = dim e_y A₀ e_x`. Extend the inclusion of
`soc N_x` in `D_k(A₀ e_x)` to a map `N_x → D_k(A₀ e_x)`. Its kernel is zero,
since every nonzero submodule meets the socle. Equality of dimensions then makes
it an isomorphism."

The labels `S_x`, `I_x` and the three dimension identities are the inputs
(`InjData`); they come from `mod A` through the graded Hom dimensions.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{w} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞}
  {L : LocalFamily (k := k) F} (D : MeshData F L)

namespace MeshData

theorem extA_injective : Function.Injective D.extA := fun a b h ↦ by
  rw [← D.resAlg_extA a, ← D.resAlg_extA b, h]

theorem extA_list_prod (l : List (Alg D.F0)) (hl : l ≠ []) :
    D.extA l.prod = (l.map D.extA).prod := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
      rcases l with _ | ⟨b, l⟩
      · simp
      · rw [List.prod_cons, D.extA_mul, ih (List.cons_ne_nil _ _), List.map_cons (l := b :: l),
          List.prod_cons]

/-- The local structure restricted to the projective labels. -/
def L0 : LocalFamily (k := k) D.F0 where
  rad p q := L.rad p.1 q.1
  comp_left f _ hg := L.comp_left f hg
  comp_right hf g := L.comp_right hf g
  mem_of_ne {p q} h f := L.mem_of_ne (fun e ↦ h (Subtype.ext e)) f
  diag p f := L.diag p.1 f
  id_not_mem p := L.id_not_mem p.1
  nilpotent p f hf := L.nilpotent p.1 f hf
  idealNilp := by
    obtain ⟨N, hN⟩ := L.idealNilp
    refine ⟨max N 1, fun l hl hrad ↦ ?_⟩
    have hne : l ≠ [] := by rintro rfl; simp at hl
    apply D.extA_injective
    rw [D.extA_list_prod l hne, hN _ (by simp; omega)]
    · ext y z; simp [extA]
    · intro a ha y z
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      simp only [extA]
      split_ifs with h
      · exact hrad b hb ⟨y, h.1⟩ ⟨z, h.2⟩
      · exact zero_mem _

/-- The simple and injective labels at the projective labels, with the Hom
dimensions of `graded-category.tex`. -/
structure InjData where
  S : D.PV → ι
  I : D.PV → ι
  dimS : ∀ p q : D.PV, Module.finrank k (F q.1 ⟶ F (S p)) = if q = p then 1 else 0
  dimSI : ∀ p q : D.PV, Module.finrank k (F (S q) ⟶ F (I p)) = if q = p then 1 else 0
  dimI : ∀ p q : D.PV, Module.finrank k (F q.1 ⟶ F (I p)) = Module.finrank k (F p.1 ⟶ F q.1)

variable [hfd : ∀ x y : ι, FiniteDimensional k (F x ⟶ F y)] {D} (J : InjData D)

namespace InjData

/-- `S_p⁰ = ev(S_p)`. -/
abbrev S0 (p : D.PV) := Rep D.F0 (F (J.S p))

/-- `N_p = ev(I_p)`. -/
abbrev N0 (p : D.PV) := Rep D.F0 (F (J.I p))

theorem S0_conc (p : D.PV) (m : J.S0 p) (q : D.PV) (hq : q ≠ p) : m q = 0 := by
  have h := J.dimS p q
  rw [if_neg hq] at h
  haveI := Module.finrank_zero_iff.1 h
  exact Subsingleton.elim _ _

theorem idem_smul_S0 (p : D.PV) (m : J.S0 p) : idem (F := D.F0) p • m = m := by
  ext q
  rw [idem_smul_rep]
  split_ifs with h
  · rfl
  · exact (J.S0_conc p m q h).symm

theorem finrank_S0 (p : D.PV) : Module.finrank k (J.S0 p) = 1 := by
  change Module.finrank k (∀ q : D.PV, F q.1 ⟶ F (J.S p)) = 1
  rw [Module.finrank_pi_fintype]
  simp only [J.dimS p]
  rw [Finset.sum_ite_eq']
  simp

theorem eq_smul_of_S0 (p : D.PV) {s₀ : J.S0 p} (hs₀ : s₀ ≠ 0) (m : J.S0 p) : ∃ c : k, m = c • s₀ := by
  have := (finrank_eq_one_iff_of_nonzero' s₀ hs₀).1 (J.finrank_S0 p) m
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

instance (p : D.PV) : IsSimpleModule (Alg D.F0) (J.S0 p) := by
  haveI : Nontrivial (J.S0 p) := Module.nontrivial_of_finrank_eq_succ (J.finrank_S0 p)
  refine { eq_bot_or_eq_top := fun N ↦ ?_ }
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · right
    obtain ⟨m, hmN, hm⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, rfl⟩ := J.eq_smul_of_S0 p hm x
    rw [← algebraMap_smul (Alg D.F0) c m]
    exact N.smul_mem _ hmN

end InjData

/-- One-object families. -/
abbrev uZ (x : ι) : Unit → ι := fun _ ↦ x

/-- `R⁰_X ≅ ⊕_{Unit} R⁰_X`. -/
def eU (X : 𝒞) : Rep D.F0 X ≃ₗ[Alg D.F0] (Unit → Rep D.F0 X) :=
  (LinearEquiv.funUnique Unit (Alg D.F0) (Rep D.F0 X)).symm

include hfd in
/-- **Maps between evaluations of labels are evaluations of morphisms.** -/
theorem hom_eq_repMap (x y : ι) (g : Rep D.F0 (F x) →ₗ[Alg D.F0] Rep D.F0 (F y)) :
    ∃ h : F x ⟶ F y, ∀ m, g m = repMap h m := by
  obtain ⟨f, hf⟩ := D.evMap_surjective (Z := uZ x) (Z' := uZ y)
    ((D.eU (F y)).toLinearMap.comp (g.comp (D.eU (F x)).symm.toLinearMap))
  refine ⟨f () (), fun m ↦ ?_⟩
  have := congrFun (LinearMap.congr_fun hf (D.eU (F x) m)) ()
  rw [evMap_apply, Fintype.sum_unique] at this
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
  exact this.symm

include hfd in
theorem repMap_eq_zero (x y : ι) (h : F x ⟶ F y) (hz : ∀ m : Rep D.F0 (F x), repMap h m = 0) :
    h = 0 := by
  have : D.evMap (fun _ _ ↦ h : Mat F (uZ x) (uZ y)) = 0 := by
    refine LinearMap.ext fun m ↦ funext fun j' ↦ ?_
    rw [evMap_apply, Fintype.sum_unique]
    exact hz _
  exact congrFun (congrFun (D.evMap_injective this) ()) ()

namespace InjData

/-- **`ev(I_p) ≅ D(A₀ e_p)`** (`graded-category.tex`). -/
theorem N0_equiv (p : D.PV) : Nonempty (J.N0 p ≃ₗ[Alg D.F0] DRep (k := k) D.F0 p) := by
  -- the socle map `S_p⁰ → N_p`
  have h1 : Module.finrank k (F (J.S p) ⟶ F (J.I p)) = 1 := by rw [J.dimSI p p, if_pos rfl]
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : F (J.S p) ⟶ F (J.I p), h₀ ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero).1 (by rw [h1]; exact Nat.one_pos)
  haveI : Nontrivial (J.S0 p) := Module.nontrivial_of_finrank_eq_succ (J.finrank_S0 p)
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : J.S0 p)
  set t : J.N0 p := repMap (F := D.F0) h₀ s₀
  have ht : t ≠ 0 := by
    intro h0
    apply hh₀
    refine D.repMap_eq_zero _ _ h₀ fun m ↦ ?_
    obtain ⟨c, rfl⟩ := J.eq_smul_of_S0 p hs₀ m
    have e : repMap (F := D.F0) h₀ (c • s₀) = c • t := by
      ext y; simp [t, Linear.smul_comp]
    rw [e, h0, smul_zero]
  obtain ⟨lam, hlam⟩ : ∃ lam : Module.Dual k (J.N0 p), lam t ≠ 0 := by
    by_contra hall
    push Not at hall
    exact ht ((Module.forall_dual_apply_eq_zero_iff k t).1 hall)
  set θ : J.N0 p →ₗ[Alg D.F0] DRep (k := k) D.F0 p := theta p lam
  have hidt : idem (F := D.F0) p • t = t := by
    change idem p • repMap (F := D.F0) h₀ s₀ = repMap (F := D.F0) h₀ s₀
    rw [← map_smul, J.idem_smul_S0]
  have hθt : θ t ≠ 0 := by
    intro h0
    have := congrArg (fun φ : DRep (k := k) D.F0 p ↦ φ p (𝟙 _)) h0
    simp only [θ] at this
    rw [theta_apply, elemAt_id, hidt] at this
    exact hlam this
  -- injectivity: every nonzero submodule meets the socle
  have hinj : Function.Injective θ := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hker
    obtain ⟨T, hT, hTk⟩ := exists_atom_le (k := k) hker
    haveI : IsSimpleModule (Alg D.F0) T := (isSimpleModule_iff_isAtom).2 hT
    haveI : Nontrivial T := IsSimpleModule.nontrivial (Alg D.F0) T
    obtain ⟨t', ht'⟩ := exists_ne (0 : T)
    obtain ⟨q, hq⟩ : ∃ q, idem (F := D.F0) q • t' ≠ 0 := by
      by_contra hall
      push Not at hall
      exact ht' (eq_zero_of_idem (F := D.F0) hall)
    obtain ⟨eT⟩ := D.L0.iso_top_of_idem q t' hq
    haveI : Nontrivial (J.S0 q) := Module.nontrivial_of_finrank_eq_succ (J.finrank_S0 q)
    obtain ⟨s₁, hs₁⟩ := exists_ne (0 : J.S0 q)
    obtain ⟨eS⟩ := D.L0.iso_top_of_idem q s₁ (by rw [J.idem_smul_S0]; exact hs₁)
    set σ : J.S0 q ≃ₗ[Alg D.F0] T := eS.trans eT.symm
    obtain ⟨h', hh'⟩ := D.hom_eq_repMap _ _ (T.subtype.comp σ.toLinearMap)
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' h₀ hh₀).1 h1 h'
      have hgs : ((σ s₀ : T) : J.N0 q) = c • t := by
        have := hh' s₀
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply] at this
        rw [this, ← hc, repMap_smul_apply]
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hgs
        exact hs₀ (σ.injective (Subtype.ext (by rw [hgs, map_zero]; rfl)))
      have htT : t ∈ T := by
        have : t = c⁻¹ • ((σ s₀ : T) : J.N0 q) := by rw [hgs, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [this, ← algebraMap_smul (Alg D.F0) c⁻¹]
        exact T.smul_mem _ (σ s₀).2
      exact hθt (hTk htT)
    · have h0 : Module.finrank k (F (J.S q) ⟶ F (J.I p)) = 0 := by rw [J.dimSI p q, if_neg hqp]
      haveI := Module.finrank_zero_iff.1 h0
      have hz : h' = 0 := Subsingleton.elim _ _
      have := hh' s₁
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, hz,
        repMap_zero, LinearMap.zero_apply] at this
      exact hs₁ (σ.injective (Subtype.ext (by rw [this, map_zero]; rfl)))
  -- equal dimensions
  haveI : FiniteDimensional k (DRep (k := k) D.F0 p) :=
    inferInstanceAs (FiniteDimensional k (∀ q : D.PV, Module.Dual k (F p.1 ⟶ F q.1)))
  have hdim : Module.finrank k (J.N0 p) = Module.finrank k (DRep (k := k) D.F0 p) := by
    change Module.finrank k (∀ q : D.PV, F q.1 ⟶ F (J.I p)) =
      Module.finrank k (∀ q : D.PV, Module.Dual k (F p.1 ⟶ F q.1))
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [J.dimI p q, Subspace.dual_finrank_eq]
  have hbij : Function.Bijective θ := by
    refine ⟨hinj, ?_⟩
    have := LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := θ.restrictScalars k)
    exact this.1 hinj
  exact ⟨LinearEquiv.ofBijective θ hbij⟩

include J in
/-- **Evaluation is essentially surjective** (Lemma 2.9 with Proposition 2.10):
every finite-dimensional `A₀`-module is the evaluation of a family of labels. -/
theorem essSurj {X : Type*} [AddCommGroup X] [Module k X] [Module (Alg D.F0) X]
    [IsScalarTower k (Alg D.F0) X] [FiniteDimensional k X] :
    ∃ (μ : Type) (_ : Fintype μ) (_ : DecidableEq μ) (W : μ → ι),
      Nonempty (X ≃ₗ[Alg D.F0] D.EZ W) := by
  -- an injective copresentation `0 → X → J⁰ → J¹`
  obtain ⟨n, ιX, hιX⟩ := exists_embedding (k := k) (F := D.F0) (X := X)
  set J₀ := ∀ c : D.PV × Fin n, DRep (k := k) D.F0 c.1
  set C := J₀ ⧸ LinearMap.range ιX
  obtain ⟨n', ιC, hιC⟩ := exists_embedding (k := k) (F := D.F0) (X := C)
  set J₁ := ∀ c : D.PV × Fin n', DRep (k := k) D.F0 c.1
  set g : J₀ →ₗ[Alg D.F0] J₁ := ιC.comp (LinearMap.range ιX).mkQ
  have hkerg : LinearMap.ker g = LinearMap.range ιX := by
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hιC, Submodule.comap_bot, Submodule.ker_mkQ]
  -- the injectives are evaluations of the injective labels
  set I₀ : D.PV × Fin n → ι := fun c ↦ J.I c.1
  set I₁ : D.PV × Fin n' → ι := fun c ↦ J.I c.1
  set e₀ : J₀ ≃ₗ[Alg D.F0] D.EZ I₀ :=
    LinearEquiv.piCongrRight fun c ↦ (Classical.choice (J.N0_equiv c.1)).symm
  set e₁ : J₁ ≃ₗ[Alg D.F0] D.EZ I₁ :=
    LinearEquiv.piCongrRight fun c ↦ (Classical.choice (J.N0_equiv c.1)).symm
  obtain ⟨f, hf⟩ := D.evMap_surjective (Z := I₀) (Z' := I₁)
    (e₁.toLinearMap.comp (g.comp e₀.symm.toLinearMap))
  have hker : (LinearMap.ker g).map e₀.toLinearMap = LinearMap.ker (D.evMap f) := by
    ext y
    rw [hf, Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff]
  obtain ⟨μ, _, _, W, ⟨eW⟩⟩ := D.ker_evMap_equiv f
  refine ⟨μ, inferInstance, inferInstance, W, ⟨?_⟩⟩
  exact (((LinearEquiv.ofInjective ιX hιX).trans (LinearEquiv.ofEq _ _ hkerg.symm)).trans
    (e₀.submoduleMap (LinearMap.ker g))).trans ((LinearEquiv.ofEq _ _ hker).trans eW)

end InjData

end MeshData

end CatAlg

end MultiplicativeBasisDeformations
