module

public import MultiplicativeBasisDeformations.Foundations.ARPrime
public import MultiplicativeBasisDeformations.Foundations.Char2A0
public import MultiplicativeBasisDeformations.Foundations.IntegralA0

/-!
# `A⁽²⁾ = 𝔽₂P` (Section 10)

`integral-deformations.tex`: "Its projective corner `End(⊕_x P_x)^op` is `A⁽²⁾`: a nonzero
homogeneous projective Hom is one-dimensional over `𝔽₂`, and every nonzero product coefficient is
one."

The form functor of `C⁽²⁾ → k(Γ_A)` gives an injective ring map `ι₂ : A⁽²⁾ → A₀` on the
projective corners (`ι₂`), and `𝔽₂`-independent families stay `k`-independent
(`linearIndependent_ι₂`). For each ray `t` of `A₀` (with its normed basis vector `b_t`) the
corner of `A⁽²⁾` at the endpoints of `t` in the length degree of `t` contains exactly one
nonzero vector `e_t` (`eT`); `ι₂ e_t` is a nonzero multiple of `b_t`. The `e_t` form a
multiplicative basis of `A⁽²⁾` with the multiplication table of `A₀`, hence
`𝔽₂P ≅ A⁽²⁾` (`Θ₂`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe w

namespace RaySys

namespace Mult

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] [DecidableEq R] (M : Mult V R)
  {K : Type} [Field K] {Λ : Type*} [Ring Λ] [Algebra K Λ] (e : Module.Basis R K Λ)
  (he : ∀ r s, e r * e s = (M.mul r s).elim 0 e) (h1 : ∑ v, e (M.e v) = 1)

/-- The linear equivalence `KP ≃ Λ` of a basis with the multiplication table of `P`. -/
def linOf : M.Lin K ≃ₗ[K] Λ := (M.basis K).equiv e (Equiv.refl R)

theorem linOf_b (r : R) : M.linOf e (M.b K r) = e r := by
  rw [linOf, ← basis_apply, Module.Basis.equiv_apply, Equiv.refl_apply]

include he in
theorem linOf_mul (x y : M.Lin K) : M.linOf e (x * y) = M.linOf e x * M.linOf e y := by
  have key : ∀ r s, M.linOf e (M.b K r * M.b K s) = e r * e s := by
    intro r s
    rw [b_mul, he]
    cases M.mul r s with
    | none => simp
    | some t => simp only [Option.elim_some, linOf_b]
  have hspan : ∀ z : M.Lin K, z ∈ Submodule.span K (Set.range (M.b K)) :=
    fun z ↦ by rw [span_b]; trivial
  have hy : ∀ r, M.linOf e (M.b K r * y) = e r * M.linOf e y := by
    intro r
    induction hspan y using Submodule.span_induction with
    | mem z hz => obtain ⟨s, rfl⟩ := hz; rw [key, linOf_b]
    | zero => simp
    | add z z' _ _ h1 h2 => rw [mul_add, map_add, h1, h2, map_add, mul_add]
    | smul t z _ h => rw [mul_smul_comm, map_smul, h, map_smul, mul_smul_comm]
  induction hspan x using Submodule.span_induction with
  | mem z hz => obtain ⟨r, rfl⟩ := hz; rw [hy, linOf_b]
  | zero => simp
  | add z z' _ _ h1 h2 => rw [add_mul, map_add, h1, h2, map_add, add_mul]
  | smul t z _ h => rw [smul_mul_assoc, map_smul, h, map_smul, smul_mul_assoc]

/-- **An algebra with a basis carrying the multiplication table of `P` is `KP`.** -/
def algOf : M.Lin K ≃ₐ[K] Λ :=
  AlgEquiv.ofLinearEquiv (M.linOf e) (by
      rw [← sum_b_e, map_sum, ← h1]
      exact Finset.sum_congr rfl fun v _ ↦ M.linOf_b e _)
    (M.linOf_mul e he)

theorem algOf_b (r : R) : M.algOf e he h1 (M.b K r) = e r := M.linOf_b e r

end Mult

end RaySys

namespace IndSkeleton

open ScalarMeshCategory CatAlg MeshWalk

attribute [local instance] ZMod.algebra

variable {k A : Type w} [Field k] [IsAlgClosed k] [CharP k 2] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-- The form functor `C⁽²⁾ → k(Γ_A)` on morphisms. -/
abbrev Fm2 {x y : S.ARVertex} (φ : ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) : S.meshObj b x ⟶ S.meshObj b y :=
  Fm (S.oneC (ZMod 2)) S.oneK (S.arCoefficients b) (S.arMu b) (S.arEta b) (S.arGauge b) φ

/-- The retraction `k(Γ_A) → C⁽²⁾` along `θ`. -/
abbrev ret2 (θ : k →ₗ[ZMod 2] ZMod 2) {x y : S.ARVertex} (ψ : S.meshObj b x ⟶ S.meshObj b y) :
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶ ScalarMeshCategory.obj (S.oneC (ZMod 2)) y :=
  retF (S.oneC (ZMod 2)) S.oneK (S.arCoefficients b) (S.arMu b) (S.arEta b) (S.arGauge b) θ ψ

section Wrap

variable {x y z : S.ARVertex}

theorem Fm2_add (φ φ' : ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) : S.Fm2 b (φ + φ') = S.Fm2 b φ + S.Fm2 b φ' :=
  Fm_add _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) _ _

theorem Fm2_zero : S.Fm2 b (0 : ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) = 0 :=
  Fm_zero _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b)

theorem Fm2_smul (a : ZMod 2) (φ : ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) :
    S.Fm2 b (a • φ) = algebraMap (ZMod 2) k a • S.Fm2 b φ :=
  Fm_smul _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) _ _

theorem Fm2_sum {κ : Type*} (s : Finset κ) (φ : κ → (ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) y)) :
    S.Fm2 b (∑ i ∈ s, φ i) = ∑ i ∈ s, S.Fm2 b (φ i) :=
  Fm_sum _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) _ _

theorem Fm2_comp (φ : ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) y)
    (φ' : ScalarMeshCategory.obj (S.oneC (ZMod 2)) y ⟶ ScalarMeshCategory.obj (S.oneC (ZMod 2)) z) :
    S.Fm2 b (φ ≫ φ') = S.Fm2 b φ ≫ S.Fm2 b φ' :=
  Fm_comp _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) _ _

theorem Fm2_id : S.Fm2 b (𝟙 (ScalarMeshCategory.obj (S.oneC (ZMod 2)) x)) = 𝟙 (S.meshObj b x) :=
  Fm_id _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) x

theorem Fm2_injective : Function.Injective (S.Fm2 b (x := x) (y := y)) :=
  Fm_injective _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b)

theorem Fm2_pathMor (p : Quiver.Path x y) :
    S.Fm2 b (pathMor (S.oneC (ZMod 2)) p) =
      ((pathWt (S.arMu b) p : kˣ) : k) • pathMor (S.arCoefficients b) p := by
  rw [Fm2, Fm, redE_pathMor S.hredOne, gaugeQ_pathMor]

variable (θ : k →ₗ[ZMod 2] ZMod 2)

theorem ret2_smul_Fm2 (t : k) (φ : ScalarMeshCategory.obj (S.oneC (ZMod 2)) x ⟶
    ScalarMeshCategory.obj (S.oneC (ZMod 2)) y) : S.ret2 b θ (t • S.Fm2 b φ) = θ t • φ :=
  retF_smul_Fm _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) θ t φ

theorem ret2_add (ψ ψ' : S.meshObj b x ⟶ S.meshObj b y) :
    S.ret2 b θ (ψ + ψ') = S.ret2 b θ ψ + S.ret2 b θ ψ' :=
  retF_add _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) θ ψ ψ'

theorem ret2_zero : S.ret2 b θ (0 : S.meshObj b x ⟶ S.meshObj b y) = 0 :=
  retF_zero _ _ _ S.hredOne (S.arMu b) (S.arEta b) (S.arGauge b) θ

end Wrap

/-- The prime-field corner algebra `A⁽²⁾`. -/
abbrev A2 := (Alg (S.primeMeshData b).F0)ᵐᵒᵖ

/-- The corner algebra `A₀`. -/
abbrev Ak := (Alg (S.arMeshData b).F0)ᵐᵒᵖ

/-- **The comparison `ι₂ : A⁽²⁾ → A₀`**, entrywise the form functor. -/
def ι₂ (a : S.A2 b) : S.Ak b :=
  MulOpposite.op fun p q ↦ S.Fm2 b (a.unop p q)

theorem ι₂_apply (a : S.A2 b) (p q : (S.arMeshData b).PV) :
    (S.ι₂ b a).unop p q = S.Fm2 b (a.unop p q) := rfl

theorem ι₂_add (a a' : S.A2 b) : S.ι₂ b (a + a') = S.ι₂ b a + S.ι₂ b a' := by
  apply MulOpposite.unop_injective; ext p q
  simp only [MulOpposite.unop_add, CatAlg.add_apply, ι₂_apply]
  exact S.Fm2_add b _ _

theorem ι₂_zero : S.ι₂ b 0 = 0 := by
  apply MulOpposite.unop_injective; ext p q
  simp only [MulOpposite.unop_zero, CatAlg.zero_apply, ι₂_apply]
  exact S.Fm2_zero b

theorem ι₂_smul (a : ZMod 2) (x : S.A2 b) : S.ι₂ b (a • x) = algebraMap (ZMod 2) k a • S.ι₂ b x := by
  apply MulOpposite.unop_injective; ext p q
  simp only [MulOpposite.unop_smul, CatAlg.smul_apply, ι₂_apply]
  exact S.Fm2_smul b _ _

theorem ι₂_sum {κ : Type*} (s : Finset κ) (f : κ → S.A2 b) :
    S.ι₂ b (∑ i ∈ s, f i) = ∑ i ∈ s, S.ι₂ b (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ι₂_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ι₂_add, ih]

theorem ι₂_mul (a a' : S.A2 b) : S.ι₂ b (a * a') = S.ι₂ b a * S.ι₂ b a' := by
  apply MulOpposite.unop_injective; ext p q
  show S.Fm2 b ((a * a').unop p q) = ((S.ι₂ b a').unop * (S.ι₂ b a).unop) p q
  rw [MulOpposite.unop_mul, mul_apply, mul_apply, S.Fm2_sum b]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  exact S.Fm2_comp b _ _

theorem ι₂_one : S.ι₂ b 1 = 1 := by
  apply MulOpposite.unop_injective; ext p q
  rw [ι₂_apply, MulOpposite.unop_one, one_apply, MulOpposite.unop_one, one_apply, idTo, idTo]
  split_ifs with h
  · subst h; exact S.Fm2_id b
  · exact S.Fm2_zero b

/-- The retraction on corner algebras. -/
def retA (θ : k →ₗ[ZMod 2] ZMod 2) (z : S.Ak b) : S.A2 b :=
  MulOpposite.op fun p q ↦ S.ret2 b θ (z.unop p q)

theorem retA_smul_ι₂ (θ : k →ₗ[ZMod 2] ZMod 2) (t : k) (a : S.A2 b) :
    S.retA b θ (t • S.ι₂ b a) = θ t • a := by
  apply MulOpposite.unop_injective; ext p q
  simp only [retA, MulOpposite.unop_smul, CatAlg.smul_apply, MulOpposite.unop_op]
  exact S.ret2_smul_Fm2 b θ t _

theorem retA_add (θ : k →ₗ[ZMod 2] ZMod 2) (z z' : S.Ak b) :
    S.retA b θ (z + z') = S.retA b θ z + S.retA b θ z' := by
  apply MulOpposite.unop_injective; ext p q
  simp only [retA, MulOpposite.unop_add, CatAlg.add_apply, MulOpposite.unop_op]
  exact S.ret2_add b θ _ _

theorem retA_zero (θ : k →ₗ[ZMod 2] ZMod 2) : S.retA b θ 0 = 0 := by
  apply MulOpposite.unop_injective; ext p q
  simp only [retA, MulOpposite.unop_zero, CatAlg.zero_apply, MulOpposite.unop_op]
  exact S.ret2_zero b θ

theorem retA_sum (θ : k →ₗ[ZMod 2] ZMod 2) {κ : Type*} (s : Finset κ) (f : κ → S.Ak b) :
    S.retA b θ (∑ i ∈ s, f i) = ∑ i ∈ s, S.retA b θ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [retA_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, retA_add, ih]

theorem ι₂_injective : Function.Injective (S.ι₂ b) := by
  obtain ⟨θ, h1⟩ := exists_retraction (K := ZMod 2) (k := k)
  intro a a' e
  have := congrArg (S.retA b θ) (congrArg ((1 : k) • ·) e)
  rwa [retA_smul_ι₂, retA_smul_ι₂, h1, one_smul, one_smul] at this

/-- **`𝔽₂`-independent families stay `k`-independent.** -/
theorem linearIndependent_ι₂ {κ : Type*} {f : κ → S.A2 b} (hf : LinearIndependent (ZMod 2) f) :
    LinearIndependent k (fun i ↦ S.ι₂ b (f i)) := by
  rw [linearIndependent_iff'] at hf ⊢
  intro s g hg i hi
  have key : ∀ θ : k →ₗ[ZMod 2] ZMod 2, θ (g i) = 0 := by
    intro θ
    have h := congrArg (S.retA b θ) hg
    rw [retA_sum, retA_zero] at h
    simp only [retA_smul_ι₂] at h
    exact hf s (fun j ↦ θ (g j)) h i hi
  exact (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (g i)).1 key


/-! ### The basis of `A⁽²⁾` over the rays of `A₀` -/

theorem ι₂_unitM {x y : (S.arMeshData b).PV}
    (f : ScalarMeshCategory.obj (S.oneC (ZMod 2)) x.1 ⟶ ScalarMeshCategory.obj (S.oneC (ZMod 2)) y.1) :
    S.ι₂ b (MulOpposite.op (unitM (F := (S.primeMeshData b).F0) x y f)) =
      MulOpposite.op (unitM (F := (S.arMeshData b).F0) x y (S.Fm2 b f)) := by
  have hid : ∀ p q : (S.arMeshData b).PV,
      S.Fm2 b (idTo (F := (S.primeMeshData b).F0) p q) = idTo (F := (S.arMeshData b).F0) p q := by
    intro p q
    by_cases h : p = q
    · subst h; rw [idTo_self, idTo_self]; exact S.Fm2_id b
    · rw [idTo_ne h, idTo_ne h]; exact S.Fm2_zero b
  apply MulOpposite.unop_injective; ext p q
  rw [ι₂_apply, MulOpposite.unop_op, MulOpposite.unop_op, unitM_apply, unitM_apply, S.Fm2_comp b,
    S.Fm2_comp b, hid, hid]

theorem idem_eq_unitM {ι : Type} [Fintype ι] [DecidableEq ι] {𝒞 : Type*} [Category 𝒞]
    [Preadditive 𝒞] {F : ι → 𝒞} (x : ι) : idem (F := F) x = unitM x x (𝟙 (F x)) := by
  apply CatAlg.ext; intro p q
  simp [unitM_apply, idem, colAlg, unit]

theorem ι₂_eP (x : (S.arMeshData b).PV) : S.ι₂ b (eP (S.primeMeshData b) x) = eP (S.arMeshData b) x := by
  rw [eP, eP, idem_eq_unitM, idem_eq_unitM, ι₂_unitM, S.Fm2_id b]

/-- **Two nonzero elements of `A⁽²⁾` over the same line of `A₀` are equal.** -/
theorem eq_of_ι₂_mem_span {a a' : S.A2 b} {z : S.Ak b} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (h : S.ι₂ b a ∈ k ∙ z) (h' : S.ι₂ b a' ∈ k ∙ z) : a = a' := by
  by_contra hne
  have hF : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have hli : LinearIndependent (ZMod 2) ![a, a'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases hF s with rfl | rfl <;> rcases hF t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at hst; exact absurd hst ha'
    · rw [zero_smul, one_smul, add_zero] at hst; exact absurd hst ha
    · rw [one_smul, one_smul, add_eq_zero_iff_eq_neg, ZModModule.neg_eq_self] at hst
      exact absurd hst hne
  have hk := S.linearIndependent_ι₂ b hli
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 h
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.1 h'
  have hk' : LinearIndependent k ![S.ι₂ b a, S.ι₂ b a'] := by
    convert hk using 1; ext i; fin_cases i <;> rfl
  have := (LinearIndependent.pair_iff.1 hk') β (-α) (by
    rw [← hα, ← hβ, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm β α, add_neg_cancel])
  have hα0 : α = 0 := neg_eq_zero.1 this.2
  apply ha
  apply S.ι₂_injective b
  rw [ι₂_zero, ← hα, hα0, zero_smul]

section Table

attribute [local instance] Classical.decEq

variable [∀ x y : S.ARVertex, Subsingleton (x ⟶ y)]
  [∀ x y : S.ARVertex, FiniteDimensional k (MeshWalk.meshFam S.arTranslationQuiver
    (S.arCoefficients b) x ⟶ MeshWalk.meshFam S.arTranslationQuiver (S.arCoefficients b) y)]
  [∀ x y : S.ARVertex, FiniteDimensional (ZMod 2) (MeshWalk.meshFam S.arTranslationQuiver
    (S.oneC (ZMod 2)) x ⟶ MeshWalk.meshFam S.arTranslationQuiver (S.oneC (ZMod 2)) y)]
  (v₀ : S.ARVertex) (hF : IsRepresentationFinite k (Alg (S.arMeshData b).F0)ᵐᵒᵖ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWt S.arTranslationQuiver ℤ)

instance : Fintype (RayA0 (S.arMeshData b) v₀) := MeshWalk.instFintypeRayA0 (S.arMeshData b) v₀

/-- The ray degree. -/
abbrev dP (r : RayA0 (S.arMeshData b) v₀) : ℤ :=
  (SysD (S.arMeshData b) v₀ hF Wd).P.deg ((SysD (S.arMeshData b) v₀ hF Wd).P.wt r)

theorem exists_eT (r : RayA0 (S.arMeshData b) v₀) :
    ∃ a : S.A2 b, (lenA0 (S.primeMeshData b) (hfin2 (c := S.oneC (ZMod 2)))).IsHom
      (S.dP b v₀ hF Wd r).toNat a ∧
      ∃ t : k, t ≠ 0 ∧ S.ι₂ b a = t • basisR (S.arMeshData b) v₀ hF r := by
  obtain ⟨⟨x, y, g⟩, hr⟩ := r
  have hv := deckV_ne (S.arMeshData b) v₀ hF x y g hr
  -- a path of degree `g` with nonzero image
  obtain ⟨p, hp, hp0⟩ : ∃ p : Quiver.Path x.1 y.1, (degW S.arTranslationQuiver v₀).deg p = g ∧
      pathMor (S.arCoefficients b) p ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hv
    have hf : deckV (S.arMeshData b) v₀ hF x y g ∈
        wPart (S.arCoefficients b) (degW S.arTranslationQuiver v₀) g x.1 y.1 :=
      (isHom_iff (Q := S.arTranslationQuiver) (c := S.arCoefficients b) (v₀ := v₀)).1
        ((HomGrading.mem_part_iff _).1 (deckV_mem (S.arMeshData b) v₀ hF x y g))
    have := wPart_le_span (Q := S.arTranslationQuiver) (c := S.arCoefficients b) (v₀ := v₀) g
      x.1 y.1 hf
    have hsub : Submodule.span k {f | ∃ p : Quiver.Path x.1 y.1,
        (degW S.arTranslationQuiver v₀).deg p = g ∧ pathMor (S.arCoefficients b) p = f} ≤ ⊥ :=
      Submodule.span_le.2 fun f hf ↦ by
        obtain ⟨p, hp, rfl⟩ := hf; exact (Submodule.mem_bot k).2 (hne p hp)
    exact (Submodule.mem_bot k).1 (hsub this)
  have hpm : pathMor (S.arCoefficients b) p ∈ (D0 S.arTranslationQuiver (S.arCoefficients b) v₀
      (S.arMeshData b)).part g x y := by
    refine (HomGrading.mem_part_iff _).2 ((isHom_iff (Q := S.arTranslationQuiver)
      (c := S.arCoefficients b) (v₀ := v₀)).2 ?_)
    rw [← hp]; exact pathMor_mem_wPart p
  obtain ⟨α, hα⟩ := deckV_span (S.arMeshData b) v₀ hF x y g _ hpm
  have hα0 : α ≠ 0 := by rintro rfl; rw [zero_smul] at hα; exact hp0 hα
  refine ⟨MulOpposite.op (unitM (F := (S.primeMeshData b).F0) x y
    (pathMor (S.oneC (ZMod 2)) p)), ?_, ((pathWt (S.arMu b) p : kˣ) : k) * α,
    mul_ne_zero (Units.ne_zero _) hα0, ?_⟩
  · rw [dP, SysD_deg_wt (S.arMeshData b) v₀ hF Wd ⟨(x, y, g), hr⟩ hp, Int.toNat_natCast]
    exact unitM_isHom (S.primeMeshData b) (hfin2 (c := S.oneC (ZMod 2)))
      (pathMor_mem_degreePart _ p)
  · rw [ι₂_unitM, S.Fm2_pathMor b, hα, smul_smul, unitM_smul, MulOpposite.op_smul, basisR_apply]

/-- **The basis vector `e_t` of `A⁽²⁾`** over the ray `t` of `A₀`. -/
def eT (r : RayA0 (S.arMeshData b) v₀) : S.A2 b := (S.exists_eT b v₀ hF Wd r).choose

theorem eT_isHom (r : RayA0 (S.arMeshData b) v₀) :
    (lenA0 (S.primeMeshData b) (hfin2 (c := S.oneC (ZMod 2)))).IsHom (S.dP b v₀ hF Wd r).toNat
      (S.eT b v₀ hF Wd r) :=
  (S.exists_eT b v₀ hF Wd r).choose_spec.1

theorem eT_line (r : RayA0 (S.arMeshData b) v₀) :
    ∃ t : k, t ≠ 0 ∧ S.ι₂ b (S.eT b v₀ hF Wd r) = t • basisR (S.arMeshData b) v₀ hF r :=
  (S.exists_eT b v₀ hF Wd r).choose_spec.2

theorem eT_mem (r : RayA0 (S.arMeshData b) v₀) :
    S.ι₂ b (S.eT b v₀ hF Wd r) ∈ k ∙ basisR (S.arMeshData b) v₀ hF r := by
  obtain ⟨t, -, ht⟩ := S.eT_line b v₀ hF Wd r
  rw [ht]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem eT_ne_zero (r : RayA0 (S.arMeshData b) v₀) : S.eT b v₀ hF Wd r ≠ 0 := by
  obtain ⟨t, ht, he⟩ := S.eT_line b v₀ hF Wd r
  intro h0
  rw [h0, ι₂_zero] at he
  exact (smul_ne_zero ht ((basisR (S.arMeshData b) v₀ hF).ne_zero r)) he.symm

theorem basisR_mul (r s : RayA0 (S.arMeshData b) v₀) :
    basisR (S.arMeshData b) v₀ hF r * basisR (S.arMeshData b) v₀ hF s =
      ((SysD (S.arMeshData b) v₀ hF Wd).P.mul r s).elim 0 (basisR (S.arMeshData b) v₀ hF) := by
  rw [← ΘD_b (S.arMeshData b) v₀ hF Wd, ← ΘD_b (S.arMeshData b) v₀ hF Wd, ← map_mul, (SysD (S.arMeshData b) v₀ hF Wd).P.b_mul]
  cases (SysD (S.arMeshData b) v₀ hF Wd).P.mul r s with
  | none => simp
  | some t => exact ΘD_b (S.arMeshData b) v₀ hF Wd t

/-- **The `e_t` multiply by the table of `A₀`.** -/
theorem eT_mul (r s : RayA0 (S.arMeshData b) v₀) :
    S.eT b v₀ hF Wd r * S.eT b v₀ hF Wd s =
      ((SysD (S.arMeshData b) v₀ hF Wd).P.mul r s).elim 0 (S.eT b v₀ hF Wd) := by
  obtain ⟨α, hα0, hα⟩ := S.eT_line b v₀ hF Wd r
  obtain ⟨β, hβ0, hβ⟩ := S.eT_line b v₀ hF Wd s
  have e : S.ι₂ b (S.eT b v₀ hF Wd r * S.eT b v₀ hF Wd s) =
      (α * β) • ((SysD (S.arMeshData b) v₀ hF Wd).P.mul r s).elim 0
        (basisR (S.arMeshData b) v₀ hF) := by
    rw [ι₂_mul, hα, hβ, smul_mul_smul_comm, S.basisR_mul b v₀ hF Wd]
  cases h : (SysD (S.arMeshData b) v₀ hF Wd).P.mul r s with
  | none =>
      rw [h, Option.elim_none, smul_zero, ← S.ι₂_zero b] at e
      exact S.ι₂_injective b e
  | some t =>
      rw [h, Option.elim_some] at e
      refine S.eq_of_ι₂_mem_span b (fun h0 ↦ ?_) (S.eT_ne_zero b v₀ hF Wd t)
        (by rw [e]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
        (S.eT_mem b v₀ hF Wd t)
      rw [h0, ι₂_zero] at e
      exact smul_ne_zero (mul_ne_zero hα0 hβ0) ((basisR (S.arMeshData b) v₀ hF).ne_zero t) e.symm

theorem eT_e (x : (S.arMeshData b).PV) :
    S.eT b v₀ hF Wd ((SysD (S.arMeshData b) v₀ hF Wd).P.e x) = eP (S.primeMeshData b) x := by
  have hb : basisR (S.arMeshData b) v₀ hF ((SysD (S.arMeshData b) v₀ hF Wd).P.e x) =
      eP (S.arMeshData b) x := by
    change basisR (S.arMeshData b) v₀ hF (eR (S.arMeshData b) v₀ hF x) = _
    rw [basisR_eR, eP, idem_eq_unitM]
  refine S.eq_of_ι₂_mem_span b (S.eT_ne_zero b v₀ hF Wd _) (fun h0 ↦ ?_) (S.eT_mem b v₀ hF Wd _)
    (by rw [ι₂_eP, ← hb]; exact Submodule.mem_span_singleton_self _)
  have := congrArg (S.ι₂ b) h0
  rw [ι₂_eP, ι₂_zero, ← hb] at this
  exact (basisR (S.arMeshData b) v₀ hF).ne_zero _ this

theorem linearIndependent_eT : LinearIndependent (ZMod 2) (S.eT b v₀ hF Wd) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  choose t ht0 ht using S.eT_line b v₀ hF Wd
  have h := congrArg (S.ι₂ b) hg
  rw [ι₂_sum, ι₂_zero] at h
  simp only [ι₂_smul, ht, smul_smul] at h
  have := linearIndependent_iff'.1 (basisR (S.arMeshData b) v₀ hF).linearIndependent s _ h i hi
  rcases mul_eq_zero.1 this with h1 | h1
  · exact (algebraMap (ZMod 2) k).injective (by rw [h1, map_zero])
  · exact absurd h1 (ht0 i)

theorem span_eT : ⊤ ≤ Submodule.span (ZMod 2) (Set.range (S.eT b v₀ hF Wd)) := by
  rintro a -
  obtain ⟨θ, h1⟩ := exists_retraction (K := ZMod 2) (k := k)
  choose t ht0 ht using S.eT_line b v₀ hF Wd
  have hsum := (basisR (S.arMeshData b) v₀ hF).sum_repr (S.ι₂ b a)
  have e : S.ι₂ b a = ∑ r : RayA0 (S.arMeshData b) v₀, ((basisR (S.arMeshData b) v₀ hF).repr (S.ι₂ b a) r * (t r)⁻¹) •
      S.ι₂ b (S.eT b v₀ hF Wd r) := by
    conv_lhs => rw [← hsum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [ht, smul_smul, mul_assoc, inv_mul_cancel₀ (ht0 r), mul_one]
  have ha := congrArg (S.retA b θ) (congrArg ((1 : k) • ·) e)
  rw [retA_smul_ι₂, h1, one_smul, Finset.smul_sum, retA_sum] at ha
  simp only [smul_smul, mul_one, retA_smul_ι₂] at ha
  rw [ha]
  exact Submodule.sum_mem _ fun r _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

/-- The basis `(e_t)` of `A⁽²⁾`. -/
def basisT : Module.Basis (RayA0 (S.arMeshData b) v₀) (ZMod 2) (S.A2 b) :=
  Module.Basis.mk (S.linearIndependent_eT b v₀ hF Wd) (S.span_eT b v₀ hF Wd)

theorem basisT_apply (r : RayA0 (S.arMeshData b) v₀) :
    S.basisT b v₀ hF Wd r = S.eT b v₀ hF Wd r := Module.Basis.mk_apply _ _ _

/-- **`𝔽₂P ≅ A⁽²⁾`** (`integral-deformations.tex`). -/
def Θ₂ : (SysD (S.arMeshData b) v₀ hF Wd).P.Lin (ZMod 2) ≃ₐ[ZMod 2] S.A2 b :=
  (SysD (S.arMeshData b) v₀ hF Wd).P.toMult.algOf (S.basisT b v₀ hF Wd)
    (fun r s ↦ by
      simp only [basisT_apply]
      rw [S.eT_mul b v₀ hF Wd]
      cases (SysD (S.arMeshData b) v₀ hF Wd).P.mul r s <;> simp [basisT_apply])
    (by
      simp only [basisT_apply]
      rw [show (1 : S.A2 b) = MulOpposite.op 1 from rfl,
        ← sum_idem_eq_one (F := (S.primeMeshData b).F0), Finset.op_sum]
      exact Finset.sum_congr rfl fun x _ ↦ S.eT_e b v₀ hF Wd x)

theorem Θ₂_b (r : RayA0 (S.arMeshData b) v₀) :
    S.Θ₂ b v₀ hF Wd ((SysD (S.arMeshData b) v₀ hF Wd).P.b (ZMod 2) r) = S.eT b v₀ hF Wd r := by
  rw [Θ₂, RaySys.Mult.algOf_b, basisT_apply]

/-- **The table of `A⁽²⁾`** (`MeshWalk.TabIso`). -/
def tab₂ : MeshWalk.TabIso (S.primeMeshData b) (SysD (S.arMeshData b) v₀ hF Wd).P.toMult where
  d := S.dP b v₀ hF Wd
  d_mul r s t h := by
    simp only [dP]; rw [(SysD (S.arMeshData b) v₀ hF Wd).P.wt_mul _ _ _ h, map_add]
  d_e x := by simp only [dP]; rw [(SysD (S.arMeshData b) v₀ hF Wd).P.wt_e, map_zero]
  d_nonneg r := (SysD (S.arMeshData b) v₀ hF Wd).P.deg_nonneg r
  Θ := S.Θ₂ b v₀ hF Wd
  Θ_hom r := by rw [Θ₂_b]; exact S.eT_isHom b v₀ hF Wd r
  Θ_e x := by rw [Θ₂_b]; exact S.eT_e b v₀ hF Wd x

end Table

end IndSkeleton

end MultiplicativeBasisDeformations
