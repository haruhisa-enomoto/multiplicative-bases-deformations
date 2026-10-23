module

public import MultiplicativeBasisDeformations.Foundations.StandardForm
public import MultiplicativeBasisDeformations.Foundations.GradedRealizationIso
public import MultiplicativeBasisDeformations.Foundations.PositiveDeformation

/-!
# `A` is a positive filtered deformation of `A₀`

`positive-deformations.tex`: "the filtration `F^nA(x, y) = J^n(P_y, P_x)` of
Section 3 makes `A` a positive filtered deformation of `A₀`: by Construction 2.8, its
associated graded algebra is `A₀`."

Here: the projective corner `(Alg (P_p)_p)ᵒᵖ` of `ind(mod A)` is filtered by the radical
powers of its entries; the initial forms of Proposition 2.6 (`phi`) identify the layers with
the length-graded pieces of `A₀` multiplicatively (`posFiltProj`). The Peirce isomorphism
transports this to `A` (`posFiltA`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

/-! ### Transport of a filtration along an algebra isomorphism -/

namespace PosFiltration

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  {B : Type w} [Ring B] [Algebra k B] {B' : Type w} [Ring B'] [Algebra k B']

/-- **A positive filtered deformation transported along an algebra isomorphism.** -/
def transport (P : PosFiltration G B) (ψ : B ≃ₐ[k] B') : PosFiltration G B' where
  F d := (P.F d).map ψ.toLinearEquiv.toLinearMap
  F_zero := by rw [P.F_zero, Submodule.map_top, LinearMap.range_eq_top]; exact ψ.surjective
  F_succ_le d := Submodule.map_mono (P.F_succ_le d)
  F_mul d e a b ha hb := by
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a' * b', P.F_mul d e a' b' ha' hb', by simp⟩
  M := P.M
  F_M := by rw [P.F_M, Submodule.map_bot]
  σ d := (P.σ d).comp ψ.symm.toLinearEquiv.toLinearMap
  σ_hom d a := P.σ_hom d _
  σ_ker d a ha := by
    obtain ⟨a', ha', rfl⟩ := ha
    show P.σ d (ψ.symm (ψ a')) = 0 ↔ _
    rw [ψ.symm_apply_apply, P.σ_ker d a' ha']
    constructor
    · intro h; exact ⟨a', h, rfl⟩
    · rintro ⟨a'', h, he⟩
      rw [show a' = a'' from ψ.injective he.symm]; exact h
  σ_surj d x hx := by
    obtain ⟨a, ha, hax⟩ := P.σ_surj d x hx
    refine ⟨ψ a, ⟨a, ha, rfl⟩, ?_⟩
    show P.σ d (ψ.symm (ψ a)) = x
    rw [ψ.symm_apply_apply, hax]
  σ_mul d e a b ha hb := by
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    show P.σ (d + e) (ψ.symm (ψ a' * ψ b')) = P.σ d (ψ.symm (ψ a')) * P.σ e (ψ.symm (ψ b'))
    rw [← map_mul, ψ.symm_apply_apply, ψ.symm_apply_apply, ψ.symm_apply_apply]
    exact P.σ_mul d e a' b' ha' hb'

end PosFiltration

namespace IndSkeleton

variable {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (S : IndSkeleton k A) (b : S.ArrowBases)

/-! ### Initial forms -/

/-- A linear map extending the initial form `J^d → J^d/J^{d+1}` (through a complement). -/
def initForm (d : ℕ) (X Y : S.Ind) : (X ⟶ Y) →ₗ[k] S.layer d X Y :=
  (Submodule.mkQ _).comp (Submodule.linearProjOfIsCompl (S.radPow d X Y) _
    (Submodule.exists_isCompl (S.radPow d X Y)).choose_spec)

theorem initForm_of_mem {d : ℕ} {X Y : S.Ind} {f : X ⟶ Y} (hf : f ∈ S.radPow d X Y) :
    S.initForm d X Y f = S.layerClass f hf := by
  rw [initForm, LinearMap.comp_apply]
  have h := Submodule.linearProjOfIsCompl_apply_left
    (Submodule.exists_isCompl (S.radPow d X Y)).choose_spec ⟨f, hf⟩
  erw [h]
  rfl

theorem layerClass_eq_zero {d : ℕ} {X Y : S.Ind} {f : X ⟶ Y} (hf : f ∈ S.radPow d X Y) :
    S.layerClass f hf = 0 ↔ f ∈ S.radPow (d + 1) X Y := by
  rw [layerClass, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

/-! ### The projective corner of `ind(mod A)` -/

/-- The projective corner `(Alg (P_p)_p)ᵒᵖ` of `ind(mod A)`. -/
abbrev Aproj := (CatAlg.Alg (fun p : (S.arMeshData b).PV ↦ S.label p.1))ᵐᵒᵖ

/-- `A₀`. -/
abbrev AZ := (CatAlg.Alg (S.arMeshData b).F0)ᵐᵒᵖ

/-- The filtration by radical powers of the entries. -/
def Fproj (d : ℕ) : Submodule k (S.Aproj b) where
  carrier := {a | ∀ p q, a.unop p q ∈ S.radPow d (S.label p.1) (S.label q.1)}
  add_mem' ha hb p q := by
    rw [MulOpposite.unop_add, CatAlg.add_apply]; exact add_mem (ha p q) (hb p q)
  zero_mem' p q := by rw [MulOpposite.unop_zero, CatAlg.zero_apply]; exact zero_mem _
  smul_mem' t a ha p q := by
    rw [MulOpposite.unop_smul, CatAlg.smul_apply]; exact Submodule.smul_mem _ t (ha p q)

theorem mem_Fproj {d : ℕ} {a : S.Aproj b} :
    a ∈ S.Fproj b d ↔ ∀ p q, a.unop p q ∈ S.radPow d (S.label p.1) (S.label q.1) := Iff.rfl

/-- The initial-form map of degree `d` to `A₀` (Proposition 2.6). -/
def σproj (d : ℕ) : S.Aproj b →ₗ[k] S.AZ b where
  toFun a := MulOpposite.op fun p q ↦
    ((S.phi b d p.1 q.1).symm (S.initForm d _ _ (a.unop p q)) : _)
  map_add' a a' := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    simp only [MulOpposite.unop_add, MulOpposite.unop_op, CatAlg.add_apply, map_add,
      Submodule.coe_add]
    rfl
  map_smul' t a := by
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    simp only [MulOpposite.unop_smul, MulOpposite.unop_op, CatAlg.smul_apply, map_smul,
      Submodule.coe_smul, RingHom.id_apply]
    rfl

theorem σproj_apply (d : ℕ) (a : S.Aproj b) (p q : (S.arMeshData b).PV) :
    (S.σproj b d a).unop p q = ((S.phi b d p.1 q.1).symm (S.initForm d _ _ (a.unop p q)) : _) := rfl

theorem hfinA0 : ∀ x y : S.ARVertex,
    FiniteDimensional k (ScalarMeshCategory.obj (S.arCoefficients b) x ⟶
      ScalarMeshCategory.obj (S.arCoefficients b) y) := fun x y ↦ S.finiteDimensional_meshHom b x y

theorem σproj_isHom (d : ℕ) (a : S.Aproj b) :
    (MeshWalk.lenA0 (S.arMeshData b) (S.hfinA0 b)).IsHom d (S.σproj b d a) := by
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  change ScalarMeshCategory.degProj (S.arCoefficients b) d p.1 q.1 ((S.σproj b d a).unop p q) =
    (S.σproj b d a).unop p q
  rw [σproj_apply, ScalarMeshCategory.degProj_of_mem _ (Subtype.prop _), if_pos rfl]

theorem σproj_eq_zero_iff {d : ℕ} {a : S.Aproj b} (ha : a ∈ S.Fproj b d) :
    S.σproj b d a = 0 ↔ a ∈ S.Fproj b (d + 1) := by
  constructor
  · intro h p q
    have := congrArg (fun z : S.AZ b ↦ z.unop p q) h
    simp only [σproj_apply, MulOpposite.unop_zero, CatAlg.zero_apply] at this
    rw [S.initForm_of_mem (ha p q)] at this
    rw [← S.layerClass_eq_zero (ha p q)]
    have h0 : (S.phi b d p.1 q.1).symm (S.layerClass _ (ha p q)) = 0 :=
      Subtype.ext (by simpa using this)
    rwa [LinearEquiv.map_eq_zero_iff] at h0
  · intro h
    apply MulOpposite.unop_injective
    apply CatAlg.ext; intro p q
    rw [σproj_apply, S.initForm_of_mem (ha p q), (S.layerClass_eq_zero (ha p q)).2 (h p q),
      map_zero]
    rfl

theorem σproj_surj (d : ℕ) (x : S.AZ b)
    (hx : (MeshWalk.lenA0 (S.arMeshData b) (S.hfinA0 b)).IsHom d x) :
    ∃ a ∈ S.Fproj b d, S.σproj b d a = x := by
  classical
  have hmem : ∀ p q, x.unop p q ∈ ScalarMeshCategory.degreePart (S.arCoefficients b) d p.1 q.1 := by
    intro p q
    have := congrArg (fun z : S.AZ b ↦ z.unop p q) hx
    change ScalarMeshCategory.degProj (S.arCoefficients b) d p.1 q.1 (x.unop p q) = x.unop p q at this
    rw [← this]
    exact ScalarMeshCategory.degProj_mem _ d _
  have hpre : ∀ p q, ∃ f : S.label p.1 ⟶ S.label q.1, ∃ hf : f ∈ S.radPow d _ _,
      S.layerClass f hf = S.phi b d p.1 q.1 ⟨_, hmem p q⟩ := by
    intro p q
    obtain ⟨⟨f, hf⟩, h⟩ := Submodule.Quotient.mk_surjective _ (S.phi b d p.1 q.1 ⟨_, hmem p q⟩)
    exact ⟨f, hf, h⟩
  choose f hf hfx using hpre
  refine ⟨MulOpposite.op fun p q ↦ f p q, fun p q ↦ hf p q, ?_⟩
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p q
  rw [σproj_apply]
  change (((S.phi b d p.1 q.1).symm (S.initForm d _ _ (f p q))) : _) = x.unop p q
  rw [S.initForm_of_mem (hf p q), hfx, LinearEquiv.symm_apply_apply]

theorem F_mul_proj (d e : ℕ) (a a' : S.Aproj b) (ha : a ∈ S.Fproj b d) (ha' : a' ∈ S.Fproj b e) :
    a * a' ∈ S.Fproj b (d + e) := by
  intro p r
  rw [MulOpposite.unop_mul, CatAlg.mul_apply]
  refine Submodule.sum_mem _ fun q _ ↦ ?_
  have := S.comp_mem_radPow (ha' p q) (ha q r)
  rwa [Nat.add_comm] at this

theorem σproj_mul (d e : ℕ) (a a' : S.Aproj b) (ha : a ∈ S.Fproj b d) (ha' : a' ∈ S.Fproj b e) :
    S.σproj b (d + e) (a * a') = S.σproj b d a * S.σproj b e a' := by
  rw [Nat.add_comm d e]
  apply MulOpposite.unop_injective
  apply CatAlg.ext; intro p r
  rw [σproj_apply, MulOpposite.unop_mul, MulOpposite.unop_mul, CatAlg.mul_apply, CatAlg.mul_apply,
    map_sum, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hc := S.comp_mem_radPow (ha' p q) (ha q r)
  rw [S.initForm_of_mem hc, σproj_apply, σproj_apply, S.initForm_of_mem (ha' p q),
    S.initForm_of_mem (ha q r)]
  obtain ⟨hfg, hfg', h⟩ := S.phi_comp b ((S.phi b e p.1 q.1).symm (S.layerClass _ (ha' p q)))
    ((S.phi b d q.1 r.1).symm (S.layerClass _ (ha q r))) _ (ha' p q) _ (ha q r)
    (LinearEquiv.apply_symm_apply _ _) (LinearEquiv.apply_symm_apply _ _)
  rw [← h, LinearEquiv.symm_apply_apply]

/-- **The projective corner of `ind(mod A)` is a positive filtered deformation of `A₀`.** -/
def posFiltProj : PosFiltration (MeshWalk.lenA0 (S.arMeshData b) (S.hfinA0 b)) (S.Aproj b) where
  F := S.Fproj b
  F_zero := by
    ext a; simp only [Submodule.mem_top, iff_true]
    intro p q; rw [radPow_zero]; trivial
  F_succ_le d a ha p q := S.radPow_succ_le d _ _ (ha p q)
  F_mul := S.F_mul_proj b
  M := (S.exists_radPow_eq_bot).choose
  F_M := by
    ext a
    simp only [Submodule.mem_bot]
    constructor
    · intro ha
      apply MulOpposite.unop_injective
      apply CatAlg.ext; intro p q
      have := ha p q
      rw [(S.exists_radPow_eq_bot).choose_spec, Submodule.mem_bot] at this
      exact this
    · rintro rfl p q; exact zero_mem _
  σ := S.σproj b
  σ_hom := S.σproj_isHom b
  σ_ker _ _ ha := S.σproj_eq_zero_iff b ha
  σ_surj := S.σproj_surj b
  σ_mul := S.σproj_mul b

/-! ### Transport to `A` -/

variable {n : ℕ} {e : Fin n → A} (he : CompleteOrthogonalIdempotents e)
  (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hbasic : ∀ i j, (∃ x y : A, e i * x * e j = x ∧ e j * y * e i = y ∧ x * y = e i ∧
    y * x = e j) → i = j)

/-- **`A` is the projective corner of `ind(mod A)`** (Peirce). -/
def algEquivProj : A ≃ₐ[k] S.Aproj b := by
  haveI : S.incl.Linear k := ⟨fun _ _ ↦ rfl⟩
  haveI : S.incl.Additive := ⟨rfl⟩
  let σE := S.pvEquiv b he hprim hbasic
  let α : ∀ p : (S.arMeshData b).PV, S.incl.obj (S.label p.1) ≅ idealMod ((e ∘ σE) p) :=
    fun p ↦ S.isoLabel b he hprim p
  have he' : CompleteOrthogonalIdempotents (e ∘ σE) := (CompleteOrthogonalIdempotents.equiv σE).2 he
  exact (peirceEquiv he').trans (AlgEquiv.op (CatAlg.algEquivOfFunctor S.incl α).symm)

/-- **`A` is a positive filtered deformation of `A₀`** (`positive-deformations.tex`). -/
def posFiltA : PosFiltration (MeshWalk.lenA0 (S.arMeshData b) (S.hfinA0 b)) A :=
  (S.posFiltProj b).transport (S.algEquivProj b he hprim hbasic).symm

end IndSkeleton

end MultiplicativeBasisDeformations
