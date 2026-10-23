module

public import MultiplicativeBasisDeformations.Refinements.LiftedMeshData
public import MultiplicativeBasisDeformations.Refinements.RegularLift
public import MultiplicativeBasisDeformations.Foundations.ExtProjective
public import MultiplicativeBasisDeformations.Foundations.FiltrationDim
public import MultiplicativeBasisDeformations.Foundations.CategoryAlgebraCorners

/-!
# The projective corner of the lifted modules is `B` (toward Corollary 12.1)

`deformation-refinements.tex`: "At projective labels choose the regular `B`-projectives."
The vertex idempotents `e_p` of `A₀` give vertices of the length grading (`vxIdem`), and a
splitting of `B` respecting them (Lemma 6.4). The lift `M_p^B` at a projective label is the
regular module `φ(e_p) B` (Proposition 6.5(3)), by uniqueness of lifts; the corner algebra of
the lifted modules at the projective labels is therefore `B` (`cornerEquiv`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData GExt PosFiltration

attribute [local instance] Classical.decEq

universe u

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y))
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-! ### The vertex idempotents of `A₀` -/

theorem idem_apply' (x y z : D.PV) : idem (F := D.F0) x y z = idTo y x ≫ idTo x z := rfl

theorem idem_mul_idem_ne {p q : D.PV} (h : p ≠ q) : idem (F := D.F0) p * idem q = 0 := by
  refine CatAlg.ext fun y z ↦ ?_
  simp only [mul_apply, idem_apply', CatAlg.zero_apply, Category.assoc]
  rw [← Preadditive.comp_sum]
  simp_rw [← Category.assoc (idTo p _)]
  rw [← Preadditive.sum_comp, sum_idTo_comp (F := D.F0) p (fun w ↦ idTo w q), idTo_ne h,
    Limits.zero_comp, Limits.comp_zero]

theorem sum_idem' : ∑ x, idem (F := D.F0) x = 1 := by
  refine CatAlg.ext fun y z ↦ ?_
  rw [CatAlg.sum_apply, CatAlg.one_apply (F := D.F0)]
  simp only [idem_apply']
  exact sum_idTo_comp (F := D.F0) y (fun x ↦ idTo x z)

theorem idem_mem (p y z : D.PV) : idem (F := D.F0) p y z ∈ degreePart c 0 y.1 z.1 := by
  rw [idem_apply']
  have := comp_mem_degreePart' c (idTo_mem_degreePart D y p) (idTo_mem_degreePart D p z)
  rwa [add_zero] at this

/-- **The vertex idempotents of `A₀`** as vertices of its length grading. -/
def vxIdem : LenGrading.Vertices (lenA0 D hfin) where
  n := Fintype.card D.PV
  e i := MulOpposite.op (idem (F := D.F0) ((Fintype.equivFin D.PV).symm i))
  complete := by
    refine (CompleteOrthogonalIdempotents.iff_ortho_complete).2 ⟨fun i j hij ↦ ?_, ?_⟩
    · apply MulOpposite.unop_injective
      rw [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op, MulOpposite.unop_zero]
      exact idem_mul_idem_ne D (fun h ↦ hij ((Fintype.equivFin D.PV).symm.injective h).symm)
    · apply MulOpposite.unop_injective
      rw [Finset.unop_sum, MulOpposite.unop_one]
      simp only [MulOpposite.unop_op]
      rw [Equiv.sum_comp (Fintype.equivFin D.PV).symm (fun p ↦ idem (F := D.F0) p)]
      exact sum_idem' D
  deg0 i := by
    have h := (galgA0_isHom D hfin 0 (MulOpposite.op (idem (F := D.F0)
      ((Fintype.equivFin D.PV).symm i)))).2 fun y z ↦ idem_mem D _ y z
    exact (ZGr.ofLen_isHom _ 0 _).1 h
  span0 a ha := by
    classical
    have ha' := (galgA0_isHom D hfin 0 a).1 ((ZGr.ofLen_isHom _ 0 _).2 ha)
    choose t ht using fun p : D.PV ↦ ScalarMeshCategory.degreePart_zero_eq c (ha' p p)
    refine ⟨fun i ↦ t ((Fintype.equivFin D.PV).symm i), ?_⟩
    apply MulOpposite.unop_injective
    refine CatAlg.ext fun y z ↦ ?_
    rw [Finset.unop_sum, CatAlg.sum_apply]
    simp only [MulOpposite.unop_smul, MulOpposite.unop_op, CatAlg.smul_apply, idem_apply']
    rw [Equiv.sum_comp (Fintype.equivFin D.PV).symm
      (fun p ↦ t p • (idTo (F := D.F0) y p ≫ idTo p z))]
    rw [Finset.sum_eq_single y]
    · by_cases hyz : y = z
      · subst hyz; rw [ht y]; simp
      · rw [degreePart_zero_ne (fun h ↦ hyz (Subtype.ext h)) (ha' y z), idTo_ne hyz,
          Limits.comp_zero, smul_zero]
    · intro p _ hp; rw [idTo_ne (Ne.symm hp), Limits.zero_comp, smul_zero]
    · simp

theorem vxIdem_e (p : D.PV) :
    (vxIdem D hfin).e (Fintype.equivFin D.PV p) = MulOpposite.op (idem (F := D.F0) p) := by
  simp [vxIdem]

/-! ### The lifts at projective labels are regular -/

variable {D hfin} {B : Type u} [Ring B] [Algebra k B] {P : PosFiltration (lenA0 D hfin) B}
  (Ls : Lifts D hfin P) (S : Split P)
  (hleft : ∀ i a, S.φ ((vxIdem D hfin).e i * a) = S.φ ((vxIdem D hfin).e i) * S.φ a)

theorem idem_isHom0 (p : D.PV) : (lenA0 D hfin).IsHom 0 (MulOpposite.op (idem (F := D.F0) p)) := by
  rw [← vxIdem_e D hfin p]; exact (vxIdem D hfin).deg0 _

theorem idem_idem (p : D.PV) : IsIdempotentElem (MulOpposite.op (idem (F := D.F0) p)) := by
  change MulOpposite.op _ * MulOpposite.op _ = MulOpposite.op _
  rw [← MulOpposite.op_mul, idem_mul_idem]

theorem colAlg_mul_idem (p : D.PV) (m : Rep D.F0 (meshFam Q c p.1)) :
    colAlg (F := D.F0) p m * idem p = colAlg p m := by
  rw [idem, ← colAlg_smul, colAlg_smul_unit]

/-- The cyclic projective `ψ : M_p → e_p A₀`, `m ↦ (m, as a column)`. -/
def ψR (p : D.PV) : Rep D.F0 (meshFam Q c p.1) →ₗ[k] RI k (MulOpposite.op (idem (F := D.F0) p)) where
  toFun m := ⟨MulOpposite.op (colAlg (F := D.F0) p m), by
    rw [mem_RI (idem_idem p)]
    change MulOpposite.op (colAlg p m * idem p) = _
    rw [colAlg_mul_idem]⟩
  map_add' m m' := Subtype.ext (by
    change MulOpposite.op (colAlg p (m + m')) = MulOpposite.op (colAlg p m) + MulOpposite.op (colAlg p m')
    rw [colAlg_add, MulOpposite.op_add])
  map_smul' t m := Subtype.ext (by
    change MulOpposite.op (colAlg p (t • m)) = t • MulOpposite.op (colAlg p m)
    rw [colAlg_smul', MulOpposite.op_smul])

theorem ψR_apply (p : D.PV) (m) :
    (ψR (D := D) p m).1 = MulOpposite.op (colAlg (F := D.F0) p m) := rfl

theorem ψR_act (p : D.PV) (m) (a : (Alg D.F0)ᵐᵒᵖ) :
    (ψR (D := D) p (a.unop • m)).1 = (ψR p m).1 * a := by
  rw [ψR_apply, ψR_apply, colAlg_smul, MulOpposite.op_mul]
  rfl

theorem ψR_injective (p : D.PV) : Function.Injective (ψR (D := D) p) := by
  intro m m' h
  have := congrArg (fun r : RI k _ ↦ r.1.unop • unit (F := D.F0) p) h
  simp only [ψR_apply, MulOpposite.unop_op, colAlg_smul_unit] at this
  exact this

theorem ψR_surjective (p : D.PV) : Function.Surjective (ψR (D := D) p) := by
  intro r
  refine ⟨r.1.unop • unit (F := D.F0) p, Subtype.ext ?_⟩
  rw [ψR_act]
  change MulOpposite.op (colAlg p (unit p)) * r.1 = r.1
  exact (mem_RI (idem_idem p)).1 r.2

theorem ψR_isHom (p : D.PV) (q : ℤ) (m) (hm : (gmodEv D hfin p.1).gr.IsHom q m) :
    (rightIdeal (one_isHom D hfin) (idem_isHom0 p) (idem_idem p)).gr.IsHom (q + 0)
      (ψR p m) := by
  apply Subtype.ext
  have h := (cycProj D hfin p).ψ_deg q m hm
  change (galgA0 D hfin).gr.IsHom (q - 0) _ at h
  rw [sub_zero] at h
  rw [add_zero]
  exact h

include hleft in
theorem hleft_p (p : D.PV) (a) :
    S.φ (MulOpposite.op (idem (F := D.F0) p) * a) =
      S.φ (MulOpposite.op (idem (F := D.F0) p)) * S.φ a := by
  rw [← vxIdem_e D hfin p]; exact hleft _ a

/-- The regular lift transported to `M_p`. -/
def regT (p : D.PV) : FLift P (one_isHom D hfin) (gmodEv D hfin p.1) :=
  FLift.transport (Split.regularLift (one_isHom D hfin) (idem_isHom0 p) (idem_idem p) S
      (hleft_p S hleft p))
    (ψR p) (ψR_injective p) (fun m x ↦ ψR_surjective p _)
    (r := 0) (fun q m hm d hd ↦ by
      rw [(ZGr.proj_of_isHom _ (ψR_isHom p q m hm)), if_neg (by omega)])
    (fun m a ↦ by
      rw [ZGr.comp_eq_self_of_hom _ _ (ψR_isHom p)]
      exact Subtype.ext (ψR_act p m a))
    (by rw [ZGr.comp_eq_self_of_hom _ _ (ψR_isHom p)]; exact ψR_injective p)

include hleft in
theorem ψR_regT (p : D.PV) (m) (x : B) :
    S.φ (ψR p ((regT S hleft p).act m x)).1 = S.φ (ψR (D := D) p m).1 * x := by
  have := FLift.transport_act (Split.regularLift (one_isHom D hfin) (idem_isHom0 p) (idem_idem p) S
      (hleft_p S hleft p)) (ψR p) (ψR_injective p) (fun m x ↦ ψR_surjective p _)
    (r := 0) (fun q m hm d hd ↦ by
      rw [(ZGr.proj_of_isHom _ (ψR_isHom p q m hm)), if_neg (by omega)])
    (fun m a ↦ by
      rw [ZGr.comp_eq_self_of_hom _ _ (ψR_isHom p)]
      exact Subtype.ext (ψR_act p m a))
    (by rw [ZGr.comp_eq_self_of_hom _ _ (ψR_isHom p)]; exact ψR_injective p) m x
  change ψR p ((regT S hleft p).act m x) = _ at this
  rw [this]
  simp [Split.regularLift]

variable (Vx : LenGrading.Vertices (lenA0 D hfin))

include Vx in
theorem exists_regIso (p : D.PV) :
    ∃ Φ : Rep D.F0 (meshFam Q c p.1) ≃ₗ[k] Rep D.F0 (meshFam Q c p.1),
      ∀ m x, Φ ((Ls.L p.1).act m x) = (regT S hleft p).act (Φ m) x := by
  obtain ⟨Φ, hΦ, -⟩ := fLift_unique Vx (fun t _ ↦ extVanish_proj D hfin p _ 0 t)
    (Ls.L p.1) (regT S hleft p)
  exact ⟨Φ, hΦ⟩

/-- **`M_p^B ≅ φ(e_p)B`**: the embedding `θ_p : M_p^B → B`. -/
def θ (p : D.PV) : Rep D.F0 (meshFam Q c p.1) →ₗ[k] B :=
  S.φ.toLinearMap ∘ₗ (RI k _).subtype ∘ₗ ψR p ∘ₗ (exists_regIso Ls S hleft Vx p).choose.toLinearMap

theorem θ_act (p : D.PV) (m) (x : B) :
    θ Ls S hleft Vx p ((Ls.L p.1).act m x) = θ Ls S hleft Vx p m * x := by
  simp only [θ, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
    (exists_regIso Ls S hleft Vx p).choose_spec]
  exact ψR_regT S hleft p _ x

theorem θ_injective (p : D.PV) : Function.Injective (θ Ls S hleft Vx p) :=
  S.φ.injective.comp (Subtype.val_injective.comp ((ψR_injective p).comp
    (exists_regIso Ls S hleft Vx p).choose.injective))

/-- The lifted vertex idempotent `E_p = φ(e_p)`. -/
abbrev Ep (p : D.PV) : B := S.φ (MulOpposite.op (idem (F := D.F0) p))

theorem mem_range_θ (p : D.PV) (b : B) :
    b ∈ LinearMap.range (θ Ls S hleft Vx p) ↔ Ep S p * b = b := by
  constructor
  · rintro ⟨m, rfl⟩
    simp only [θ, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    set r := ψR p ((exists_regIso Ls S hleft Vx p).choose m)
    have hr := (mem_RI (idem_idem p)).1 r.2
    rw [← hleft_p S hleft p, hr]
  · intro hb
    set a := S.φ.symm b
    have ha : MulOpposite.op (idem (F := D.F0) p) * a ∈ RI k (MulOpposite.op (idem (F := D.F0) p)) :=
      ⟨a, rfl⟩
    obtain ⟨m, hm⟩ := ψR_surjective (D := D) p ⟨_, ha⟩
    refine ⟨(exists_regIso Ls S hleft Vx p).choose.symm m, ?_⟩
    simp only [θ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      Submodule.subtype_apply, hm]
    rw [hleft_p S hleft p, LinearEquiv.apply_symm_apply, hb]

/-! ### The corner algebra -/

include hleft in
theorem Ep_mul_Ep (p q : D.PV) : Ep S p * Ep S q = if p = q then Ep S p else 0 := by
  rw [Ep, Ep, ← hleft_p S hleft p]
  split_ifs with h
  · subst h; rw [(idem_idem p).eq]
  · rw [← MulOpposite.op_mul, idem_mul_idem_ne D (Ne.symm h), MulOpposite.op_zero, map_zero]

theorem sum_Ep : ∑ p, Ep S p = (1 : B) := by
  rw [← S.one, ← map_sum]
  congr 1
  apply MulOpposite.unop_injective
  rw [Finset.unop_sum, MulOpposite.unop_one]
  simp only [MulOpposite.unop_op]
  exact sum_idem' D

include hleft in
theorem Ep_idem (p : D.PV) : Ep S p * Ep S p = Ep S p := by
  rw [Ep_mul_Ep S hleft, if_pos rfl]

/-- The components `m ↦ θ_q⁻¹(E_q b θ_p m)` of left multiplication by `b`. -/
def ξ (b : B) (p q : D.PV) : Rep D.F0 (meshFam Q c p.1) →ₗ[k] Rep D.F0 (meshFam Q c q.1) :=
  (LinearEquiv.ofInjective _ (θ_injective Ls S hleft Vx q)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (θ Ls S hleft Vx q))
      (LinearMap.mulLeft k (Ep S q * b) ∘ₗ θ Ls S hleft Vx p) fun m ↦ by
        rw [mem_range_θ]
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        rw [← mul_assoc, ← mul_assoc, Ep_idem S hleft]

theorem θ_ξ (b : B) (p q : D.PV) (m) :
    θ Ls S hleft Vx q (ξ Ls S hleft Vx b p q m) = Ep S q * b * θ Ls S hleft Vx p m := by
  have := (LinearEquiv.ofInjective _ (θ_injective Ls S hleft Vx q)).apply_symm_apply
    ⟨Ep S q * b * θ Ls S hleft Vx p m, by
      rw [mem_range_θ, ← mul_assoc, ← mul_assoc, Ep_idem S hleft]⟩
  exact congrArg Subtype.val this

theorem ξ_act (b : B) (p q : D.PV) (m) (x : B) :
    ξ Ls S hleft Vx b p q ((Ls.L p.1).act m x) = (Ls.L q.1).act (ξ Ls S hleft Vx b p q m) x := by
  apply θ_injective Ls S hleft Vx q
  rw [θ_ξ, θ_act, θ_act, θ_ξ]
  simp only [mul_assoc]

/-- **Left multiplication**, as an element of the corner algebra. -/
def Ξ (b : B) : (Alg (fun p : D.PV ↦ FB Ls p.1))ᵐᵒᵖ :=
  MulOpposite.op fun p q ↦ ofLin Ls (ξ Ls S hleft Vx b p q) (ξ_act Ls S hleft Vx b p q)

theorem toLin_Ξ (b : B) (p q : D.PV) :
    toLin ((Ξ Ls S hleft Vx b).unop p q) = ξ Ls S hleft Vx b p q := rfl

theorem θ_toLin_idTo (p q : D.PV) (m) :
    θ Ls S hleft Vx q (toLin (idTo (F := fun p : D.PV ↦ FB Ls p.1) p q) m) =
      Ep S q * θ Ls S hleft Vx p m := by
  have hθ := (mem_range_θ Ls S hleft Vx p (θ Ls S hleft Vx p m)).1 ⟨m, rfl⟩
  by_cases h : p = q
  · subst h; rw [idTo_self, toLin_id, LinearMap.id_apply, hθ]
  · rw [idTo_ne h, toLin_zero, LinearMap.zero_apply, map_zero, ← hθ, ← mul_assoc,
      Ep_mul_Ep S hleft, if_neg (Ne.symm h), zero_mul]

theorem Ξ_one : Ξ Ls S hleft Vx 1 = 1 := by
  apply MulOpposite.unop_injective
  refine CatAlg.ext fun p q ↦ toLin_injective (LinearMap.ext fun m ↦ ?_)
  apply θ_injective Ls S hleft Vx q
  rw [toLin_Ξ, θ_ξ, mul_one, MulOpposite.unop_one, CatAlg.one_apply, θ_toLin_idTo]

theorem Ξ_mul (b b' : B) : Ξ Ls S hleft Vx (b * b') = Ξ Ls S hleft Vx b * Ξ Ls S hleft Vx b' := by
  apply MulOpposite.unop_injective
  refine CatAlg.ext fun p r ↦ toLin_injective (LinearMap.ext fun m ↦ ?_)
  apply θ_injective Ls S hleft Vx r
  rw [toLin_Ξ, θ_ξ, MulOpposite.unop_mul, CatAlg.mul_apply, toLin_sum, LinearMap.sum_apply,
    map_sum]
  simp only [toLin_comp, LinearMap.comp_apply, toLin_Ξ, θ_ξ]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  simp only [mul_assoc (Ep S r * b), ← Finset.mul_sum]
  rw [sum_Ep S, one_mul]

theorem Ξ_add (b b' : B) : Ξ Ls S hleft Vx (b + b') = Ξ Ls S hleft Vx b + Ξ Ls S hleft Vx b' := by
  apply MulOpposite.unop_injective
  refine CatAlg.ext fun p q ↦ toLin_injective (LinearMap.ext fun m ↦ ?_)
  apply θ_injective Ls S hleft Vx q
  rw [toLin_Ξ, θ_ξ, MulOpposite.unop_add, CatAlg.add_apply, toLin_add, LinearMap.add_apply,
    map_add, toLin_Ξ, toLin_Ξ, θ_ξ, θ_ξ, mul_add, add_mul]

theorem Ξ_smul (t : k) (b : B) : Ξ Ls S hleft Vx (t • b) = t • Ξ Ls S hleft Vx b := by
  apply MulOpposite.unop_injective
  refine CatAlg.ext fun p q ↦ toLin_injective (LinearMap.ext fun m ↦ ?_)
  apply θ_injective Ls S hleft Vx q
  rw [toLin_Ξ, θ_ξ, MulOpposite.unop_smul, CatAlg.smul_apply, toLin_smul, LinearMap.smul_apply,
    map_smul, toLin_Ξ, θ_ξ, mul_smul_comm, smul_mul_assoc]

/-- **Left multiplication as an algebra map** `B → (End ⊕_p M_p^B)ᵒᵖ`. -/
def ΞAlg : B →ₐ[k] (Alg (fun p : D.PV ↦ FB Ls p.1))ᵐᵒᵖ where
  toFun := Ξ Ls S hleft Vx
  map_one' := Ξ_one Ls S hleft Vx
  map_mul' := Ξ_mul Ls S hleft Vx
  map_zero' := by
    have := Ξ_smul Ls S hleft Vx 0 0
    rwa [zero_smul, zero_smul] at this
  map_add' := Ξ_add Ls S hleft Vx
  commutes' t := by
    rw [Algebra.algebraMap_eq_smul_one, Ξ_smul, Ξ_one, Algebra.algebraMap_eq_smul_one]

theorem ΞAlg_injective : Function.Injective (ΞAlg Ls S hleft Vx) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have h : ∀ p q, Ep S q * b * Ep S p = 0 := by
    intro p q
    obtain ⟨m, hm⟩ := (mem_range_θ Ls S hleft Vx p (Ep S p)).2 (Ep_idem S hleft p)
    have := congrArg (fun a : (Alg (fun p : D.PV ↦ FB Ls p.1))ᵐᵒᵖ ↦ θ Ls S hleft Vx q
      (toLin (a.unop p q) m)) hb
    rw [show (ΞAlg Ls S hleft Vx b).unop p q = (Ξ Ls S hleft Vx b).unop p q from rfl, toLin_Ξ,
      θ_ξ, hm, MulOpposite.unop_zero, CatAlg.zero_apply, toLin_zero, LinearMap.zero_apply,
      map_zero] at this
    exact this
  calc b = (∑ q, Ep S q) * b * ∑ p, Ep S p := by rw [sum_Ep, one_mul, mul_one]
    _ = ∑ q, ∑ p, Ep S q * b * Ep S p := by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ ↦ by rw [Finset.mul_sum]
    _ = 0 := Finset.sum_eq_zero fun q _ ↦ Finset.sum_eq_zero fun p _ ↦ h p q

/-! ### Bijectivity by dimensions -/

theorem finrank_Alg {ι : Type} [Fintype ι] [DecidableEq ι] {𝒞 : Type*} [Category 𝒞]
    [Preadditive 𝒞] [Linear k 𝒞] {F : ι → 𝒞} [∀ x y, FiniteDimensional k (F x ⟶ F y)] :
    Module.finrank k (Alg F) = ∑ x, ∑ y, Module.finrank k (F x ⟶ F y) := by
  change Module.finrank k (∀ x y : ι, F x ⟶ F y) = _
  rw [Module.finrank_pi_fintype]
  simp_rw [Module.finrank_pi_fintype]

instance finiteDimensional_Alg {ι : Type} [Fintype ι] [DecidableEq ι] {𝒞 : Type*} [Category 𝒞]
    [Preadditive 𝒞] [Linear k 𝒞] {F : ι → 𝒞} [∀ x y, FiniteDimensional k (F x ⟶ F y)] :
    FiniteDimensional k (Alg F) :=
  inferInstanceAs (FiniteDimensional k (∀ x y : ι, F x ⟶ F y))

variable (J : D.InjData) (h1 : DegOne D)

include S Vx J h1 in
theorem finrank_corner :
    Module.finrank k (Alg (fun p : D.PV ↦ FB Ls p.1))ᵐᵒᵖ = Module.finrank k B := by
  rw [← S.φ.finrank_eq, ← (MulOpposite.opLinearEquiv k).finrank_eq,
    ← (MulOpposite.opLinearEquiv k).finrank_eq, finrank_Alg, finrank_Alg]
  exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦
    finrank_FB Ls J h1 Vx p.1 q.1

include J h1 in
theorem ΞAlg_bijective : Function.Bijective (ΞAlg Ls S hleft Vx) := by
  have hinj := ΞAlg_injective Ls S hleft Vx
  have : FiniteDimensional k B := S.φ.finiteDimensional
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (ΞAlg Ls S hleft Vx).toLinearMap) (finrank_corner Ls S Vx J h1).symm).1 hinj

/-- **The corner algebra of the lifted modules at the projective labels is `B`.** -/
def cornerEquiv : B ≃ₐ[k] (Alg (fun p : D.PV ↦ FB Ls p.1))ᵐᵒᵖ :=
  AlgEquiv.ofBijective (ΞAlg Ls S hleft Vx) (ΞAlg_bijective Ls S hleft Vx J h1)

end MeshWalk

end MultiplicativeBasisDeformations
