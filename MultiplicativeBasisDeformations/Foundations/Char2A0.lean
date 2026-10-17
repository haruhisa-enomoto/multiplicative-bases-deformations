import MultiplicativeBasisDeformations.Foundations.A0Table
import MultiplicativeBasisDeformations.Foundations.TransportFamily
import MultiplicativeBasisDeformations.Foundations.WeightHH
import MultiplicativeBasisDeformations.Foundations.CharBasis

/-!
# The characteristic-two step for `A₀`

The proof of Proposition 8.3(1) (`main-theorems.tex:7–35`) on `A₀`: with the rows `S` of
Proposition 6.1 and their dual mesh weights, choose for each row with a nonzero class the
indicator of Proposition 11.2 supplied by Corollary 10.5, form the binary family and apply
Proposition 7.9 (`char2_core`).

Deviation (weights): the integer weights used for the characters are those of the mesh
weight `w = (w_R)_{R ∈ S} × length` built from the dual mesh weights of Proposition 6.1
(`dualWt`), with values in `ℤ^S × ℤ`. The residual characters are then
`(e_R, deg)`, part of an evident integer basis (`latBasis`); this replaces Proposition 7.5
and Lemma 7.4 here (which need a connected Auslander–Reiten quiver). Corollary 10.5 is an
explicit hypothesis of `char2_A0`; it is discharged by `cor105Hyp` in `FinalBasis.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

/-! ### The lattice of the dual weights -/

section Lattice

variable {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V} {ι : Type} [Fintype ι] [DecidableEq ι]
  (Wd : ι → MeshWt Q ℤ)

/-- The lattice `ℤ^ι × ℤ` of the dual weights (a type synonym without a decidable equality
instance, so that the classical one is used throughout, as in the weight grading of `A₀`). -/
def DLat (ι : Type) : Type := (ι → ℤ) × ℤ

instance : AddCommGroup (DLat ι) := inferInstanceAs (AddCommGroup ((ι → ℤ) × ℤ))

instance : Module ℤ (DLat ι) := inferInstanceAs (Module ℤ ((ι → ℤ) × ℤ))

/-- The length coordinate. -/
def lenCoord : DLat ι →+ ℤ := AddMonoidHom.snd (ι → ℤ) ℤ

/-- The mesh weight `(w_R)_R × length`, with values in `ℤ^ι × ℤ`. -/
def dualWt0 : MeshWt Q ((ι → ℤ) × ℤ) where
  w a := (fun i ↦ (Wd i).w a, 1)
  ν x := (fun i ↦ (Wd i).ν x, 2)
  mesh x a := by
    refine Prod.ext (funext fun i ↦ ?_) ?_
    · exact (Wd i).mesh x a
    · change (1 : ℤ) + 1 = 2; norm_num

/-- The mesh weight `(w_R)_R × length`. -/
def dualWt : MeshWt Q (DLat ι) := dualWt0 Wd

theorem dualWt0_pw {y x : V} (p : Quiver.Path y x) :
    (dualWt0 Wd).pw p = (fun i ↦ (Wd i).pw p, (p.length : ℤ)) := by
  induction p with
  | nil => simp [MeshWt.pw]; rfl
  | cons p a ih =>
    rw [MeshWt.pw, ih, Quiver.Path.length_cons]
    refine Prod.ext (funext fun i ↦ ?_) ?_
    · simp [MeshWt.pw, dualWt0]
    · simp [dualWt0]

theorem dualWt_pw {y x : V} (p : Quiver.Path y x) :
    (dualWt Wd).pw p = ((fun i ↦ (Wd i).pw p, (p.length : ℤ)) : (ι → ℤ) × ℤ) :=
  dualWt0_pw Wd p

theorem rowWt_dualWt (R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) :
    rowWt (dualWt Wd) R = ((fun i ↦ rowWt (Wd i) R, (R.2.length : ℤ) - 2) : (ι → ℤ) × ℤ) := by
  unfold rowWt
  rw [dualWt_pw]
  rfl

/-- The shear `(v, m) ↦ (v, m + Σ v_i ℓ_i)`. -/
def shear0 (ℓ : ι → ℤ) : ((ι → ℤ) × ℤ) ≃ₗ[ℤ] ((ι → ℤ) × ℤ) where
  toFun p := (p.1, p.2 + ∑ i, p.1 i * ℓ i)
  invFun p := (p.1, p.2 - ∑ i, p.1 i * ℓ i)
  map_add' p p' := by
    refine Prod.ext rfl ?_
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
  map_smul' t p := by
    refine Prod.ext rfl ?_
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_assoc, ← Finset.mul_sum]; ring
  left_inv p := by simp
  right_inv p := by simp

/-- The shear, with values in `DLat ι`. -/
def shear (ℓ : ι → ℤ) : ((ι → ℤ) × ℤ) ≃ₗ[ℤ] DLat ι :=
  (shear0 ℓ).trans (LinearEquiv.refl ℤ ((ι → ℤ) × ℤ))

/-- **An integer basis containing the residual characters.** -/
def latBasis (ℓ : ι → ℤ) : Module.Basis (ι ⊕ Unit) ℤ (DLat ι) :=
  ((Pi.basisFun ℤ ι).prod (Module.Basis.singleton Unit ℤ)).map (shear ℓ)

theorem latBasis_inl (ℓ : ι → ℤ) (i : ι) :
    latBasis ℓ (Sum.inl i) = ((Pi.single i 1, ℓ i) : (ι → ℤ) × ℤ) := by
  have h1 := Module.Basis.prod_apply_inl_fst (Pi.basisFun ℤ ι) (Module.Basis.singleton Unit ℤ) i
  have h2 := Module.Basis.prod_apply_inl_snd (Pi.basisFun ℤ ι) (Module.Basis.singleton Unit ℤ) i
  rw [latBasis, Module.Basis.map_apply]
  set p := (Pi.basisFun ℤ ι).prod (Module.Basis.singleton Unit ℤ) (Sum.inl i)
  refine Prod.ext ?_ ?_
  · change p.1 = _; rw [h1, Pi.basisFun_apply]
  · change p.2 + ∑ j, p.1 j * ℓ j = ℓ i
    rw [h1, h2, Pi.basisFun_apply, zero_add,
      Finset.sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul]) (by simp)]
    simp

/-- **Basis vectors are primitive.** -/
theorem prim_of_basis {L : Type} [AddCommGroup L] [DecidableEq L] {κ : Type*}
    (B : Module.Basis κ ℤ L) (j : κ) : RaySys.Sys.Prim (B j) := by
  intro n η h
  have := congrArg (fun z ↦ B.repr z j) h
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul, Finsupp.smul_apply,
    nsmul_eq_mul] at this
  have h1 : (n : ℤ) * B.repr η j = 1 := this.symm
  have := Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg n) h1
  omega

end Lattice

/-! ### Homogeneity of the ray basis of `A₀` -/

section A0

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)

variable [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWt Q ℤ)

theorem dualWt_map_snd : (dualWt Wd).map lenCoord = lenW := rfl

theorem hdg_dual :
    lenCoord.comp ((dualWt Wd).res (v₀ := v₀) c D) =
      (lenW (Q := Q)).res (v₀ := v₀) c D := by
  rw [← MeshWt.res_map, dualWt_map_snd]

/-- The ray system of `A₀` with the dual weights. -/
abbrev SysD : RaySys.Sys D.PV (RayA0 D v₀) (DLat ι) :=
  A0SysL D v₀ hF (dualWt Wd) lenCoord (hdg_dual D v₀ Wd)

/-- `kP ≅ A₀`. -/
abbrev ΘD : (SysD D v₀ hF Wd).P.Lin k ≃ₐ[k] (Alg D.F0)ᵐᵒᵖ :=
  thetaA0L D v₀ hF (dualWt Wd) lenCoord (hdg_dual D v₀ Wd)

theorem ΘD_b (t : RayA0 D v₀) : ΘD D v₀ hF Wd ((SysD D v₀ hF Wd).P.b k t) = basisR D v₀ hF t :=
  thetaA0L_b D v₀ hF _ _ _ t

theorem SysD_deg_wt (t : RayA0 D v₀) {p : Quiver.Path t.1.1.1 t.1.2.1.1}
    (hp : (degW Q v₀).deg p = t.1.2.2) :
    (SysD D v₀ hF Wd).P.deg ((SysD D v₀ hF Wd).P.wt t) = p.length := by
  change lenCoord (wtLat D v₀ (dualWt Wd) t) = _
  rw [dg_wtLat D v₀ (dualWt Wd) _ (hdg_dual D v₀ Wd), degR_wtR_path D v₀ hp]

/-- **The ray basis is length-homogeneous.** -/
theorem ΘD_lenHom (t : RayA0 D v₀) :
    (lenA0 D (hfinObj (c := c))).IsHom ((SysD D v₀ hF Wd).P.deg ((SysD D v₀ hF Wd).P.wt t)).toNat
      (ΘD D v₀ hF Wd ((SysD D v₀ hF Wd).P.b k t)) := by
  obtain ⟨⟨x, y, g⟩, ht⟩ := t
  obtain ⟨p, hp⟩ := exists_path_of_nz ht
  rw [SysD_deg_wt D v₀ hF Wd ⟨(x, y, g), ht⟩ hp, Int.toNat_natCast, ΘD_b]
  exact basisR_isHom D v₀ hF ht hp

/-- **The ray basis is weight-homogeneous.** -/
theorem ΘD_latHom (t : RayA0 D v₀) :
    (latA0 (dualWt Wd) (hfinObj (c := c)) D).IsHom ((SysD D v₀ hF Wd).P.wt t)
      (ΘD D v₀ hF Wd ((SysD D v₀ hF Wd).P.b k t)) := by
  obtain ⟨⟨x, y, g⟩, ht⟩ := t
  obtain ⟨p, hp⟩ := exists_path_of_nz ht
  rw [ΘD_b, latA0_isHom, grA0_isHom]
  intro p' q'
  rw [basisR_apply]
  change unitM x y (deckV D v₀ hF x y g) p' q' ∈ _
  rw [unitM_apply]
  by_cases hx : p' = x
  · subst hx
    by_cases hy : q' = y
    · subst hy
      rw [idTo_self, idTo_self, Category.id_comp, Category.comp_id]
      have hf := deckV_mem D v₀ hF p' q' g
      change deckV D v₀ hF p' q' g ∈ (deckGrading Q c v₀).part g p'.1 q'.1 at hf
      rw [HomGrading.mem_part_iff, isHom_iff] at hf
      have hw : (SysD D v₀ hF Wd).P.wt ⟨(p', q', g), ht⟩ = (dualWt Wd).pw p := by
        change (dualWt Wd).res c D (cls Q c v₀ D (p', q', g)) = _
        rw [MeshWt.res_cls, MeshWt.rv_path _ ht hp]
      rw [hw]
      refine Submodule.span_le.2 ?_ (wPart_le_span Q c v₀ g p'.1 q'.1 hf)
      rintro _ ⟨p'', hp'', rfl⟩
      have e : (dualWt Wd).pw p'' = (dualWt Wd).pw p := by
        have h1 := MeshWt.rv_path (c := c) (D := D) (dualWt Wd) ht hp
        have h2 := MeshWt.rv_path (c := c) (D := D) (dualWt Wd) ht hp''
        exact h2.symm.trans h1
      rw [← e]
      exact pathMor_mem_wP (dualWt Wd) p''
    · rw [idTo_ne (Ne.symm hy), Limits.comp_zero, Limits.comp_zero]; exact Submodule.zero_mem _
  · rw [idTo_ne hx, Limits.zero_comp]; exact Submodule.zero_mem _

theorem FpA0_e_ΘD (i : Fin (FpA0 D v₀ hF).m) :
    (FpA0 D v₀ hF).e i = ΘD D v₀ hF Wd ((SysD D v₀ hF Wd).P.b k
      ((SysD D v₀ hF Wd).P.e ((Fintype.equivFin D.PV).symm i))) := by
  rw [ΘD_b]; rfl

/-- **The vertex idempotents of `A₀`** as degree-zero vertices. -/
def VxA0 : LenGrading.Vertices (lenA0 D (hfinObj (c := c))) where
  n := (FpA0 D v₀ hF).m
  e := (FpA0 D v₀ hF).e
  complete := (FpA0 D v₀ hF).complete
  deg0 := FpA0_he0 D v₀ hF
  span0 a ha := by
    classical
    set S := SysD D v₀ hF Wd
    set Θ := ΘD D v₀ hF Wd
    have hG := ΘD_lenHom D v₀ hF Wd
    refine ⟨fun i ↦ (S.basisΛ k Θ).repr a (S.P.e ((Fintype.equivFin D.PV).symm i)), ?_⟩
    have h0 : ∀ r, (S.basisΛ k Θ).repr a r ≠ 0 → r = S.P.e (S.P.src r) := by
      intro r hr
      by_contra hne
      apply hr
      refine (lenA0 D hfinObj).repr_eq_zero_of_isHom (S.basisΛ k Θ)
        (fun r ↦ (S.P.deg (S.P.wt r)).toNat) (fun r ↦ by rw [S.basisΛ_apply]; exact hG r) ha ?_
      have := S.P.deg_pos r hne
      omega
    conv_lhs => rw [← (S.basisΛ k Θ).sum_repr a]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image fun x ↦ S.P.e x)) (fun r _ hr ↦ by
      by_cases h : (S.basisΛ k Θ).repr a r = 0
      · rw [h, zero_smul]
      · exact absurd (Finset.mem_image.2 ⟨_, Finset.mem_univ _, (h0 r h).symm⟩) hr),
      Finset.sum_image (fun x _ y _ h ↦ by rw [← S.P.src_e x, h, S.P.src_e])]
    symm
    refine Fintype.sum_equiv (idxA0 D v₀ hF).symm _ _ fun i ↦ ?_
    rw [FpA0_e_ΘD D v₀ hF Wd i, ← S.basisΛ_apply]
    rfl

theorem VxA0_e (i : Fin (VxA0 D v₀ hF Wd).n) : ∃ x, (VxA0 D v₀ hF Wd).e i =
    ΘD D v₀ hF Wd ((SysD D v₀ hF Wd).P.b k ((SysD D v₀ hF Wd).P.e x)) :=
  ⟨_, FpA0_e_ΘD D v₀ hF Wd i⟩

theorem rowWt_dual_eq {Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1}
    (hWd : ∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0) (j : ι) :
    rowWt (dualWt Wd) (Rw j) =
      latBasis (fun i ↦ ((Rw i).2.length : ℤ) - 2) (Sum.inl j) := by
  rw [rowWt_dualWt, latBasis_inl]
  refine Prod.ext (funext fun i ↦ ?_) rfl
  change rowWt (Wd i) (Rw j) = (Pi.single j (1 : ℤ) : ι → ℤ) i
  rw [hWd, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

/-- **The statement of Corollary 10.5** for `A₀` with the dual weights: every residual row
with a nonzero class in positive degree has a zero-supported representative with values in the
stem lines (`zero-supported-coverage`). -/
def Cor105 (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) : Prop :=
  ∀ i, (∃ q, 0 < q ∧ ∃ φ, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) φ ∧
        LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) q φ ∧
        LenGrading.IsCocycle₂ φ ∧ (latA0 (dualWt Wd) (hfinObj (c := c)) D).Char₂
          (rowWt (dualWt Wd) (Rw i)) φ ∧
        ¬ RaySys.Sys.IsCobdry k (lenA0 D (hfinObj (c := c))) q φ) →
      ∃ a : RayA0 D v₀ → RayA0 D v₀ → k, (SysD D v₀ hF Wd).EdgeOK k a ∧
        (∀ z : RayA0 D v₀ × RayA0 D v₀, a z.1 z.2 ≠ 0 → (SysD D v₀ hF Wd).eps z.1 z.2 ≠ 0 →
          (SysD D v₀ hF Wd).pairChar z = rowWt (dualWt Wd) (Rw i)) ∧
        ¬ RaySys.Sys.IsCobdry k (lenA0 D (hfinObj (c := c)))
          ((SysD D v₀ hF Wd).P.deg (rowWt (dualWt Wd) (Rw i))).toNat
          ((SysD D v₀ hF Wd).transp k (ΘD D v₀ hF Wd) ((SysD D v₀ hF Wd).coch k a))

/-- **The characteristic-two step on `A₀`** (proof of Proposition 8.3(1), with Proposition 7.9):
an algebra `B` which is a positive filtered deformation of `A₀` has a normed multiplicative ray
basis, given the rows of Proposition 6.1 with dual weights and the zero-supported
representatives of Corollary 10.5. -/
theorem char2_A0 (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hWd : ∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0)
    (hS : CokerSpan c (Set.range Rw))
    (hcor : Cor105 D v₀ hF Wd Rw)
    {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B]
    (P : PosFiltration (lenA0 D (hfinObj (c := c))) B) :
    ∃ (F : PrimitiveIdempotents B) (b : Module.Basis (F.NonzeroRay k) k B),
      IsNormedMultiplicativeBasis b ∧ F.IsRayTransversal b ∧
        ∃ (ι : D.PV ≃ Fin F.m) (β : RayA0 D v₀ → B), F.IsRayPres (k := k) (A0Mult D v₀ hF) ι β := by
  classical
  set S := SysD D v₀ hF Wd
  set Θ := ΘD D v₀ hF Wd
  set G := lenA0 D (hfinObj (c := c))
  set Wl := latA0 (dualWt Wd) (hfinObj (c := c)) D
  have hfinS : IsRepresentationFinite k (S.P.Lin k) := A0TabL_isRepresentationFinite D v₀ hF (dualWt Wd) lenCoord (hdg_dual D v₀ Wd)
  have hG := ΘD_lenHom D v₀ hF Wd
  have hW := ΘD_latHom D v₀ hF Wd
  set χ : ι → DLat ι := fun i ↦ rowWt (dualWt Wd) (Rw i)
  -- the rows with a nonzero class
  let good : ι → Prop := fun i ↦ ∃ q, 0 < q ∧ ∃ φ, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) φ ∧
    LenGrading.HasDeg₂ G q φ ∧
    LenGrading.IsCocycle₂ φ ∧ Wl.Char₂ (χ i) φ ∧ ¬ RaySys.Sys.IsCobdry k G q φ
  have hsel : ∀ i : {i // good i}, ∃ E : Quotient S.pairSetoid,
      (∀ z : RayA0 D v₀ × RayA0 D v₀, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 →
        S.pairChar z = χ i) ∧
      ¬ RaySys.Sys.IsCobdry k G (S.P.deg (χ i)).toNat (S.transp k Θ (S.muE k E)) ∧
      0 < S.P.deg (χ i) := by
    intro ⟨i, hi⟩
    obtain ⟨a, ha, hsupp, hnz⟩ := hcor i hi
    obtain ⟨E, hE, hEnz⟩ := S.select_class k hfinS Θ ha hsupp hnz
    refine ⟨E, hE, hEnz, ?_⟩
    obtain ⟨q, hq, φ, -, hφd, -, hφc, hφnz⟩ := hi
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hφnz (RaySys.Sys.isCobdry_zero k G q)
    have := S.deg_eq_of_ne_zero k Θ hG hW hφ0 hφd hφc
    change 0 < S.P.deg (χ i)
    omega
  choose Esel hEsel hEnz hχpos using hsel
  set n := Fintype.card {i // good i}
  set eI : Fin n ≃ {i // good i} := (Fintype.equivFin _).symm
  set E : Fin n → Quotient S.pairSetoid := fun j ↦ Esel (eI j)
  set qd : Fin n → ℕ := fun j ↦ (S.P.deg (χ (eI j))).toNat
  set μ : Fin n → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
    fun j ↦ S.transp k Θ (S.muE k (E j))
  have hχinj : ∀ a b : ι, χ a = χ b → a = b := by
    intro a b h
    have h' := congrArg (fun l : DLat ι ↦ (l : (ι → ℤ) × ℤ).1 a) h
    simp only [χ, rowWt_dualWt] at h'
    rw [hWd, hWd, if_pos rfl] at h'
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h'
    exact one_ne_zero h'
  have hEinj : Function.Injective E := by
    intro j j' h
    have h2 : ∀ z : RayA0 D v₀ × RayA0 D v₀, (⟦z⟧ : Quotient S.pairSetoid) = E j →
        S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ (eI j') :=
      fun z hz hz0 ↦ hEsel (eI j') z (hz.trans h) hz0
    have := S.classChar_unique k hfinS Θ (hEsel (eI j)) h2 (hEnz (eI j))
    exact eI.injective (Subtype.ext (hχinj _ _ this))
  have hdist : ∀ R ∈ Set.range Rw, ∀ R' ∈ Set.range Rw, rowWt (dualWt Wd) R = rowWt (dualWt Wd) R' →
      R = R' := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
    rw [hχinj a b h]
  have he0 : ∀ i, Wl.IsHom 0 ((VxA0 D v₀ hF Wd).e i) := by
    intro i
    obtain ⟨x, hx⟩ := VxA0_e D v₀ hF Wd i
    rw [hx]
    have := hW (S.P.e x)
    rwa [S.P.wt_e] at this
  have hrel : ∀ j, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) (μ j) := fun j ↦
    S.transp_isRel k hfinS Θ (VxA0 D v₀ hF Wd) (VxA0_e D v₀ hF Wd) _
  have hdeg : ∀ j, LenGrading.HasDeg₂ G (qd j) (μ j) := fun j ↦
    S.transp_muE_deg k hfinS Θ hG (hEsel (eI j)) (hχpos (eI j)).le
  have hcoc : ∀ j, LenGrading.IsCocycle₂ (μ j) := fun j ↦
    S.transp_coch_isCocycle k hfinS Θ (S.edgeOK_ind k (E j))
  have hchar : ∀ j, Wl.Char₂ (χ (eI j)) (μ j) := fun j ↦
    S.transp_muE_char k hfinS Θ hW (hEsel (eI j))
  have hspan := span_A0 (dualWt Wd) (hfinObj (c := c)) J h1 hS hdist (VxA0 D v₀ hF Wd) he0 μ qd
    (fun j ↦ Rw (eI j)) (fun j ↦ ⟨_, rfl⟩) hrel hcoc hdeg (fun j ↦ by
      have := hχpos (eI j); simp only [qd]; omega) hchar (fun j ↦ hEnz (eI j)) (by
      rintro _ ⟨i, rfl⟩
      by_cases hi : good i
      · exact Or.inl ⟨eI.symm ⟨i, hi⟩, by simp [eI]⟩
      · right
        intro q hq φ hφr hφd hφc hφχ
        by_contra hno
        exact hi ⟨q, hq, φ, hφr, hφd, hφc, hφχ, hno⟩)
  have H : LenGrading.FamilyHyp (VxA0 D v₀ hF Wd) μ qd :=
    ⟨fun j ↦ by have := hχpos (eI j); simp only [qd]; omega, hrel, hdeg,
      fun lam a b c ↦ S.transp_family_assoc k hfinS Θ E lam a b c, hspan⟩
  have hbasis : ∃ (κ : Type) (bL : Module.Basis κ ℤ (DLat ι)) (jj : Fin n → κ),
      Function.Injective jj ∧ ∀ j, bL (jj j) = χ (eI j) :=
    ⟨ι ⊕ Unit, latBasis (fun i ↦ ((Rw i).2.length : ℤ) - 2), fun j ↦ Sum.inl (eI j).1,
      fun j j' h ↦ eI.injective (Subtype.ext (Sum.inl_injective h)),
      fun j ↦ (rowWt_dual_eq Wd hWd _).symm⟩
  obtain ⟨lam, -, Ψ, hΨ, hnorm, htr, hpres⟩ := S.char2_core k hfinS (compat_A0 (dualWt Wd) hfinObj) Θ
    hEinj (χ := fun j ↦ χ (eI j)) (fun j ↦ hchar j) H he0 hbasis P
  exact ⟨_, _, hnorm, htr, _, _, hpres⟩

set_option maxHeartbeats 1000000 in
/-- **Remark 11.5, surjectivity**: the indicator cocycles of Proposition 11.2 (transported to
`A₀`) span `HH²(A₀)_{>0}`. Every normalized relative cocycle of positive internal degree `q` is a
combination of indicators `μ_{E_j}` of degree `q` plus a relative coboundary (the indicators
being normalized relative cocycles of positive degree). -/
theorem indicator_span_A0 (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hWd : ∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0)
    (hS : CokerSpan c (Set.range Rw))
    (hcor : Cor105 D v₀ hF Wd Rw) :
    ∃ (n : ℕ) (E : Fin n → Quotient (SysD D v₀ hF Wd).pairSetoid) (qd : Fin n → ℕ),
      (∀ j, 0 < qd j ∧
        LenGrading.IsRel₂ (VxA0 D v₀ hF Wd)
          ((SysD D v₀ hF Wd).transp k (ΘD D v₀ hF Wd) ((SysD D v₀ hF Wd).muE k (E j))) ∧
        LenGrading.IsCocycle₂
          ((SysD D v₀ hF Wd).transp k (ΘD D v₀ hF Wd) ((SysD D v₀ hF Wd).muE k (E j))) ∧
        LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) (qd j)
          ((SysD D v₀ hF Wd).transp k (ΘD D v₀ hF Wd) ((SysD D v₀ hF Wd).muE k (E j)))) ∧
      ∀ q, 0 < q → ∀ φ, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) φ →
        LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) q φ → LenGrading.IsCocycle₂ φ →
        ∃ (cf : Fin n → k) (f : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ),
          LenGrading.IsRel₁ (VxA0 D v₀ hF Wd) f ∧
          LenGrading.HasDeg₁ (lenA0 D (hfinObj (c := c))) q f ∧
          φ = (∑ j ∈ Finset.univ.filter (fun j ↦ qd j = q),
            cf j • (SysD D v₀ hF Wd).transp k (ΘD D v₀ hF Wd) ((SysD D v₀ hF Wd).muE k (E j))) +
            LenGrading.cobdry k f := by
  classical
  set S := SysD D v₀ hF Wd
  set Θ := ΘD D v₀ hF Wd
  set G := lenA0 D (hfinObj (c := c))
  set Wl := latA0 (dualWt Wd) (hfinObj (c := c)) D
  have hfinS : IsRepresentationFinite k (S.P.Lin k) := A0TabL_isRepresentationFinite D v₀ hF (dualWt Wd) lenCoord (hdg_dual D v₀ Wd)
  have hG := ΘD_lenHom D v₀ hF Wd
  have hW := ΘD_latHom D v₀ hF Wd
  set χ : ι → DLat ι := fun i ↦ rowWt (dualWt Wd) (Rw i)
  -- the rows with a nonzero class
  let good : ι → Prop := fun i ↦ ∃ q, 0 < q ∧ ∃ φ, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) φ ∧
    LenGrading.HasDeg₂ G q φ ∧
    LenGrading.IsCocycle₂ φ ∧ Wl.Char₂ (χ i) φ ∧ ¬ RaySys.Sys.IsCobdry k G q φ
  have hsel : ∀ i : {i // good i}, ∃ E : Quotient S.pairSetoid,
      (∀ z : RayA0 D v₀ × RayA0 D v₀, (⟦z⟧ : Quotient S.pairSetoid) = E → S.eps z.1 z.2 ≠ 0 →
        S.pairChar z = χ i) ∧
      ¬ RaySys.Sys.IsCobdry k G (S.P.deg (χ i)).toNat (S.transp k Θ (S.muE k E)) ∧
      0 < S.P.deg (χ i) := by
    intro ⟨i, hi⟩
    obtain ⟨a, ha, hsupp, hnz⟩ := hcor i hi
    obtain ⟨E, hE, hEnz⟩ := S.select_class k hfinS Θ ha hsupp hnz
    refine ⟨E, hE, hEnz, ?_⟩
    obtain ⟨q, hq, φ, -, hφd, -, hφc, hφnz⟩ := hi
    have hφ0 : φ ≠ 0 := by rintro rfl; exact hφnz (RaySys.Sys.isCobdry_zero k G q)
    have := S.deg_eq_of_ne_zero k Θ hG hW hφ0 hφd hφc
    change 0 < S.P.deg (χ i)
    omega
  choose Esel hEsel hEnz hχpos using hsel
  set n := Fintype.card {i // good i}
  set eI : Fin n ≃ {i // good i} := (Fintype.equivFin _).symm
  set E : Fin n → Quotient S.pairSetoid := fun j ↦ Esel (eI j)
  set qd : Fin n → ℕ := fun j ↦ (S.P.deg (χ (eI j))).toNat
  set μ : Fin n → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
    fun j ↦ S.transp k Θ (S.muE k (E j))
  have hχinj : ∀ a b : ι, χ a = χ b → a = b := by
    intro a b h
    have h' := congrArg (fun l : DLat ι ↦ (l : (ι → ℤ) × ℤ).1 a) h
    simp only [χ, rowWt_dualWt] at h'
    rw [hWd, hWd, if_pos rfl] at h'
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h'
    exact one_ne_zero h'
  have hEinj : Function.Injective E := by
    intro j j' h
    have h2 : ∀ z : RayA0 D v₀ × RayA0 D v₀, (⟦z⟧ : Quotient S.pairSetoid) = E j →
        S.eps z.1 z.2 ≠ 0 → S.pairChar z = χ (eI j') :=
      fun z hz hz0 ↦ hEsel (eI j') z (hz.trans h) hz0
    have := S.classChar_unique k hfinS Θ (hEsel (eI j)) h2 (hEnz (eI j))
    exact eI.injective (Subtype.ext (hχinj _ _ this))
  have hdist : ∀ R ∈ Set.range Rw, ∀ R' ∈ Set.range Rw, rowWt (dualWt Wd) R = rowWt (dualWt Wd) R' →
      R = R' := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
    rw [hχinj a b h]
  have he0 : ∀ i, Wl.IsHom 0 ((VxA0 D v₀ hF Wd).e i) := by
    intro i
    obtain ⟨x, hx⟩ := VxA0_e D v₀ hF Wd i
    rw [hx]
    have := hW (S.P.e x)
    rwa [S.P.wt_e] at this
  have hrel : ∀ j, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) (μ j) := fun j ↦
    S.transp_isRel k hfinS Θ (VxA0 D v₀ hF Wd) (VxA0_e D v₀ hF Wd) _
  have hdeg : ∀ j, LenGrading.HasDeg₂ G (qd j) (μ j) := fun j ↦
    S.transp_muE_deg k hfinS Θ hG (hEsel (eI j)) (hχpos (eI j)).le
  have hcoc : ∀ j, LenGrading.IsCocycle₂ (μ j) := fun j ↦
    S.transp_coch_isCocycle k hfinS Θ (S.edgeOK_ind k (E j))
  have hchar : ∀ j, Wl.Char₂ (χ (eI j)) (μ j) := fun j ↦
    S.transp_muE_char k hfinS Θ hW (hEsel (eI j))
  have hspan := span_A0 (dualWt Wd) (hfinObj (c := c)) J h1 hS hdist (VxA0 D v₀ hF Wd) he0 μ qd
    (fun j ↦ Rw (eI j)) (fun j ↦ ⟨_, rfl⟩) hrel hcoc hdeg (fun j ↦ by
      have := hχpos (eI j); simp only [qd]; omega) hchar (fun j ↦ hEnz (eI j)) (by
      rintro _ ⟨i, rfl⟩
      by_cases hi : good i
      · exact Or.inl ⟨eI.symm ⟨i, hi⟩, by simp [eI]⟩
      · right
        intro q hq φ hφr hφd hφc hφχ
        by_contra hno
        exact hi ⟨q, hq, φ, hφr, hφd, hφc, hφχ, hno⟩)
  exact ⟨n, E, qd, fun j ↦ ⟨by have := hχpos (eI j); simp only [qd]; omega, hrel j, hcoc j,
    hdeg j⟩, hspan⟩

end A0

end MeshWalk

end MultiplicativeBasisDeformations
