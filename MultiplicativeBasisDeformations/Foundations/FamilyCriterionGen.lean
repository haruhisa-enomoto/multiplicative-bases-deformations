module

public import MultiplicativeBasisDeformations.Foundations.FamilyCriterionA0

/-!
# Proposition 7.9 on `A₀` for characters in any lattice

The setting of `FamilyCriterionA0.lean` with the dual mesh weights replaced by an arbitrary mesh
weight `W` with values in a lattice `Lt` and a degree map `dg : Lt → ℤ` recovering the length
(`dg ∘ W.res = lenW.res`). The characters are the relative row weights `rowCharG W Rw i`; instead of
the dual-weight identities, the hypotheses are that these characters are pairwise distinct and part
of an integer basis of `Lt` (Proposition 7.5 for `Lt = W(P)`). The definitions and proofs are
those of the dual-weight case (`SysG`, `ΘG`, `VxG`, `HH2NonzeroG`, `I0G`, `famMulG`, `fibAMG`,
`familyCriterion_G`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

section Gen

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  {Lt : Type} [AddCommGroup Lt] (W : MeshWt Q Lt) (dg : Lt →+ ℤ)
  (hdg : dg.comp (W.res (v₀ := v₀) c D) = (lenW (Q := Q)).res (v₀ := v₀) c D)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)

/-- The ray system of `A₀` with the dual weights. -/
abbrev SysG : RaySys.Sys D.PV (RayA0 D v₀) (Lt) :=
  A0SysL D v₀ hF W dg hdg

/-- `kP ≅ A₀`. -/
abbrev ΘG : (SysG D v₀ hF W dg hdg).P.Lin k ≃ₐ[k] (Alg D.F0)ᵐᵒᵖ :=
  thetaA0L D v₀ hF W dg hdg

theorem ΘG_b (t : RayA0 D v₀) : ΘG D v₀ hF W dg hdg ((SysG D v₀ hF W dg hdg).P.b k t) = basisR D v₀ hF t :=
  thetaA0L_b D v₀ hF _ _ _ t

theorem SysG_deg_wt (t : RayA0 D v₀) {p : Quiver.Path t.1.1.1 t.1.2.1.1}
    (hp : (degW Q v₀).deg p = t.1.2.2) :
    (SysG D v₀ hF W dg hdg).P.deg ((SysG D v₀ hF W dg hdg).P.wt t) = p.length := by
  change dg (wtLat D v₀ W t) = _
  rw [dg_wtLat D v₀ W dg hdg, degR_wtR_path D v₀ hp]

/-- **The ray basis is length-homogeneous.** -/
theorem ΘG_lenHom (t : RayA0 D v₀) :
    (lenA0 D (hfinObj (c := c))).IsHom ((SysG D v₀ hF W dg hdg).P.deg ((SysG D v₀ hF W dg hdg).P.wt t)).toNat
      (ΘG D v₀ hF W dg hdg ((SysG D v₀ hF W dg hdg).P.b k t)) := by
  obtain ⟨⟨x, y, g⟩, ht⟩ := t
  obtain ⟨p, hp⟩ := exists_path_of_nz ht
  rw [SysG_deg_wt D v₀ hF W dg hdg ⟨(x, y, g), ht⟩ hp, Int.toNat_natCast, ΘG_b]
  exact basisR_isHom D v₀ hF ht hp

/-- **The ray basis is weight-homogeneous.** -/
theorem ΘG_latHom (t : RayA0 D v₀) :
    (latA0 W (hfinObj (c := c)) D).IsHom ((SysG D v₀ hF W dg hdg).P.wt t)
      (ΘG D v₀ hF W dg hdg ((SysG D v₀ hF W dg hdg).P.b k t)) := by
  obtain ⟨⟨x, y, g⟩, ht⟩ := t
  obtain ⟨p, hp⟩ := exists_path_of_nz ht
  rw [ΘG_b, latA0_isHom, grA0_isHom]
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
      have hw : (SysG D v₀ hF W dg hdg).P.wt ⟨(p', q', g), ht⟩ = W.pw p := by
        change W.res c D (cls Q c v₀ D (p', q', g)) = _
        rw [MeshWt.res_cls, MeshWt.rv_path _ ht hp]
      rw [hw]
      refine Submodule.span_le.2 ?_ (wPart_le_span Q c v₀ g p'.1 q'.1 hf)
      rintro _ ⟨p'', hp'', rfl⟩
      have e : W.pw p'' = W.pw p := by
        have h1 := MeshWt.rv_path (c := c) (D := D) W ht hp
        have h2 := MeshWt.rv_path (c := c) (D := D) W ht hp''
        exact h2.symm.trans h1
      rw [← e]
      exact pathMor_mem_wP W p''
    · rw [idTo_ne (Ne.symm hy), Limits.comp_zero, Limits.comp_zero]; exact Submodule.zero_mem _
  · rw [idTo_ne hx, Limits.zero_comp]; exact Submodule.zero_mem _

theorem FpA0_e_ΘG (i : Fin (FpA0 D v₀ hF).m) :
    (FpA0 D v₀ hF).e i = ΘG D v₀ hF W dg hdg ((SysG D v₀ hF W dg hdg).P.b k
      ((SysG D v₀ hF W dg hdg).P.e ((Fintype.equivFin D.PV).symm i))) := by
  rw [ΘG_b]; rfl

/-- **The vertex idempotents of `A₀`** as degree-zero vertices. -/
def VxG : LenGrading.Vertices (lenA0 D (hfinObj (c := c))) where
  n := (FpA0 D v₀ hF).m
  e := (FpA0 D v₀ hF).e
  complete := (FpA0 D v₀ hF).complete
  deg0 := FpA0_he0 D v₀ hF
  span0 a ha := by
    classical
    set S := SysG D v₀ hF W dg hdg
    set Θ := ΘG D v₀ hF W dg hdg
    have hG := ΘG_lenHom D v₀ hF W dg hdg
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
    rw [FpA0_e_ΘG D v₀ hF W dg hdg i, ← S.basisΛ_apply]
    rfl

theorem VxG_e (i : Fin (VxG D v₀ hF W dg hdg).n) : ∃ x, (VxG D v₀ hF W dg hdg).e i =
    ΘG D v₀ hF W dg hdg ((SysG D v₀ hF W dg hdg).P.b k ((SysG D v₀ hF W dg hdg).P.e x)) :=
  ⟨_, FpA0_e_ΘG D v₀ hF W dg hdg i⟩

/-- The character `χ_i` of a row of Proposition 6.1. -/
abbrev rowCharG (i : ι) : Lt := rowWt W (Rw i)

/-- A row with a nonzero space `HH²(A₀)_{χ_i}` in positive internal degree. -/
def HH2NonzeroG (i : ι) : Prop :=
  ∃ q, 0 < q ∧ ∃ φ, LenGrading.IsRel₂ (VxG D v₀ hF W dg hdg) φ ∧
    LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) q φ ∧ LenGrading.IsCocycle₂ φ ∧
    (latA0 W (hfinObj (c := c)) D).Char₂ (rowCharG W Rw i) φ ∧
    ¬ RaySys.Sys.IsCobdry k (lenA0 D (hfinObj (c := c))) q φ

/-- **The index set `I₀`.** -/
abbrev I0G := {i // HH2NonzeroG D v₀ hF W dg hdg Rw i}

instance : Fintype (I0G D v₀ hF W dg hdg Rw) := Fintype.ofFinite _

variable {D v₀ hF W dg hdg Rw} in
/-- The family product `m + Σ λ_i μ_i`. -/
def famMulG (μ : I0G D v₀ hF W dg hdg Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (lam : I0G D v₀ hF W dg hdg Rw → k) : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
  LinearMap.mul k _ + ∑ i, lam i • μ i

theorem famMulG_apply (μ : I0G D v₀ hF W dg hdg Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (lam : I0G D v₀ hF W dg hdg Rw → k) (a b : (Alg D.F0)ᵐᵒᵖ) :
    famMulG μ lam a b = a * b + ∑ i, lam i • μ i a b := by
  simp [famMulG, LinearMap.sum_apply]

theorem mLam_reindexG {n : ℕ} (e : Fin n ≃ I0G D v₀ hF W dg hdg Rw)
    (μ : I0G D v₀ hF W dg hdg Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (lam : Fin n → k) (a b : (Alg D.F0)ᵐᵒᵖ) :
    LenGrading.mLam (fun j ↦ μ (e j)) lam a b = famMulG μ (fun i ↦ lam (e.symm i)) a b := by
  rw [LenGrading.mLam_apply, famMulG_apply]
  congr 1
  rw [← e.sum_comp (fun i ↦ lam (e.symm i) • μ i a b)]
  simp

variable {D v₀ hF W dg hdg Rw} in
/-- A binary or scalar fibre: the family product at `lam` as an associative unital product. -/
def fibAMG {μ : I0G D v₀ hF W dg hdg Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (hrel : ∀ i, LenGrading.IsRel₂ (VxG D v₀ hF W dg hdg) (μ i))
    (hassoc : ∀ (lam : I0G D v₀ hF W dg hdg Rw → k) (a b z : (Alg D.F0)ᵐᵒᵖ),
      famMulG μ lam (famMulG μ lam a b) z = famMulG μ lam a (famMulG μ lam b z))
    (lam : I0G D v₀ hF W dg hdg Rw → k) : AssocMul k (Alg D.F0)ᵐᵒᵖ where
  mm := famMulG μ lam
  assoc := hassoc lam
  one_left a := by
    rw [famMulG_apply, one_mul, add_eq_left]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← (VxG D v₀ hF W dg hdg).complete.complete, map_sum, LinearMap.sum_apply]
    simp [(hrel i).unitL]
  one_right a := by
    rw [famMulG_apply, mul_one, add_eq_left]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← (VxG D v₀ hF W dg hdg).complete.complete, map_sum]
    simp [(hrel i).unitR]

/-- **Proposition 7.9 on `A₀`** (`prop:family-criterion`): for the rows and characters of
Proposition 6.1 and any family `μ_i`, `i ∈ I₀`, of normalized `S`-relative cocycles of character
`χ_i` with nonzero classes, whose family product is associative and whose binary fibres have the
basis of `kP` as a normed multiplicative basis with ray category `P`: every positive filtered
deformation `B` of `A₀` is isomorphic to a binary fibre; the transported basis is a normed
multiplicative ray basis of `B` presenting `P`, and the leading term of the image of each ray
vector `b_r` is a nonzero multiple of `b_r`. -/
theorem familyCriterion_G (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (hχinj : Function.Injective fun i ↦ rowCharG W Rw i)
    (hbasisι : ∃ (κ : Type) (bL : Module.Basis κ ℤ Lt) (jι : ι → κ),
      Function.Injective jι ∧ ∀ i, bL (jι i) = rowCharG W Rw i)
    (hS : CokerSpan c (Set.range Rw))
    (μ : I0G D v₀ hF W dg hdg Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (hrel : ∀ i, LenGrading.IsRel₂ (VxG D v₀ hF W dg hdg) (μ i))
    (hchar : ∀ i, (latA0 W (hfinObj (c := c)) D).Char₂ (rowCharG W Rw i.1) (μ i))
    (hcoc : ∀ i, LenGrading.IsCocycle₂ (μ i))
    (hnz : ∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f)
    (hassoc : ∀ (lam : I0G D v₀ hF W dg hdg Rw → k) (a b z : (Alg D.F0)ᵐᵒᵖ),
      famMulG μ lam (famMulG μ lam a b) z = famMulG μ lam a (famMulG μ lam b z))
    (hfib : ∀ lam : I0G D v₀ hF W dg hdg Rw → k, (∀ i, lam i = 0 ∨ lam i = 1) →
      IsNormedMultiplicativeBasis ((basisR D v₀ hF).map (Fib.toΛ (fibAMG hrel hassoc lam)).symm) ∧
        ∃ (F : PrimitiveIdempotents (Fib (fibAMG hrel hassoc lam))) (ιF : D.PV ≃ Fin F.m),
          F.IsRayPres (k := k) (A0Mult D v₀ hF) ιF
            (fun r ↦ (Fib.toΛ (fibAMG hrel hassoc lam)).symm (basisR D v₀ hF r)))
    {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B] (Pf : PosFiltration (lenA0 D (hfinObj (c := c))) B) :
    ∃ (lam : I0G D v₀ hF W dg hdg Rw → k) (_ : ∀ i, lam i = 0 ∨ lam i = 1)
      (Ψ : (Alg D.F0)ᵐᵒᵖ ≃ₗ[k] B),
      (∀ a b, Ψ (famMulG μ lam a b) = Ψ a * Ψ b) ∧
      (∀ d, Submodule.map Ψ.toLinearMap ((lenA0 D (hfinObj (c := c))).geSub d) = Pf.F d) ∧
      IsNormedMultiplicativeBasis ((basisR D v₀ hF).map Ψ) ∧
      (∃ (F : PrimitiveIdempotents B) (ιF : D.PV ≃ Fin F.m),
        F.IsRayPres (k := k) (A0Mult D v₀ hF) ιF (fun r ↦ Ψ (basisR D v₀ hF r))) ∧
      ∀ r, ∃ t : k, t ≠ 0 ∧
        Pf.σ ((SysG D v₀ hF W dg hdg).P.deg ((SysG D v₀ hF W dg hdg).P.wt r)).toNat (Ψ (basisR D v₀ hF r)) =
          t • basisR D v₀ hF r := by
  classical
  set S := SysG D v₀ hF W dg hdg
  set Θ := ΘG D v₀ hF W dg hdg
  have hG := ΘG_lenHom D v₀ hF W dg hdg
  have hW := ΘG_latHom D v₀ hF W dg hdg
  -- positive internal degrees
  have hpos : ∀ i : I0G D v₀ hF W dg hdg Rw, 0 < S.P.deg (rowCharG W Rw i.1) := by
    intro ⟨i, hi⟩
    obtain ⟨q, hq, φ, -, hφd, -, hφc, hφnz⟩ := hi
    have hφ0 : φ ≠ 0 := by
      rintro rfl; exact hφnz (RaySys.Sys.isCobdry_zero k (lenA0 D (hfinObj (c := c))) q)
    have := S.deg_eq_of_ne_zero k Θ hG hW hφ0 hφd hφc
    change 0 < S.P.deg (rowCharG W Rw i)
    omega
  set n := Fintype.card (I0G D v₀ hF W dg hdg Rw)
  set e : Fin n ≃ I0G D v₀ hF W dg hdg Rw := (Fintype.equivFin _).symm
  set μF : Fin n → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ := fun j ↦ μ (e j)
  set qd : Fin n → ℕ := fun j ↦ (S.P.deg (rowCharG W Rw (e j).1)).toNat
  have hdeg : ∀ j, LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) (qd j) (μF j) := fun j ↦
    S.hasDeg₂_of_char k Θ hG hW (hpos (e j)).le (hchar (e j))
  have hdist : ∀ R ∈ Set.range Rw, ∀ R' ∈ Set.range Rw,
      rowWt W R = rowWt W R' → R = R' := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
    rw [hχinj h]
  have he0 : ∀ i, (latA0 W (hfinObj (c := c)) D).IsHom 0 ((VxG D v₀ hF W dg hdg).e i) := by
    intro i
    obtain ⟨x, hx⟩ := VxG_e D v₀ hF W dg hdg i
    rw [hx]
    have := hW (S.P.e x)
    rwa [S.P.wt_e] at this
  have hspan := span_A0 W (hfinObj (c := c)) J h1 hS hdist (VxG D v₀ hF W dg hdg) he0 μF qd
    (fun j ↦ Rw (e j).1) (fun j ↦ ⟨_, rfl⟩) (fun j ↦ hrel (e j)) (fun j ↦ hcoc (e j)) hdeg
    (fun j ↦ by have := hpos (e j); simp only [qd]; omega) (fun j ↦ hchar (e j))
    (fun j h ↦ by obtain ⟨H, -, hH⟩ := h; exact hnz (e j) ⟨H, hH⟩) (by
      rintro _ ⟨i, rfl⟩
      by_cases hi : HH2NonzeroG D v₀ hF W dg hdg Rw i
      · exact Or.inl ⟨e.symm ⟨i, hi⟩, by simp⟩
      · right
        intro q hq φ hφr hφd hφc hφχ
        by_contra hno
        exact hi ⟨q, hq, φ, hφr, hφd, hφc, hφχ, hno⟩)
  have H : LenGrading.FamilyHyp (VxG D v₀ hF W dg hdg) μF qd :=
    ⟨fun j ↦ by have := hpos (e j); simp only [qd]; omega, fun j ↦ hrel (e j), hdeg,
      (fun lam a b z ↦ by
        simp only [μF, mLam_reindexG D v₀ hF W dg hdg Rw e]
        exact hassoc _ a b z), hspan⟩
  have hbasis : ∃ (κ : Type) (bL : Module.Basis κ ℤ Lt) (jj : Fin n → κ),
      Function.Injective jj ∧ ∀ j, bL (jj j) = rowCharG W Rw (e j).1 := by
    obtain ⟨κ, bL, jι, hjι, hb⟩ := hbasisι
    exact ⟨κ, bL, fun j ↦ jι (e j).1, fun j j' h ↦ e.injective (Subtype.ext (hjι h)),
      fun j ↦ hb _⟩
  obtain ⟨⟨lam, hlam, Ψ, hΨ, hΨe, hΨF, cσ, hσ⟩, -⟩ := LenGrading.binaryNormalization
    (compat_A0 W (hfinObj (c := c))) (χ := fun j ↦ rowCharG W Rw (e j).1)
    (fun j ↦ hchar (e j)) H he0 hbasis Pf
  set lamI : I0G D v₀ hF W dg hdg Rw → k := fun i ↦ lam (e.symm i)
  have hlamI : ∀ i, lamI i = 0 ∨ lamI i = 1 := fun i ↦ hlam _
  have hΨ' : ∀ a b, Ψ (famMulG μ lamI a b) = Ψ a * Ψ b := by
    intro a b
    rw [← hΨ, mLam_reindexG D v₀ hF W dg hdg Rw e]
  -- the binary fibre is isomorphic to `B`
  let Φ : Fib (fibAMG hrel hassoc lamI) ≃ₐ[k] B :=
    AlgEquiv.ofLinearEquiv ((Fib.toΛ (fibAMG hrel hassoc lamI)).trans Ψ)
      (by
        change Ψ 1 = 1
        rw [← (VxG D v₀ hF W dg hdg).complete.complete, map_sum]
        exact hΨe.complete)
      (fun a b' ↦ hΨ' _ _)
  have : FiniteDimensional k (Alg D.F0)ᵐᵒᵖ := Module.Finite.of_basis (basisR D v₀ hF)
  have : FiniteDimensional k (Fib (fibAMG hrel hassoc lamI)) :=
    LinearEquiv.finiteDimensional (Fib.toΛ (fibAMG hrel hassoc lamI)).symm
  obtain ⟨hnormF, F, ιF, hpresF⟩ := hfib lamI hlamI
  have hnorm : IsNormedMultiplicativeBasis ((basisR D v₀ hF).map Ψ) := by
    have e : (basisR D v₀ hF).map Ψ = ((basisR D v₀ hF).map
        (Fib.toΛ (fibAMG hrel hassoc lamI)).symm).map Φ.symm.symm.toLinearEquiv :=
      Module.Basis.eq_of_apply_eq fun r ↦ rfl
    rw [e]
    exact hnormF.map_algEquiv Φ.symm
  have hpres := hpresF.map Φ (F.mapEquiv Φ) (Equiv.refl _) (fun i ↦ rfl)
  refine ⟨lamI, hlamI, Ψ, hΨ', hΨF, hnorm, ⟨_, _, hpres⟩, fun r ↦ ⟨(cσ (S.P.wt r) : k), Units.ne_zero _, ?_⟩⟩
  have h := hσ _ _ _ (hG r) (hW r)
  rw [ΘG_b] at h
  exact h

/-- The conclusion of Proposition 7.9 on `A₀` for a positive filtered deformation `B`, as a
predicate on the data: for every family with the hypotheses (1)–(3), the conclusions hold. -/
def FamilyCriterionStmt [Fintype Q.nonprojective] {B : Type u} [Ring B] [Algebra k B]
    (Pf : PosFiltration (lenA0 D (hfinObj (c := c))) B) : Prop :=
  ∀ (μ : I0G D v₀ hF W dg hdg Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (hrel : ∀ i, LenGrading.IsRel₂ (VxG D v₀ hF W dg hdg) (μ i))
    (hchar : ∀ i, (latA0 W (hfinObj (c := c)) D).Char₂ (rowCharG W Rw i.1) (μ i))
    (hcoc : ∀ i, LenGrading.IsCocycle₂ (μ i))
    (hnz : ∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f)
    (hassoc : ∀ (lam : I0G D v₀ hF W dg hdg Rw → k) (a b z : (Alg D.F0)ᵐᵒᵖ),
      famMulG μ lam (famMulG μ lam a b) z = famMulG μ lam a (famMulG μ lam b z))
    (hfib : ∀ lam : I0G D v₀ hF W dg hdg Rw → k, (∀ i, lam i = 0 ∨ lam i = 1) →
      IsNormedMultiplicativeBasis ((basisR D v₀ hF).map (Fib.toΛ (fibAMG hrel hassoc lam)).symm) ∧
        ∃ (F : PrimitiveIdempotents (Fib (fibAMG hrel hassoc lam))) (ιF : D.PV ≃ Fin F.m),
          F.IsRayPres (k := k) (A0Mult D v₀ hF) ιF
            (fun r ↦ (Fib.toΛ (fibAMG hrel hassoc lam)).symm (basisR D v₀ hF r))),
    ∃ (lam : I0G D v₀ hF W dg hdg Rw → k) (_ : ∀ i, lam i = 0 ∨ lam i = 1)
      (Ψ : (Alg D.F0)ᵐᵒᵖ ≃ₗ[k] B),
      (∀ a b, Ψ (famMulG μ lam a b) = Ψ a * Ψ b) ∧
      (∀ d, Submodule.map Ψ.toLinearMap ((lenA0 D (hfinObj (c := c))).geSub d) = Pf.F d) ∧
      IsNormedMultiplicativeBasis ((basisR D v₀ hF).map Ψ) ∧
      (∃ (F : PrimitiveIdempotents B) (ιF : D.PV ≃ Fin F.m),
        F.IsRayPres (k := k) (A0Mult D v₀ hF) ιF (fun r ↦ Ψ (basisR D v₀ hF r))) ∧
      ∀ r, ∃ t : k, t ≠ 0 ∧
        Pf.σ ((SysG D v₀ hF W dg hdg).P.deg ((SysG D v₀ hF W dg hdg).P.wt r)).toNat (Ψ (basisR D v₀ hF r)) =
          t • basisR D v₀ hF r

theorem familyCriterionStmt_G (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (hS : CokerSpan c (Set.range Rw))
    (hχinj : Function.Injective fun i ↦ rowCharG W Rw i)
    (hbasisι : ∃ (κ : Type) (bL : Module.Basis κ ℤ Lt) (jι : ι → κ),
      Function.Injective jι ∧ ∀ i, bL (jι i) = rowCharG W Rw i)
    {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B]
    (Pf : PosFiltration (lenA0 D (hfinObj (c := c))) B) :
    FamilyCriterionStmt D v₀ hF W dg hdg Rw Pf :=
  fun μ hrel hchar hcoc hnz hassoc hfib ↦
    familyCriterion_G D v₀ hF W dg hdg Rw J h1 hχinj hbasisι hS μ hrel hchar hcoc hnz hassoc hfib Pf

end Gen

end MeshWalk

end MultiplicativeBasisDeformations
