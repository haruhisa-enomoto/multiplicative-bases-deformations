module

public import MultiplicativeBasisDeformations.Foundations.Char2A0
public import MultiplicativeBasisDeformations.Foundations.RayTransport
public import MultiplicativeBasisDeformations.Foundations.NormedTransport
public import MultiplicativeBasisDeformations.Refinements.FibreAlgebra

/-!
# Proposition 7.9 on `A₀` for an arbitrary family

`prop:family-criterion` (`characteristic-two-construction.tex`): let `I₀` index the nonzero
spaces `HH²(A₀)_{χ_i}` of Proposition 6.1, and let normalized `S`-relative two-cochains `μ_i`,
`i ∈ I₀`, satisfy (1) each `μ_i` is homogeneous of character `χ_i` with nonzero class, (2) the
family product `m + Σ t_i μ_i` is associative, (3) every binary fibre has the basis of `kP` as a
normed multiplicative basis, and every scalar fibre has ray category `P`. Then a binary fibre is isomorphic to `A`, the
transported basis is a normed multiplicative ray basis, and the isomorphism preserves each initial
ray line up to a nonzero scalar.

Here the rows and characters are those of Proposition 6.1 with their dual mesh weights
(`rowChar`), `I₀` is the set of rows with a nonzero class in positive internal degree
(`HH2Nonzero`, `I0`), and `A` is any positive filtered deformation `B` of `A₀`
(`familyCriterion_A0`). The internal degree of `μ_i` is not assumed: it is the length coordinate
of `χ_i` (`RaySys.Sys.hasDeg₂_of_char`). Associativity is required at every scalar parameter,
which follows from associativity over the polynomial ring. Hypothesis (3) is stated on the
fibre algebra itself (`Fib (fibAM …)`), and used for binary fibres; it is transported to `B`
along the isomorphism (`IsNormedMultiplicativeBasis.map_algEquiv`, `IsRayPres.map`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace RaySys

namespace Sys

variable {V R L : Type} [AddCommGroup L] [DecidableEq L] [Fintype V] [DecidableEq V] [Fintype R]
  [DecidableEq R] (S : Sys V R L) (k : Type u) [Field k] [IsAlgClosed k]
  {Λ : Type u} [Ring Λ] [Algebra k Λ] (Θ : S.P.Lin k ≃ₐ[k] Λ)
  {G : LenGrading k Λ} {W : LatGrading k Λ L}
  (hG : ∀ r, G.IsHom (S.P.deg (S.P.wt r)).toNat (Θ (S.P.b k r)))
  (hW : ∀ r, W.IsHom (S.P.wt r) (Θ (S.P.b k r)))

include hG hW in
/-- **A cochain of character `χ` has internal degree `deg χ`.** -/
theorem hasDeg₂_of_char {χ : L} (hχ : 0 ≤ S.P.deg χ) {φ : Λ →ₗ[k] Λ →ₗ[k] Λ}
    (hc : W.Char₂ χ φ) : LenGrading.HasDeg₂ G (S.P.deg χ).toNat φ := by
  classical
  have hbG : ∀ r, G.IsHom (S.P.deg (S.P.wt r)).toNat (S.basisΛ k Θ r) :=
    fun r ↦ by rw [basisΛ_apply]; exact hG r
  have hbW : ∀ r, W.IsHom (S.P.wt r) (S.basisΛ k Θ r) := fun r ↦ by rw [basisΛ_apply]; exact hW r
  refine G.hasDeg₂_of_basis (S.basisΛ k Θ) (fun r ↦ (S.P.deg (S.P.wt r)).toNat) hbG _ _
    fun u v ↦ ?_
  have hy := hc _ _ _ _ (hbW u) (hbW v)
  rw [← (S.basisΛ k Θ).sum_repr (φ (S.basisΛ k Θ u) (S.basisΛ k Θ v))]
  refine LenGrading.isHom_sum G _ _ fun t _ ↦ ?_
  by_cases ht : S.P.wt t = S.P.wt u + S.P.wt v + χ
  · refine G.isHom_smul' _ ?_
    have := hbG t
    have h1 := S.P.deg_nonneg u
    have h2 := S.P.deg_nonneg v
    rw [ht, map_add, map_add] at this
    convert this using 1
    omega
  · rw [W.repr_eq_zero_of_isHom (S.basisΛ k Θ) S.P.wt hbW hy ht, zero_smul]
    exact G.isHom_zero' _

end Sys

end RaySys

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

section A0

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)
  [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (Wd : ι → MeshWt Q ℤ)
  (Rw : ι → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)

/-- The character `χ_i` of a row of Proposition 6.1. -/
abbrev rowChar (i : ι) : DLat ι := rowWt (dualWt Wd) (Rw i)

/-- A row with a nonzero space `HH²(A₀)_{χ_i}` in positive internal degree. -/
def HH2Nonzero (i : ι) : Prop :=
  ∃ q, 0 < q ∧ ∃ φ, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) φ ∧
    LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) q φ ∧ LenGrading.IsCocycle₂ φ ∧
    (latA0 (dualWt Wd) (hfinObj (c := c)) D).Char₂ (rowChar Wd Rw i) φ ∧
    ¬ RaySys.Sys.IsCobdry k (lenA0 D (hfinObj (c := c))) q φ

/-- **The index set `I₀`.** -/
abbrev I0 := {i // HH2Nonzero D v₀ hF Wd Rw i}

instance : Fintype (I0 D v₀ hF Wd Rw) := Fintype.ofFinite _

variable {D v₀ hF Wd Rw} in
/-- The family product `m + Σ λ_i μ_i`. -/
def famMulI (μ : I0 D v₀ hF Wd Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (lam : I0 D v₀ hF Wd Rw → k) : (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ :=
  LinearMap.mul k _ + ∑ i, lam i • μ i

theorem famMulI_apply (μ : I0 D v₀ hF Wd Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (lam : I0 D v₀ hF Wd Rw → k) (a b : (Alg D.F0)ᵐᵒᵖ) :
    famMulI μ lam a b = a * b + ∑ i, lam i • μ i a b := by
  simp [famMulI, LinearMap.sum_apply]

theorem mLam_reindex {n : ℕ} (e : Fin n ≃ I0 D v₀ hF Wd Rw)
    (μ : I0 D v₀ hF Wd Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (lam : Fin n → k) (a b : (Alg D.F0)ᵐᵒᵖ) :
    LenGrading.mLam (fun j ↦ μ (e j)) lam a b = famMulI μ (fun i ↦ lam (e.symm i)) a b := by
  rw [LenGrading.mLam_apply, famMulI_apply]
  congr 1
  rw [← e.sum_comp (fun i ↦ lam (e.symm i) • μ i a b)]
  simp

variable {D v₀ hF Wd Rw} in
/-- A binary or scalar fibre: the family product at `lam` as an associative unital product. -/
def fibAM {μ : I0 D v₀ hF Wd Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ}
    (hrel : ∀ i, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) (μ i))
    (hassoc : ∀ (lam : I0 D v₀ hF Wd Rw → k) (a b z : (Alg D.F0)ᵐᵒᵖ),
      famMulI μ lam (famMulI μ lam a b) z = famMulI μ lam a (famMulI μ lam b z))
    (lam : I0 D v₀ hF Wd Rw → k) : AssocMul k (Alg D.F0)ᵐᵒᵖ where
  mm := famMulI μ lam
  assoc := hassoc lam
  one_left a := by
    rw [famMulI_apply, one_mul, add_eq_left]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← (VxA0 D v₀ hF Wd).complete.complete, map_sum, LinearMap.sum_apply]
    simp [(hrel i).unitL]
  one_right a := by
    rw [famMulI_apply, mul_one, add_eq_left]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [← (VxA0 D v₀ hF Wd).complete.complete, map_sum]
    simp [(hrel i).unitR]

/-- The image of a complete set of primitive idempotents under an algebra isomorphism. -/
def _root_.MultiplicativeBasisDeformations.PrimitiveIdempotents.mapEquiv {B B' : Type u} [Ring B]
    [Algebra k B] [Ring B'] [Algebra k B'] (F : PrimitiveIdempotents B) (ψ : B ≃ₐ[k] B') :
    PrimitiveIdempotents B' where
  m := F.m
  e i := ψ (F.e i)
  complete := F.complete.map (ψ : B →+* B')
  primitive i := isPrimitiveIdempotent_map ψ (F.primitive i)

/-- **Proposition 7.9 on `A₀`** (`prop:family-criterion`): for the rows and characters of
Proposition 6.1 and any family `μ_i`, `i ∈ I₀`, of normalized `S`-relative cocycles of character
`χ_i` with nonzero classes, whose family product is associative and whose binary fibres have the
basis of `kP` as a normed multiplicative basis with ray category `P`: every positive filtered
deformation `B` of `A₀` is isomorphic to a binary fibre; the transported basis is a normed
multiplicative ray basis of `B` presenting `P`, and the leading term of the image of each ray
vector `b_r` is a nonzero multiple of `b_r`. -/
theorem familyCriterion_A0 (J : D.InjData) (h1 : DegOne D) [Fintype Q.nonprojective]
    (hWd : ∀ i j, rowWt (Wd i) (Rw j) = if j = i then 1 else 0)
    (hS : CokerSpan c (Set.range Rw))
    (μ : I0 D v₀ hF Wd Rw → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ)
    (hrel : ∀ i, LenGrading.IsRel₂ (VxA0 D v₀ hF Wd) (μ i))
    (hchar : ∀ i, (latA0 (dualWt Wd) (hfinObj (c := c)) D).Char₂ (rowChar Wd Rw i.1) (μ i))
    (hcoc : ∀ i, LenGrading.IsCocycle₂ (μ i))
    (hnz : ∀ i, ¬ ∃ f, μ i = LenGrading.cobdry k f)
    (hassoc : ∀ (lam : I0 D v₀ hF Wd Rw → k) (a b z : (Alg D.F0)ᵐᵒᵖ),
      famMulI μ lam (famMulI μ lam a b) z = famMulI μ lam a (famMulI μ lam b z))
    (hfib : ∀ lam : I0 D v₀ hF Wd Rw → k, (∀ i, lam i = 0 ∨ lam i = 1) →
      IsNormedMultiplicativeBasis ((basisR D v₀ hF).map (Fib.toΛ (fibAM hrel hassoc lam)).symm) ∧
        ∃ (F : PrimitiveIdempotents (Fib (fibAM hrel hassoc lam))) (ιF : D.PV ≃ Fin F.m),
          F.IsRayPres (k := k) (A0Mult D v₀ hF) ιF
            (fun r ↦ (Fib.toΛ (fibAM hrel hassoc lam)).symm (basisR D v₀ hF r)))
    {B : Type u} [Ring B] [Algebra k B] [FiniteDimensional k B] (Pf : PosFiltration (lenA0 D (hfinObj (c := c))) B) :
    ∃ (lam : I0 D v₀ hF Wd Rw → k) (_ : ∀ i, lam i = 0 ∨ lam i = 1)
      (Ψ : (Alg D.F0)ᵐᵒᵖ ≃ₗ[k] B),
      (∀ a b, Ψ (famMulI μ lam a b) = Ψ a * Ψ b) ∧
      IsNormedMultiplicativeBasis ((basisR D v₀ hF).map Ψ) ∧
      (∃ (F : PrimitiveIdempotents B) (ιF : D.PV ≃ Fin F.m),
        F.IsRayPres (k := k) (A0Mult D v₀ hF) ιF (fun r ↦ Ψ (basisR D v₀ hF r))) ∧
      ∀ r, ∃ t : k, t ≠ 0 ∧
        Pf.σ ((SysD D v₀ hF Wd).P.deg ((SysD D v₀ hF Wd).P.wt r)).toNat (Ψ (basisR D v₀ hF r)) =
          t • basisR D v₀ hF r := by
  classical
  set S := SysD D v₀ hF Wd
  set Θ := ΘD D v₀ hF Wd
  have hG := ΘD_lenHom D v₀ hF Wd
  have hW := ΘD_latHom D v₀ hF Wd
  -- positive internal degrees
  have hpos : ∀ i : I0 D v₀ hF Wd Rw, 0 < S.P.deg (rowChar Wd Rw i.1) := by
    intro ⟨i, hi⟩
    obtain ⟨q, hq, φ, -, hφd, -, hφc, hφnz⟩ := hi
    have hφ0 : φ ≠ 0 := by
      rintro rfl; exact hφnz (RaySys.Sys.isCobdry_zero k (lenA0 D (hfinObj (c := c))) q)
    have := S.deg_eq_of_ne_zero k Θ hG hW hφ0 hφd hφc
    change 0 < S.P.deg (rowChar Wd Rw i)
    omega
  set n := Fintype.card (I0 D v₀ hF Wd Rw)
  set e : Fin n ≃ I0 D v₀ hF Wd Rw := (Fintype.equivFin _).symm
  set μF : Fin n → (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ →ₗ[k] (Alg D.F0)ᵐᵒᵖ := fun j ↦ μ (e j)
  set qd : Fin n → ℕ := fun j ↦ (S.P.deg (rowChar Wd Rw (e j).1)).toNat
  have hdeg : ∀ j, LenGrading.HasDeg₂ (lenA0 D (hfinObj (c := c))) (qd j) (μF j) := fun j ↦
    S.hasDeg₂_of_char k Θ hG hW (hpos (e j)).le (hchar (e j))
  have hχinj : ∀ a b : ι, rowChar Wd Rw a = rowChar Wd Rw b → a = b := by
    intro a b h
    have h' := congrArg (fun l : DLat ι ↦ (l : (ι → ℤ) × ℤ).1 a) h
    simp only [rowChar, rowWt_dualWt] at h'
    rw [hWd, hWd, if_pos rfl] at h'
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h'
    exact one_ne_zero h'
  have hdist : ∀ R ∈ Set.range Rw, ∀ R' ∈ Set.range Rw,
      rowWt (dualWt Wd) R = rowWt (dualWt Wd) R' → R = R' := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
    rw [hχinj a b h]
  have he0 : ∀ i, (latA0 (dualWt Wd) (hfinObj (c := c)) D).IsHom 0 ((VxA0 D v₀ hF Wd).e i) := by
    intro i
    obtain ⟨x, hx⟩ := VxA0_e D v₀ hF Wd i
    rw [hx]
    have := hW (S.P.e x)
    rwa [S.P.wt_e] at this
  have hspan := span_A0 (dualWt Wd) (hfinObj (c := c)) J h1 hS hdist (VxA0 D v₀ hF Wd) he0 μF qd
    (fun j ↦ Rw (e j).1) (fun j ↦ ⟨_, rfl⟩) (fun j ↦ hrel (e j)) (fun j ↦ hcoc (e j)) hdeg
    (fun j ↦ by have := hpos (e j); simp only [qd]; omega) (fun j ↦ hchar (e j))
    (fun j h ↦ by obtain ⟨H, -, hH⟩ := h; exact hnz (e j) ⟨H, hH⟩) (by
      rintro _ ⟨i, rfl⟩
      by_cases hi : HH2Nonzero D v₀ hF Wd Rw i
      · exact Or.inl ⟨e.symm ⟨i, hi⟩, by simp⟩
      · right
        intro q hq φ hφr hφd hφc hφχ
        by_contra hno
        exact hi ⟨q, hq, φ, hφr, hφd, hφc, hφχ, hno⟩)
  have H : LenGrading.FamilyHyp (VxA0 D v₀ hF Wd) μF qd :=
    ⟨fun j ↦ by have := hpos (e j); simp only [qd]; omega, fun j ↦ hrel (e j), hdeg,
      (fun lam a b z ↦ by
        simp only [μF, mLam_reindex D v₀ hF Wd Rw e]
        exact hassoc _ a b z), hspan⟩
  have hbasis : ∃ (κ : Type) (bL : Module.Basis κ ℤ (DLat ι)) (jj : Fin n → κ),
      Function.Injective jj ∧ ∀ j, bL (jj j) = rowChar Wd Rw (e j).1 :=
    ⟨ι ⊕ Unit, latBasis (fun i ↦ ((Rw i).2.length : ℤ) - 2), fun j ↦ Sum.inl (e j).1,
      fun j j' h ↦ e.injective (Subtype.ext (Sum.inl_injective h)),
      fun j ↦ (rowWt_dual_eq Wd hWd _).symm⟩
  obtain ⟨⟨lam, hlam, Ψ, hΨ, hΨe, -, cσ, hσ⟩, -⟩ := LenGrading.binaryNormalization
    (compat_A0 (dualWt Wd) (hfinObj (c := c))) (χ := fun j ↦ rowChar Wd Rw (e j).1)
    (fun j ↦ hchar (e j)) H he0 hbasis Pf
  set lamI : I0 D v₀ hF Wd Rw → k := fun i ↦ lam (e.symm i)
  have hlamI : ∀ i, lamI i = 0 ∨ lamI i = 1 := fun i ↦ hlam _
  have hΨ' : ∀ a b, Ψ (famMulI μ lamI a b) = Ψ a * Ψ b := by
    intro a b
    rw [← hΨ, mLam_reindex D v₀ hF Wd Rw e]
  -- the binary fibre is isomorphic to `B`
  let Φ : Fib (fibAM hrel hassoc lamI) ≃ₐ[k] B :=
    AlgEquiv.ofLinearEquiv ((Fib.toΛ (fibAM hrel hassoc lamI)).trans Ψ)
      (by
        change Ψ 1 = 1
        rw [← (VxA0 D v₀ hF Wd).complete.complete, map_sum]
        exact hΨe.complete)
      (fun a b' ↦ hΨ' _ _)
  have : FiniteDimensional k (Alg D.F0)ᵐᵒᵖ := Module.Finite.of_basis (basisR D v₀ hF)
  have : FiniteDimensional k (Fib (fibAM hrel hassoc lamI)) :=
    LinearEquiv.finiteDimensional (Fib.toΛ (fibAM hrel hassoc lamI)).symm
  obtain ⟨hnormF, F, ιF, hpresF⟩ := hfib lamI hlamI
  have hnorm : IsNormedMultiplicativeBasis ((basisR D v₀ hF).map Ψ) := by
    have e : (basisR D v₀ hF).map Ψ = ((basisR D v₀ hF).map
        (Fib.toΛ (fibAM hrel hassoc lamI)).symm).map Φ.symm.symm.toLinearEquiv :=
      Module.Basis.eq_of_apply_eq fun r ↦ rfl
    rw [e]
    exact hnormF.map_algEquiv Φ.symm
  have hpres := hpresF.map Φ (F.mapEquiv Φ) (Equiv.refl _) (fun i ↦ rfl)
  refine ⟨lamI, hlamI, Ψ, hΨ', hnorm, ⟨_, _, hpres⟩, fun r ↦ ⟨(cσ (S.P.wt r) : k), Units.ne_zero _, ?_⟩⟩
  have h := hσ _ _ _ (hG r) (hW r)
  rw [ΘD_b] at h
  exact h

end A0

end MeshWalk

end MultiplicativeBasisDeformations
