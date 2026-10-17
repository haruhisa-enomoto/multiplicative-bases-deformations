import MultiplicativeBasisDeformations.Foundations.A0Table
import MultiplicativeBasisDeformations.Foundations.RayPres

/-!
# Weight lifting for the ray table of `A₀`

Proposition 8.3(3) for `P = ray A₀` (`local-ray-geometry.tex:36–39`: "For the present
`P = ray A₀`, freeness already follows directly from Proposition 7.2"): an additive weight of
`P` modulo two factors through `W(P) ⊗ 𝔽₂`; since `W(P)` is free (`WP_free`), it lifts to an
integer additive weight (`A0Mult_lift2`).
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

variable {k : Type u} [Field k] {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} (D : MeshData (meshFam Q c) L)

variable [IsAlgClosed k] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)]
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (v₀ : V) (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

/-- A nonzero composite of deck pieces is a product of rays of `A₀`. -/
theorem A0Mult_of_comp {x y z : D.PV} {g h : Deck Q v₀} {f : D.F0 x ⟶ D.F0 y}
    {f' : D.F0 y ⟶ D.F0 z} (hf : f ∈ (D0 Q c v₀ D).part g x y) (hf' : f' ∈ (D0 Q c v₀ D).part h y z)
    (hff : f ≫ f' ≠ 0) :
    ∃ (h1 : NZ Q c v₀ D (x, y, g)) (h2 : NZ Q c v₀ D (y, z, h)) (h3 : NZ Q c v₀ D (x, z, g * h)),
      (A0Mult D v₀ hF).mul ⟨(y, z, h), h2⟩ ⟨(x, y, g), h1⟩ = some ⟨(x, z, g * h), h3⟩ := by
  obtain ⟨c1, hc1⟩ := deckV_span D v₀ hF x y g f hf
  obtain ⟨c2, hc2⟩ := deckV_span D v₀ hF y z h f' hf'
  have hb : deckV D v₀ hF x y g ≫ deckV D v₀ hF y z h ≠ 0 := by
    intro h0; apply hff
    rw [hc1, hc2, Linear.smul_comp, Linear.comp_smul, h0, smul_zero, smul_zero]
  have hf0 : f ≠ 0 := fun h0 ↦ hff (by rw [h0, Limits.zero_comp])
  have hf'0 : f' ≠ 0 := fun h0 ↦ hff (by rw [h0, Limits.comp_zero])
  have h1 : NZ Q c v₀ D (x, y, g) := fun h0 ↦ hf0 (by
    have : f ∈ (D0 Q c v₀ D).part g x y := hf
    rw [h0] at this; exact this)
  have h2 : NZ Q c v₀ D (y, z, h) := fun h0 ↦ hf'0 (by
    have : f' ∈ (D0 Q c v₀ D).part h y z := hf'
    rw [h0] at this; exact this)
  rcases deckV_mul D v₀ hF x y z g h with h0 | hgh
  · exact absurd h0 hb
  have h3 : NZ Q c v₀ D (x, z, g * h) := fun h0 ↦ hb (by
    rw [hgh]
    have := deckV_mem D v₀ hF x z (g * h)
    rw [h0] at this; exact this)
  refine ⟨h1, h2, h3, (RaySys.OfBasis.mulB_eq_some _).2 ?_⟩
  rw [basisR_apply, basisR_apply, basisR_apply, ← MulOpposite.op_mul]
  change MulOpposite.op (unitM x y (deckV D v₀ hF x y g) * unitM y z (deckV D v₀ hF y z h)) = _
  rw [unitM_mul, hgh]

open Classical in
/-- The additive weight on pieces induced by a weight of the rays. -/
def wPiece (w : RayA0 D v₀ → ZMod 2) (t : Piece Q c v₀ D) : ZMod 2 :=
  if h : NZ Q c v₀ D t then w ⟨t, h⟩ else 0

/-- **An additive weight modulo two factors through `W(P)`.** -/
def wbar (w : RayA0 D v₀ → ZMod 2)
    (hw : ∀ r s t, (A0Mult D v₀ hF).mul r s = some t → w t = w r + w s) :
    WP Q c v₀ D →+ ZMod 2 :=
  QuotientAddGroup.lift (relW Q c v₀ D)
    (Finsupp.liftAddHom fun t ↦ zmultiplesHom _ (wPiece D v₀ w t)) (by
      intro r hr
      rw [AddMonoidHom.mem_ker]
      induction hr using AddSubgroup.closure_induction with
      | mem r hr =>
        rcases hr with ⟨x, y, z, g, h, f, f', hf, hf', hff, rfl⟩ | ⟨t, ht, rfl⟩
        · obtain ⟨h1, h2, h3, hm⟩ := A0Mult_of_comp D v₀ hF hf hf' hff
          simp only [map_sub, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_smul,
            wPiece, dif_pos h1, dif_pos h2, dif_pos h3]
          rw [hw _ _ _ hm]; ring
        · simp [wPiece, dif_neg ht]
      | zero => exact map_zero _
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | neg a _ ha => rw [map_neg, ha, neg_zero])

theorem wbar_cls (w : RayA0 D v₀ → ZMod 2)
    (hw : ∀ r s t, (A0Mult D v₀ hF).mul r s = some t → w t = w r + w s) (t : RayA0 D v₀) :
    wbar D v₀ hF w hw (cls Q c v₀ D t.1) = w t := by
  simp only [wbar, cls, QuotientAddGroup.lift_mk, Finsupp.liftAddHom_apply_single,
    zmultiplesHom_apply, one_smul, wPiece]
  rw [dif_pos (show NZ Q c v₀ D t.1 from t.2)]

include hF in
/-- **Weight lifting for the ray table of a connected `A₀`** (Proposition 7.2(1)). -/
theorem A0Mult_lift2 (x₀ : D.PV) (hconn : A0Conn Q c v₀ D x₀) : (A0Mult D v₀ hF).Lift2 := by
  intro w hw
  haveI := WP_free hF hconn
  set B := Module.Free.chooseBasis ℤ (WP Q c v₀ D)
  set wb := wbar D v₀ hF w hw
  let ωb : WP Q c v₀ D →ₗ[ℤ] ℤ := B.constr ℤ fun j ↦ ((wb (B j)).val : ℤ)
  have hred : ∀ x, (ωb x : ZMod 2) = wb x := by
    have : (Int.castAddHom (ZMod 2)).toIntLinearMap.comp ωb = wb.toIntLinearMap :=
      B.ext fun j ↦ by
        simp only [LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap, ωb,
          Module.Basis.constr_basis, Int.coe_castAddHom, Int.cast_natCast, ZMod.natCast_zmod_val]
    intro x
    exact congrArg (fun φ ↦ φ x) this
  refine ⟨fun t ↦ ωb (cls Q c v₀ D t.1), fun r s t h ↦ ?_, fun t ↦ ?_⟩
  · show ωb (cls Q c v₀ D t.1) = ωb (cls Q c v₀ D r.1) + ωb (cls Q c v₀ D s.1)
    rw [cls_mul_A0 D v₀ hF h, map_add]
  · rw [hred, wbar_cls]

/-- **Connectivity of the table of `A₀` is connectivity of `A₀`.** -/
theorem A0Conn_of_conn (hc : (A0Mult D v₀ hF).Conn) (x₀ : D.PV) : A0Conn Q c v₀ D x₀ := by
  intro x
  have h := hc x₀ x
  induction h with
  | rel a b hr =>
    obtain ⟨⟨⟨y, z, g⟩, hg⟩, rfl, rfl⟩ := hr
    exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨g, hg⟩)
  | refl => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b d _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end MeshWalk

end MultiplicativeBasisDeformations
