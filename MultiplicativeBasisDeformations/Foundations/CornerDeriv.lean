import MultiplicativeBasisDeformations.Foundations.PathEval
import MultiplicativeBasisDeformations.Foundations.GModLemmas

/-!
# A first-order functor on the projective corner trivializes the deformation

`integral-deformations.tex` (proof of Lemma 10.2): "If its value is zero, arrow changes
remove all first-order mesh errors. The Hom category of the lifted modules becomes constant.
Restricting to its actual projective corner trivializes the algebra deformation."

Ring-generic form. Modules `N_X` over an `R`-algebra `Λ` carry first-order lifts of their
actions for a cocycle `μ`; the arrows `φ_a` and their corrections `g_a` satisfy the mesh
relations exactly and to first order. At projective labels `p` the module is regular,
`N_p ≅ e_pΛ` with generator `w_p` and inverse `ψ_p`, its lifted action is the regular one, and
evaluation at `w_p` identifies `RQ(p, s)` modulo the mesh ideal with `N_p e_s`. Then `μ` is a
Hochschild coboundary (`eq_hcobdry`), through the derivation `Δ(b) = ∑_p ψ_p Δ_p(w_p b)` with
`Δ_p(n) = ∑_s δ(n e_s)(w_s)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

namespace CornerDeriv

open ScalarMeshCategory GExt PathEval

variable {R : Type u} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {μ : Λ →ₗ[R] Λ →ₗ[R] Λ} {q : ℤ}
  {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (u : MeshCoefficients R Q)
  (N : V → Type v) [∀ X, AddCommGroup (N X)] [∀ X, Module R (N X)]
  (MM : ∀ X, GMod GΛ (N X)) (Lf : ∀ X, ActLift μ q (MM X))
  (φ g : ∀ {y x : V}, (y ⟶ x) → (N y →ₗ[R] N x))
  {P : Type} [Fintype P] (lab : P → V) (e : P → Λ) (w : ∀ p, N (lab p))
  (ψ : ∀ p, N (lab p) →ₗ[R] Λ)

/-- **The hypotheses of the projective corner argument.** -/
structure Hyp : Prop where
  e_idem : ∀ p, e p * e p = e p
  e_sum : ∑ p, e p = 1
  φ_act : ∀ {y x : V} (a : y ⟶ x) m b, φ a ((MM y).act m b) = (MM x).act (φ a m) b
  lift : ∀ {y x : V} (a : y ⟶ x), IsLiftHom (Lf y) (Lf x) (φ a) (g a)
  mesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1,
    ((u x a.1 a.2 : Rˣ) : R) • (φ a.2 ∘ₗ φ (Q.mate x a.1 a.2)) = 0
  zmesh : ∀ x : Q.nonprojective, ∑ a : Σ y : V, y ⟶ x.1, ((u x a.1 a.2 : Rˣ) : R) •
    (φ a.2 ∘ₗ g (Q.mate x a.1 a.2) + g a.2 ∘ₗ φ (Q.mate x a.1 a.2)) = 0
  w_e : ∀ p, (MM (lab p)).act (w p) (e p) = w p
  ψ_w : ∀ p b, ψ p ((MM (lab p)).act (w p) b) = e p * b
  w_ψ : ∀ p n, (MM (lab p)).act (w p) (ψ p n) = n
  reg : ∀ p n b, (Lf (lab p)).act n b = (MM (lab p)).act (w p) (μ (ψ p n) b)
  surj : ∀ s p (n : N (lab p)), (MM (lab p)).act n (e s) = n →
    ∃ F : LinearPaths.obj (k := R) (lab s) ⟶ LinearPaths.obj (k := R) (lab p),
      evL N φ F (w s) = n
  inj : ∀ s p (F : LinearPaths.obj (k := R) (lab s) ⟶ LinearPaths.obj (k := R) (lab p)),
    evL N φ F (w s) = 0 → F ∈ (CategoricalIdeal.HomIdeal.linearSpan R (meshRelations u)).hom
      (LinearPaths.obj (lab s)) (LinearPaths.obj (lab p))

variable {u N MM Lf φ g lab e w ψ} (H : Hyp u N MM Lf φ g lab e w ψ)
include H

theorem evP_act {Y X : V} (p : Quiver.Path Y X) (m : N Y) (b : Λ) :
    evP N φ p ((MM Y).act m b) = (MM X).act (evP N φ p m) b := by
  induction p with
  | nil => rw [evP_nil]; rfl
  | cons p a ih => rw [evP_cons, LinearMap.comp_apply, ih, H.φ_act, LinearMap.comp_apply]

theorem evL_act {Y X : V} (F : LinearPaths.obj (k := R) Y ⟶ LinearPaths.obj (k := R) X)
    (m : N Y) (b : Λ) : evL N φ F ((MM Y).act m b) = (MM X).act (evL N φ F m) b := by
  induction F using rq_induction with
  | h0 => simp
  | hadd F G hF hG => rw [map_add, LinearMap.add_apply, LinearMap.add_apply, hF, hG, map_add,
      LinearMap.add_apply]
  | hsmul t F hF => rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hF, map_smul,
      LinearMap.smul_apply]
  | hpath p => rw [evL_path, evP_act H]

theorem act_sum_e {Y : V} (m : N Y) : ∑ s, (MM Y).act m (e s) = m := by
  rw [← map_sum, H.e_sum, (MM Y).act_one]

theorem ψ_eq_e_mul (p : P) (n : N (lab p)) : e p * ψ p n = ψ p n := by
  conv_rhs => rw [← H.w_ψ p n]
  rw [H.ψ_w]

theorem ψ_act (p : P) (n : N (lab p)) (b : Λ) : ψ p ((MM (lab p)).act n b) = ψ p n * b := by
  conv_lhs => rw [← H.w_ψ p n]
  rw [(MM (lab p)).act_mul, H.ψ_w, ← mul_assoc, ψ_eq_e_mul H]

theorem act_e_idem {Y : V} (m : N Y) (s : P) :
    (MM Y).act ((MM Y).act m (e s)) (e s) = (MM Y).act m (e s) := by
  rw [(MM Y).act_mul, H.e_idem]

/-! ### The derivation on the regular modules -/

/-- A preimage of `n e_s` in `RQ(s, p)`. -/
def pre (s p : P) (n : N (lab p)) :
    LinearPaths.obj (k := R) (lab s) ⟶ LinearPaths.obj (k := R) (lab p) :=
  Classical.choose (H.surj s p ((MM (lab p)).act n (e s)) (act_e_idem H n s))

theorem evL_pre (s p : P) (n : N (lab p)) :
    evL N φ (pre H s p n) (w s) = (MM (lab p)).act n (e s) :=
  Classical.choose_spec (H.surj s p ((MM (lab p)).act n (e s)) (act_e_idem H n s))

theorem δL_eq_pre {s p : P} {n : N (lab p)}
    {F : LinearPaths.obj (k := R) (lab s) ⟶ LinearPaths.obj (k := R) (lab p)}
    (hF : evL N φ F (w s) = (MM (lab p)).act n (e s)) :
    δL N φ g F (w s) = δL N φ g (pre H s p n) (w s) := by
  have h0 : evL N φ (F - pre H s p n) (w s) = 0 := by
    rw [map_sub, LinearMap.sub_apply, hF, evL_pre, sub_self]
  have := δL_ideal H.mesh H.zmesh (H.inj s p _ h0)
  rw [map_sub, sub_eq_zero] at this
  rw [this]

/-- `Δ_p(n) = ∑_s δ(n e_s)(w_s)`. -/
def Δm (p : P) : N (lab p) →ₗ[R] N (lab p) where
  toFun n := ∑ s, δL N φ g (pre H s p n) (w s)
  map_add' n n' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← δL_eq_pre H (F := pre H s p n + pre H s p n') (by
      rw [map_add, LinearMap.add_apply, evL_pre, evL_pre, map_add, LinearMap.add_apply]),
      map_add, LinearMap.add_apply]
  map_smul' t n := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← δL_eq_pre H (F := t • pre H s p n) (by
      rw [map_smul, LinearMap.smul_apply, evL_pre, GMod.act_smul]),
      map_smul, LinearMap.smul_apply]

theorem Δm_apply (p : P) (n : N (lab p)) : Δm H p n = ∑ s, δL N φ g (pre H s p n) (w s) := rfl

/-- **`δF` is the commutator of `Δ` with `F`.** -/
theorem δL_comm {r p : P} (F : LinearPaths.obj (k := R) (lab r) ⟶ LinearPaths.obj (k := R) (lab p))
    (n : N (lab r)) : δL N φ g F n = Δm H p (evL N φ F n) - evL N φ F (Δm H r n) := by
  have hn : n = ∑ s, evL N φ (pre H s r n) (w s) := by
    conv_lhs => rw [← act_sum_e H n]
    exact Finset.sum_congr rfl fun s _ ↦ (evL_pre H s r n).symm
  have h1 : δL N φ g F n = ∑ s, δL N φ g F (evL N φ (pre H s r n) (w s)) := by
    conv_lhs => rw [hn]
    rw [map_sum]
  rw [eq_sub_iff_add_eq, Δm_apply, Δm_apply, map_sum, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← δL_eq_pre H (F := pre H s r n ≫ F) (by
      rw [evL_comp, LinearMap.comp_apply, evL_pre, evL_act H]), δL_comp]
  rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, add_comm]

theorem Δm_evL {r p : P}
    (F : LinearPaths.obj (k := R) (lab r) ⟶ LinearPaths.obj (k := R) (lab p)) (n : N (lab r)) :
    Δm H p (evL N φ F n) = δL N φ g F n + evL N φ F (Δm H r n) := by
  rw [δL_comm H F n, sub_add_cancel]

/-! ### The derivation on `Λ` -/

/-- **The derivation on `Λ`**: `Δ(b) = ∑_p ψ_p(Δ_p(w_p b))`. -/
def Δ : Λ →ₗ[R] Λ := ∑ p, ψ p ∘ₗ Δm H p ∘ₗ (MM (lab p)).act (w p)

theorem Δ_apply (b : Λ) : Δ H b = ∑ p, ψ p (Δm H p ((MM (lab p)).act (w p) b)) := by
  simp [Δ, LinearMap.sum_apply]

/-- The component `e_p x e_r` of `x` as a morphism `r → p`. -/
def Fpr (x : Λ) (p r : P) : LinearPaths.obj (k := R) (lab r) ⟶ LinearPaths.obj (k := R) (lab p) :=
  pre H r p ((MM (lab p)).act (w p) x)

theorem evL_Fpr (x : Λ) (p r : P) :
    evL N φ (Fpr H x p r) (w r) = (MM (lab p)).act (w p) (x * e r) := by
  rw [Fpr, evL_pre, (MM (lab p)).act_mul]

theorem evL_Fpr_act (x : Λ) (p r : P) (c : Λ) :
    evL N φ (Fpr H x p r) ((MM (lab r)).act (w r) c) = (MM (lab p)).act (w p) (x * e r * c) := by
  rw [evL_act H, evL_Fpr, (MM (lab p)).act_mul]

theorem ψ_evL_Fpr (x : Λ) (p r : P) (n : N (lab r)) :
    ψ p (evL N φ (Fpr H x p r) n) = e p * x * e r * ψ r n := by
  conv_lhs => rw [← H.w_ψ r n]
  rw [evL_Fpr_act, H.ψ_w, ← mul_assoc, ← mul_assoc]

theorem sum_ψ_evL_Fpr (x : Λ) (r : P) (n : N (lab r)) :
    ∑ p, ψ p (evL N φ (Fpr H x p r) n) = x * ψ r n := by
  simp only [ψ_evL_Fpr H]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, H.e_sum, one_mul, mul_assoc,
    ψ_eq_e_mul H]

theorem act_w_mul (x b : Λ) (p : P) :
    (MM (lab p)).act (w p) (x * b) = ∑ r, evL N φ (Fpr H x p r) ((MM (lab r)).act (w r) b) := by
  simp only [evL_Fpr_act H]
  rw [← map_sum]
  congr 1
  rw [← Finset.sum_mul, ← Finset.mul_sum, H.e_sum, mul_one]

theorem Δ_mul_sub (x b : Λ) :
    Δ H (x * b) - x * Δ H b =
      ∑ p, ∑ r, ψ p (δL N φ g (Fpr H x p r) ((MM (lab r)).act (w r) b)) := by
  have h1 : Δ H (x * b) = ∑ p, ∑ r, (ψ p (δL N φ g (Fpr H x p r) ((MM (lab r)).act (w r) b)) +
      ψ p (evL N φ (Fpr H x p r) (Δm H r ((MM (lab r)).act (w r) b)))) := by
    rw [Δ_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [act_w_mul H x b p, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [Δm_evL H, map_add]
  have h2 : x * Δ H b = ∑ p, ∑ r,
      ψ p (evL N φ (Fpr H x p r) (Δm H r ((MM (lab r)).act (w r) b))) := by
    rw [Δ_apply, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [sum_ψ_evL_Fpr H]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [add_sub_cancel_right]

theorem ψ_w_one (r : P) : ψ r (w r) = e r := by
  conv_lhs => rw [← (MM (lab r)).act_one (w r)]
  rw [H.ψ_w, mul_one]

/-- **The derivation identity**, the hypothesis of `GExt.eq_hcobdry_of_derivation`. -/
theorem Δ_eq (x b : Λ) :
    Δ H (x * b) - x * Δ H b - (Δ H x - x * Δ H 1) * b =
      ∑ p, e p * μ (e p * x) b - x * ∑ p, e p * μ (e p) b := by
  have h0 := Δ_mul_sub H x 1
  rw [mul_one] at h0
  rw [Δ_mul_sub H x b, h0, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [(MM _).act_one, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have key : ∀ p r, ψ p (δL N φ g (Fpr H x p r) ((MM (lab r)).act (w r) b)) -
      ψ p (δL N φ g (Fpr H x p r) (w r)) * b =
        e p * μ (e p * x * e r) b - e p * x * e r * μ (e r) b := by
    intro p r
    have hL := (δL_lift (Lf := Lf) H.lift (Fpr H x p r)).2 (w r) b
    rw [← ψ_act H, ← map_sub, hL, map_sub, H.reg, H.reg, H.ψ_w, evL_Fpr, ψ_w_one H,
      ψ_evL_Fpr H, H.ψ_w, H.ψ_w]
    congr 1
    · rw [mul_assoc (e p)]
    · rw [← mul_assoc (e p * x * e r), mul_assoc (e p * x), H.e_idem]
  simp only [key, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [← Finset.mul_sum, ← LinearMap.sum_apply, ← map_sum, ← Finset.mul_sum, H.e_sum, mul_one]
  · rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, H.e_sum, one_mul, mul_assoc]

/-- **The trivialization**: `μ` is a Hochschild coboundary. -/
theorem eq_hcobdry (hμ : IsHCocycle μ) : ∃ h : Λ →ₗ[R] Λ, μ = hcobdry h :=
  ⟨_, eq_hcobdry_of_derivation e H.e_idem H.e_sum hμ (Δ H) (Δ_eq H)⟩

end CornerDeriv

end MultiplicativeBasisDeformations
