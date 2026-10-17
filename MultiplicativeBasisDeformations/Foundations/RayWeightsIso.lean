import MultiplicativeBasisDeformations.Foundations.RayWeights

/-!
# Proposition 7.2(1): `W(P) ≅ ℤ^{n−1} ⊕ G_ab`

`weights-and-parameters.tex` (`prop:integral-ray-weights`(1)): "There is an identification
`W(P) = (I_𝓛)_G` […] the class `θ_g` of `e_{gx} − e_x` is independent of the object `x`, and
`g ↦ θ_g` identifies `G_ab` with a direct summand of `W(P)` with complement `ℤ^{n−1}`:
`W(P) ≅ ℤ^{n−1} ⊕ G_ab`."

With the deck group `G` of the base component (`Hs`, the stabilizer of the component `𝓛₀` of the
base object in the deck group of the coned complex; see `RayWeights.lean`):
* `W(P) = (I_𝓛₀)_G`: `[Σ v_o e_o] ↦ Σ v_o ζ(o)` is an isomorphism (`coinvEquiv`), with inverse
  `βW` built from `Ψ`;
* the comparison `Ψ` of `RayWeights.lean` is an isomorphism onto the vectors with coordinate sum
  zero times `G_ab` (`ΨW_ΦW`, `WPequiv`), hence `W(P) ≃ ℤ^{n−1} × G_ab` (`WPequivFree`);
* `θ_g = ζ(gx) − ζ(x)` does not depend on `x` in `𝓛₀` and is the `G_ab` summand under
  `WPequivFree` (`theta_summand`).
`W(P)` is free of finite rank (`WP_free`, `WP_finite`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type*} [Field k] [IsAlgClosed k] [Infinite k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {c : MeshCoefficients k Q} {v₀ : V}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  {x₀ : D.PV} (hconn : A0Conn Q c v₀ D x₀)
  {ζ : LObj Q c v₀ D → WP Q c v₀ D}
  (hζ : ∀ o o', Thin.Line o o' → wtL Q c v₀ D o o' = ζ o' - ζ o)

theorem grp_conj' {G : Type*} [Group G] (x y z w : G) :
    z * (x⁻¹ * (y * w⁻¹)) = (x * z⁻¹)⁻¹ * (y * w⁻¹) := by group

theorem grp_mul_inv' {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

theorem grp_g1 {G : Type*} [Group G] (g a : G) : g * 1 * a⁻¹ = g * (1 * a⁻¹) := by group

/-- The class in `H_ab` of an object of the base component: `κ(x, b) = b · a_x⁻¹`. -/
def κ (o : LObj Q c v₀ D) (ho : conn Q c v₀ D (o₀ Q c v₀ D x₀) o) :
    Additive (Abelianization (Hs Q c v₀ D x₀)) :=
  Additive.ofMul (Abelianization.of ⟨o.2 * (aL hconn o.1)⁻¹, mem_Hs hconn (x := o.1) (b := o.2) ho⟩)

theorem κ_indep (o : LObj Q c v₀ D) (ho ho' : conn Q c v₀ D (o₀ Q c v₀ D x₀) o) :
    κ hconn o ho = κ hconn o ho' := rfl

theorem nz_of_line {o o' : LObj Q c v₀ D} (h : Thin.Line o o') :
    NZ Q c v₀ D (o.1, o'.1, o.2⁻¹ * o'.2) := by
  obtain ⟨f, hf⟩ := h
  intro h0
  apply hf
  apply Subtype.ext
  have h1 : f.1 ∈ (D0 Q c v₀ D).part (o.2⁻¹ * o'.2) o.1 o'.1 := f.2
  change (D0 Q c v₀ D).part (o.2⁻¹ * o'.2) o.1 o'.1 = ⊥ at h0
  rw [h0, Submodule.mem_bot] at h1
  exact h1

include hζ in
/-- **`Ψ` on differences of object values** in the base component. -/
theorem ΨW_zeta_sub {o o' : LObj Q c v₀ D} (h : conn Q c v₀ D o o')
    (ho : conn Q c v₀ D (o₀ Q c v₀ D x₀) o) :
    ΨW hconn (ζ o' - ζ o) = (Pi.single o'.1 1 - Pi.single o.1 1,
      κ hconn o' (Relation.EqvGen.trans _ _ _ ho h) - κ hconn o ho) := by
  induction h with
  | rel a b hab =>
      rw [← hζ _ _ hab, wtL, ΨW_cls, ψgen, dif_pos (nz_of_line hab)]
      refine Prod.ext rfl ?_
      simp only [κ]
      have e : (⟨aL hconn a.1 * (a.2⁻¹ * b.2) * (aL hconn b.1)⁻¹,
          mem_Hs hconn (conn_nz hconn (nz_of_line hab))⟩ : Hs Q c v₀ D x₀) =
          (⟨a.2 * (aL hconn a.1)⁻¹, mem_Hs hconn (x := a.1) (b := a.2) ho⟩ : Hs Q c v₀ D x₀)⁻¹ *
          ⟨b.2 * (aL hconn b.1)⁻¹, mem_Hs hconn (x := b.1) (b := b.2)
            (Relation.EqvGen.trans _ _ _ ho (Relation.EqvGen.rel _ _ hab))⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
        exact grp_conj' (G := Deck Q v₀) _ _ _ _
      rw [e, map_mul, map_inv, ofMul_mul, ofMul_inv]
      abel
  | refl a =>
      rw [sub_self, map_zero, sub_self, sub_self]; rfl
  | symm a b hab ih =>
      have ha : conn Q c v₀ D (o₀ Q c v₀ D x₀) a :=
        Relation.EqvGen.trans _ _ _ ho (Relation.EqvGen.symm _ _ hab)
      have := ih ha
      rw [← neg_sub, map_neg, this]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_neg, neg_sub]
      · simp only [Prod.snd_neg, neg_sub]
  | trans a b d hab hbd ih ih' =>
      have hb : conn Q c v₀ D (o₀ Q c v₀ D x₀) b := Relation.EqvGen.trans _ _ _ ho hab
      rw [show ζ d - ζ a = (ζ d - ζ b) + (ζ b - ζ a) by abel, map_add, ih' hb, ih ho]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add]; abel
      · simp only [Prod.snd_add]; abel

theorem κ_aL (x : D.PV) : κ hconn (x, aL hconn x) (aL_spec hconn x) = 0 := by
  simp only [κ]
  have : (⟨aL hconn x * (aL hconn x)⁻¹, mem_Hs hconn (aL_spec hconn x)⟩ : Hs Q c v₀ D x₀) = 1 :=
    Subtype.ext (grp_mul_inv' (G := Deck Q v₀) _)
  rw [this, map_one, ofMul_one]

theorem conn_o₀_gL (g : Hs Q c v₀ D x₀) :
    conn Q c v₀ D (o₀ Q c v₀ D x₀) (gL Q c v₀ D g.1 (o₀ Q c v₀ D x₀)) := by
  have e : g.1 * (1 : Deck Q v₀) = g.1 := mul_one _
  have := g.2
  simp only [gL, o₀]
  rw [e]
  exact this

include hζ in
theorem ΦW_inr (g : Hs Q c v₀ D x₀) :
    ΦW hconn hζ (0, Additive.ofMul (Abelianization.of g)) =
      ζ (gL Q c v₀ D g.1 (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀) := by
  simp only [ΦW, AddMonoidHom.coprod_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
    MonoidHom.coe_toAdditiveLeft, Function.comp_apply]
  rw [toMul_ofMul, Abelianization.lift_apply_of]
  simp only [γH, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  rw [Finset.sum_eq_zero fun x _ ↦ zero_smul ℤ _, zero_add]

include hζ in
theorem ΦW_inl (v : D.PV → ℤ) :
    ΦW hconn hζ (v, 0) = ∑ x, v x • ζ (mkL Q c v₀ D x (aL hconn x)) := by
  simp only [ΦW, AddMonoidHom.coprod_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zero,
    add_zero]

include hζ in
/-- **`Ψ ∘ Φ = 1` on the vectors with coordinate sum zero.** -/
theorem ΨW_ΦW (p : Tgt Q c v₀ D x₀) (hp : ∑ x, p.1 x = 0) : ΨW hconn (ΦW hconn hζ p) = p := by
  obtain ⟨v, h⟩ := p
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul h)
  have hh : h = Additive.ofMul (Abelianization.of g) := by
    rw [show Abelianization.of g = (QuotientGroup.mk g : Abelianization (Hs Q c v₀ D x₀)) from rfl,
      hg]; rfl
  subst hh
  have hp' : ∑ x, v x = 0 := hp
  have hsplit : (v, Additive.ofMul (Abelianization.of g)) =
      ((v, 0) : Tgt Q c v₀ D x₀) + (0, Additive.ofMul (Abelianization.of g)) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_add, map_add, ΦW_inl, ΦW_inr]
  have e1 : ∑ x, v x • ζ (mkL Q c v₀ D x (aL hconn x)) =
      ∑ x, v x • (ζ (mkL Q c v₀ D x (aL hconn x)) - ζ (o₀ Q c v₀ D x₀)) := by
    have hs : ∀ x, v x • (ζ (mkL Q c v₀ D x (aL hconn x)) - ζ (o₀ Q c v₀ D x₀)) =
        v x • ζ (mkL Q c v₀ D x (aL hconn x)) - v x • ζ (o₀ Q c v₀ D x₀) := fun x ↦ by
      rw [zsmul_sub]
    rw [Finset.sum_congr rfl fun x _ ↦ hs x, Finset.sum_sub_distrib, ← Finset.sum_smul, hp',
      zero_smul, sub_zero]
  rw [e1, map_sum]
  simp only [map_zsmul]
  rw [Finset.sum_congr rfl fun x _ ↦ by
    rw [ΨW_zeta_sub hconn hζ (aL_spec hconn x) (Relation.EqvGen.refl _), κ_aL]]
  rw [ΨW_zeta_sub hconn hζ (conn_o₀_gL g) (Relation.EqvGen.refl _)]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, smul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hp', zero_smul, sub_zero]
    simp only [gL, o₀, sub_self, add_zero]
    ext y
    simp [Finset.sum_apply, Pi.single_apply]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd, zero_sub, smul_neg,
      Finset.sum_neg_distrib, ← Finset.sum_smul, hp', zero_smul, neg_zero, zero_add]
    simp only [κ]
    have key : ∀ u w : Hs Q c v₀ D x₀, u = g * w → Additive.ofMul (Abelianization.of u) -
        Additive.ofMul (Abelianization.of w) = Additive.ofMul (Abelianization.of g) := by
      rintro u w rfl; rw [map_mul, ofMul_mul, add_sub_cancel_right]
    apply key
    apply Subtype.ext
    simp only [gL, o₀, Subgroup.coe_mul]
    exact grp_g1 (G := Deck Q v₀) _ _

/-- The vectors with coordinate sum zero, times `H_ab`. -/
def SumZero : AddSubgroup (Tgt Q c v₀ D x₀) where
  carrier := {p | ∑ x, p.1 x = 0}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Prod.fst_neg, Pi.neg_apply, Finset.sum_neg_distrib] at *
    rw [ha, neg_zero]

theorem ΨW_mem (w : WP Q c v₀ D) : ΨW hconn w ∈ SumZero (Q := Q) (c := c) (v₀ := v₀) (D := D)
    (x₀ := x₀) := by
  induction w using QuotientAddGroup.induction_on with
  | H u =>
  induction u using Finsupp.induction_linear with
  | zero => simp only [QuotientAddGroup.mk_zero, map_zero]; exact zero_mem _
  | add u u' h h' => rw [QuotientAddGroup.mk_add, map_add]; exact add_mem h h'
  | single t n =>
    have hsingle : (QuotientAddGroup.mk (Finsupp.single t n) : WP Q c v₀ D) = n • cls Q c v₀ D t := by
      rw [cls, ← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, map_zsmul, ΨW_cls]
    refine zsmul_mem ?_ n
    by_cases ht : NZ Q c v₀ D t
    · simp only [ψgen, dif_pos ht]
      change ∑ x, ((Pi.single t.2.1 (1 : ℤ) - Pi.single t.1 (1 : ℤ) : D.PV → ℤ)) x = 0
      simp [Finset.sum_sub_distrib]
    · simp only [ψgen, dif_neg ht]; exact zero_mem _

include hζ in
/-- **`W(P) ≅ {v : Σ v = 0} × G_ab`** (Proposition 7.2(1)). -/
def WPequiv : WP Q c v₀ D ≃+ SumZero (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀) where
  toFun w := ⟨ΨW hconn w, ΨW_mem hconn w⟩
  invFun p := ΦW hconn hζ p.1
  left_inv w := ΦW_ΨW hconn hζ w
  right_inv p := Subtype.ext (ΨW_ΦW hconn hζ p.1 p.2)
  map_add' a b := Subtype.ext (map_add _ a b)

theorem sum_split (f : D.PV → ℤ) : ∑ x, f x = f x₀ + ∑ y : {x : D.PV // x ≠ x₀}, f y.1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (· = x₀) f]
  congr 1
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact congrArg f (default : {x : D.PV // x = x₀}).2

/-- The vectors with coordinate sum zero are `ℤ^{n−1}`: forget the base coordinate. -/
def sumZeroEquiv : SumZero (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀) ≃+
    ({x : D.PV // x ≠ x₀} → ℤ) × Additive (Abelianization (Hs Q c v₀ D x₀)) where
  toFun p := (fun x ↦ p.1.1 x.1, p.1.2)
  invFun u := ⟨(fun x ↦ if hx : x = x₀ then -∑ y : {x : D.PV // x ≠ x₀}, u.1 y else u.1 ⟨x, hx⟩,
    u.2), by
      change ∑ x, (if hx : x = x₀ then -∑ y : {x : D.PV // x ≠ x₀}, u.1 y else u.1 ⟨x, hx⟩) = 0
      rw [sum_split (x₀ := x₀), dif_pos rfl]
      have hs : ∀ y : {x : D.PV // x ≠ x₀},
          (if h : y.1 = x₀ then -∑ y : {x : D.PV // x ≠ x₀}, u.1 y else u.1 ⟨y.1, h⟩) = u.1 y :=
        fun y ↦ by rw [dif_neg y.2]
      simp only [hs, neg_add_cancel]⟩
  left_inv p := by
    obtain ⟨⟨v, h⟩, hp⟩ := p
    apply Subtype.ext
    refine Prod.ext (funext fun x ↦ ?_) rfl
    by_cases hx : x = x₀
    · subst hx
      simp only []
      have hp' : ∑ x, v x = 0 := hp
      rw [sum_split (x₀ := x)] at hp'
      exact (eq_neg_of_add_eq_zero_left hp').symm
    · simp only [dif_neg hx]
  right_inv u := by
    refine Prod.ext (funext fun x ↦ ?_) rfl
    simp only [dif_neg x.2]
  map_add' a b := rfl

include hζ in
/-- **Proposition 7.2(1)**: `W(P) ≅ ℤ^{n−1} ⊕ G_ab`, with `G` the (free) deck group of the base
component and `n` the number of labels. -/
def WPequivFree : WP Q c v₀ D ≃+
    ({x : D.PV // x ≠ x₀} → ℤ) × Additive (Abelianization (Hs Q c v₀ D x₀)) :=
  (WPequiv hconn hζ).trans (sumZeroEquiv hconn)

include hζ in
/-- **`θ_g = ζ(gx) − ζ(x)` for every `x` of the base component**, and under `WPequivFree` it is the
`G_ab` summand: `g ↦ θ_g` identifies `G_ab` with a direct summand with complement `ℤ^{n−1}`. -/
theorem theta_summand (g : Hs Q c v₀ D x₀) (o : LObj Q c v₀ D)
    (ho : conn Q c v₀ D (o₀ Q c v₀ D x₀) o) :
    WPequivFree hconn hζ (ζ (gL Q c v₀ D g.1 o) - ζ o) =
      (0, Additive.ofMul (Abelianization.of g)) := by
  have hgo : conn Q c v₀ D o (gL Q c v₀ D g.1 o) := by
    have h1 := conn_gL g.1 ho
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ ho)
      (Relation.EqvGen.trans _ _ _ (conn_o₀_gL g) h1)
  have hΨ := ΨW_zeta_sub hconn hζ hgo ho
  refine Prod.ext (funext fun x ↦ ?_) ?_
  · change (ΨW hconn (ζ (gL Q c v₀ D g.1 o) - ζ o)).1 x.1 = 0
    rw [hΨ]; simp [gL]
  · change (ΨW hconn (ζ (gL Q c v₀ D g.1 o) - ζ o)).2 = _
    rw [hΨ]
    simp only [κ]
    have key : ∀ u w : Hs Q c v₀ D x₀, u = g * w → Additive.ofMul (Abelianization.of u) -
        Additive.ofMul (Abelianization.of w) = Additive.ofMul (Abelianization.of g) := by
      rintro u w rfl; rw [map_mul, ofMul_mul, add_sub_cancel_right]
    apply key
    apply Subtype.ext
    simp only [gL, Subgroup.coe_mul, mul_assoc]

/-! ### The identification `W(P) = (I_𝓛)_G` -/

section Coinvariants

variable (Q c v₀ D x₀) in
/-- The base component `𝓛₀` of the lifted projective category. -/
abbrev L0 := {o : LObj Q c v₀ D // conn Q c v₀ D (o₀ Q c v₀ D x₀) o}

/-- The deck action of `G = H` on `𝓛₀`. -/
def actL0 (g : Hs Q c v₀ D x₀) (o : L0 Q c v₀ D x₀) : L0 Q c v₀ D x₀ :=
  ⟨gL Q c v₀ D g.1 o.1, Relation.EqvGen.trans _ _ _ (conn_o₀_gL g) (conn_gL g.1 o.2)⟩

variable (Q c v₀ D x₀) in
/-- The sum of coefficients. -/
def coefSum : (L0 Q c v₀ D x₀ →₀ ℤ) →+ ℤ := Finsupp.liftAddHom fun _ ↦ AddMonoidHom.id ℤ

variable (Q c v₀ D x₀) in
/-- **`I_𝓛`**: finite sums with coefficient sum zero. -/
abbrev IL := (coefSum Q c v₀ D x₀).ker

/-- The deck action on finite sums. -/
def actF (g : Hs Q c v₀ D x₀) : (L0 Q c v₀ D x₀ →₀ ℤ) →+ (L0 Q c v₀ D x₀ →₀ ℤ) :=
  Finsupp.mapDomain.addMonoidHom (actL0 g)

theorem coefSum_actF (g : Hs Q c v₀ D x₀) (v : L0 Q c v₀ D x₀ →₀ ℤ) :
    coefSum Q c v₀ D x₀ (actF g v) = coefSum Q c v₀ D x₀ v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => rw [map_add, map_add, hu, hw, map_add]
  | single o n => simp [actF, coefSum]

variable (Q c v₀ D x₀) in
/-- The relations `g·v − v` of the coinvariants. -/
def relG : AddSubgroup (IL Q c v₀ D x₀) :=
  AddSubgroup.closure {u | ∃ (g : Hs Q c v₀ D x₀) (v : IL Q c v₀ D x₀), (u : L0 Q c v₀ D x₀ →₀ ℤ) =
    actF g v - v}

variable (Q c v₀ D x₀) in
/-- **The coinvariants `(I_𝓛)_G`.** -/
abbrev Coinv := IL Q c v₀ D x₀ ⧸ relG Q c v₀ D x₀

/-- The values of `ζ` on finite sums. -/
def αF : (L0 Q c v₀ D x₀ →₀ ℤ) →+ WP Q c v₀ D :=
  Finsupp.liftAddHom fun o ↦ zmultiplesHom _ (ζ o.1)

include hconn hζ in
/-- `ζ(g o) − ζ(o)` does not depend on `o` in the base component. -/
theorem zeta_act_sub (g : Hs Q c v₀ D x₀) (o : L0 Q c v₀ D x₀) :
    ζ (actL0 g o).1 - ζ o.1 = ζ (gL Q c v₀ D g.1 (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀) := by
  have := zeta_shift hζ g.1 o.2
  calc ζ (actL0 g o).1 - ζ o.1
      = (ζ (gL Q c v₀ D g.1 o.1) - ζ (gL Q c v₀ D g.1 (o₀ Q c v₀ D x₀))) +
        (ζ (gL Q c v₀ D g.1 (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀)) -
        (ζ o.1 - ζ (o₀ Q c v₀ D x₀)) := by simp only [actL0]; abel
    _ = _ := by rw [this, add_sub_cancel_left]

include hconn hζ in
theorem αF_actF (g : Hs Q c v₀ D x₀) (v : L0 Q c v₀ D x₀ →₀ ℤ) :
    αF (ζ := ζ) (actF g v) = αF (ζ := ζ) v + coefSum Q c v₀ D x₀ v •
      (ζ (gL Q c v₀ D g.1 (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀)) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => rw [map_add, map_add, hu, hw, map_add, map_add, add_zsmul]; abel
  | single o n =>
      simp only [actF, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single, αF,
        Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, coefSum, AddMonoidHom.id_apply]
      rw [← zeta_act_sub hconn hζ g o, zsmul_sub, add_sub_cancel]

/-- **The comparison** `(I_𝓛)_G → W(P)`, `[Σ v_o e_o] ↦ Σ v_o ζ(o)`. -/
def αbar : Coinv Q c v₀ D x₀ →+ WP Q c v₀ D :=
  QuotientAddGroup.lift (relG Q c v₀ D x₀) ((αF (ζ := ζ)).comp (IL Q c v₀ D x₀).subtype) (by
    intro u hu
    rw [AddMonoidHom.mem_ker]
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
        obtain ⟨g, v, hv⟩ := hu
        rw [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, hv, map_sub, αF_actF hconn hζ,
          AddMonoidHom.mem_ker.1 v.2, zero_zsmul, add_zero, sub_self]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | neg a _ ha => rw [map_neg, ha, neg_zero])

theorem αbar_mk (v : IL Q c v₀ D x₀) :
    αbar hconn hζ (QuotientAddGroup.mk v) = αF (ζ := ζ) v.1 := rfl

/-- The base point of `𝓛₀`. -/
def b0 : L0 Q c v₀ D x₀ := ⟨o₀ Q c v₀ D x₀, Relation.EqvGen.refl _⟩

/-- The chosen lift of a label in `𝓛₀`. -/
def bL (x : D.PV) : L0 Q c v₀ D x₀ := ⟨mkL Q c v₀ D x (aL hconn x), aL_spec hconn x⟩

/-- The generator `e_o − e_{o₀}` of `I_𝓛`. -/
def gen (o : L0 Q c v₀ D x₀) : IL Q c v₀ D x₀ :=
  ⟨Finsupp.single o 1 - Finsupp.single b0 1, by
    rw [AddMonoidHom.mem_ker, map_sub]
    simp only [coefSum, Finsupp.liftAddHom_apply_single, AddMonoidHom.id_apply, sub_self]⟩

/-- The class `τ(g) = [e_{g o₀} − e_{o₀}]`. -/
def τgen (g : Hs Q c v₀ D x₀) : Coinv Q c v₀ D x₀ :=
  QuotientAddGroup.mk (gen (actL0 g b0))

theorem actL0_mul (g h : Hs Q c v₀ D x₀) (o : L0 Q c v₀ D x₀) :
    actL0 (g * h) o = actL0 g (actL0 h o) := Subtype.ext (gL_mul g.1 h.1 o.1)

theorem mk_actF (g : Hs Q c v₀ D x₀) (v : IL Q c v₀ D x₀) (hv : actF g v.1 ∈ IL Q c v₀ D x₀) :
    (QuotientAddGroup.mk (⟨actF g v.1, hv⟩ : IL Q c v₀ D x₀) : Coinv Q c v₀ D x₀) =
      QuotientAddGroup.mk v := by
  rw [QuotientAddGroup.eq]
  have hmem : (⟨actF g v.1 - v.1, sub_mem hv v.2⟩ : IL Q c v₀ D x₀) ∈ relG Q c v₀ D x₀ :=
    AddSubgroup.subset_closure ⟨g, v, rfl⟩
  convert neg_mem hmem using 1
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_sub]
  abel

/-- **`[e_{g b} − e_{o₀}] = [e_b − e_{o₀}] + τ(g)`.** -/
theorem mk_gen_act (g : Hs Q c v₀ D x₀) (o : L0 Q c v₀ D x₀) :
    (QuotientAddGroup.mk (gen (actL0 g o)) : Coinv Q c v₀ D x₀) =
      QuotientAddGroup.mk (gen o) + τgen g := by
  have hsplit : gen (actL0 g o) = ⟨actF g (gen o).1, by
      rw [AddMonoidHom.mem_ker, coefSum_actF]; exact AddMonoidHom.mem_ker.1 (gen o).2⟩ +
        gen (actL0 g b0) := by
    apply Subtype.ext
    simp only [gen, actF, AddSubgroup.coe_add, map_sub, Finsupp.mapDomain.addMonoidHom_apply,
      Finsupp.mapDomain_single]
    abel
  rw [hsplit, QuotientAddGroup.mk_add, mk_actF]
  rfl

/-- `τ` is a homomorphism. -/
def τhom : Hs Q c v₀ D x₀ →* Multiplicative (Coinv Q c v₀ D x₀) where
  toFun g := Multiplicative.ofAdd (τgen g)
  map_one' := by
    have : actL0 (1 : Hs Q c v₀ D x₀) b0 = b0 := Subtype.ext (by
      simp only [actL0, b0, gL, OneMemClass.coe_one, o₀]; rw [one_mul])
    simp only [τgen, this, gen, sub_self]
    rfl
  map_mul' g h := by
    rw [← ofAdd_add]
    congr 1
    simp only [τgen]
    rw [actL0_mul, mk_gen_act, add_comm]
    rfl

/-- The map `ℤ^{labels} × G_ab → (I_𝓛)_G`. -/
def γW : Tgt Q c v₀ D x₀ →+ Coinv Q c v₀ D x₀ :=
  AddMonoidHom.coprod
    { toFun := fun n ↦ ∑ x, n x • (QuotientAddGroup.mk (gen (bL hconn x)) : Coinv Q c v₀ D x₀)
      map_zero' := by simp
      map_add' := fun n n' ↦ by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib] }
    (MonoidHom.toAdditiveLeft (Abelianization.lift τhom))

/-- **The inverse comparison** `W(P) → (I_𝓛)_G`. -/
def βW : WP Q c v₀ D →+ Coinv Q c v₀ D x₀ := (γW hconn).comp (ΨW hconn)

/-- The class `κ'(o) = o.2 · a_{o.1}⁻¹ ∈ G` of an object of `𝓛₀`. -/
def κ' (o : L0 Q c v₀ D x₀) : Hs Q c v₀ D x₀ :=
  ⟨o.1.2 * (aL hconn o.1.1)⁻¹, mem_Hs hconn (x := o.1.1) (b := o.1.2) o.2⟩

theorem grp_cancel' {G : Type*} [Group G] (a b : G) : a * b⁻¹ * b = a := by group

theorem actL0_κ' (o : L0 Q c v₀ D x₀) : actL0 (κ' hconn o) (bL hconn o.1.1) = o := by
  apply Subtype.ext
  change ((o.1.1, o.1.2 * (aL hconn o.1.1)⁻¹ * aL hconn o.1.1) : D.PV × Deck Q v₀) = o.1
  rw [grp_cancel' (G := Deck Q v₀)]
  rfl

theorem mk_gen_eq (o : L0 Q c v₀ D x₀) :
    (QuotientAddGroup.mk (gen o) : Coinv Q c v₀ D x₀) =
      QuotientAddGroup.mk (gen (bL hconn o.1.1)) + τgen (κ' hconn o) := by
  conv_lhs => rw [← actL0_κ' hconn o]
  exact mk_gen_act _ _

theorem gen_b0 : gen (b0 (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀)) = 0 :=
  Subtype.ext (by simp [gen])

theorem βW_gen (o : L0 Q c v₀ D x₀) :
    βW hconn (αbar hconn hζ (QuotientAddGroup.mk (gen o))) = QuotientAddGroup.mk (gen o) := by
  have hα : αbar hconn hζ (QuotientAddGroup.mk (gen o)) = ζ o.1 - ζ (o₀ Q c v₀ D x₀) := by
    rw [αbar_mk]
    simp only [gen, αF, b0, map_sub, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
  rw [hα]
  simp only [βW, γW, AddMonoidHom.comp_apply]
  rw [ΨW_zeta_sub hconn hζ o.2 (Relation.EqvGen.refl _)]
  simp only [AddMonoidHom.coprod_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    MonoidHom.coe_toAdditiveLeft, Function.comp_apply, map_sub]
  -- the label part
  rw [Finset.sum_eq_single o.1.1 (fun y _ hy ↦ by simp [hy])
      (fun h ↦ absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single (o₀ Q c v₀ D x₀).1 (fun y _ hy ↦ by simp [hy])
      (fun h ↦ absurd (Finset.mem_univ _) h)]
  simp only [Pi.single_eq_same, one_zsmul]
  -- the deck part
  have hκ : ∀ (o' : L0 Q c v₀ D x₀), Multiplicative.toAdd ((Abelianization.lift
      (τhom (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀)))
      (Additive.toMul (κ hconn o'.1 o'.2))) = τgen (κ' hconn o') := fun o' ↦ by
    simp only [κ, toMul_ofMul, Abelianization.lift_apply_of]
    rfl
  have h0 := hκ b0
  have h1 := hκ o
  have hb0 : (0 : Coinv Q c v₀ D x₀) = QuotientAddGroup.mk (gen (bL hconn x₀)) +
      τgen (κ' hconn b0) := by
    have := mk_gen_eq hconn (b0 (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀))
    rw [gen_b0] at this
    exact this
  change _ + (Multiplicative.toAdd ((Abelianization.lift
      (τhom (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀))) (Additive.toMul (κ hconn o.1 o.2))) -
    Multiplicative.toAdd ((Abelianization.lift (τhom (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀)))
      (Additive.toMul (κ hconn (b0 (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀)).1
        (b0 (Q := Q) (c := c) (v₀ := v₀) (D := D) (x₀ := x₀)).2)))) = _
  rw [h1, h0, mk_gen_eq hconn o]
  rw [eq_neg_of_add_eq_zero_right hb0.symm]
  simp only [o₀]
  abel

theorem mk_eq_sum (v : IL Q c v₀ D x₀) :
    (QuotientAddGroup.mk v : Coinv Q c v₀ D x₀) =
      ∑ o ∈ v.1.support, v.1 o • (QuotientAddGroup.mk (gen o) : Coinv Q c v₀ D x₀) := by
  have hc : ∑ i ∈ v.1.support, v.1 i = 0 := by
    have := AddMonoidHom.mem_ker.1 v.2
    simpa [coefSum, Finsupp.liftAddHom_apply, Finsupp.sum] using this
  have hv : v = ∑ o ∈ v.1.support, v.1 o • gen o := by
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    simp only [AddSubgroup.coe_zsmul, gen, zsmul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hc, zero_smul, sub_zero]
    conv_lhs => rw [← Finsupp.sum_single v.1]
    simp [Finsupp.sum, Finsupp.smul_single]
  conv_lhs => rw [hv]
  simp only [QuotientAddGroup.mk_sum, QuotientAddGroup.mk_zsmul]

include hζ in
theorem βW_αbar (q : Coinv Q c v₀ D x₀) : βW hconn (αbar hconn hζ q) = q := by
  induction q using QuotientAddGroup.induction_on with
  | H v =>
    rw [mk_eq_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun o _ ↦ by rw [map_zsmul, map_zsmul, βW_gen]

include hζ in
theorem αbar_γW (p : Tgt Q c v₀ D x₀) (hp : ∑ x, p.1 x = 0) :
    αbar hconn hζ (γW hconn p) = ΦW hconn hζ p := by
  obtain ⟨n, h⟩ := p
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul h)
  have hh : h = Additive.ofMul (Abelianization.of g) := by
    rw [show Abelianization.of g = (QuotientGroup.mk g : Abelianization (Hs Q c v₀ D x₀)) from rfl,
      hg]; rfl
  subst hh
  have hn : ∑ x, n x = 0 := hp
  have hsplit : (n, Additive.ofMul (Abelianization.of g)) =
      ((n, 0) : Tgt Q c v₀ D x₀) + (0, Additive.ofMul (Abelianization.of g)) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, map_add, map_add, map_add, ΦW_inl, ΦW_inr]
  congr 1
  · simp only [γW, AddMonoidHom.coprod_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_zero,
      add_zero, map_sum, map_zsmul, αbar_mk]
    have hs : ∀ x, n x • αF (ζ := ζ) (gen (bL hconn x)).1 =
        n x • ζ (mkL Q c v₀ D x (aL hconn x)) - n x • ζ (o₀ Q c v₀ D x₀) := fun x ↦ by
      simp only [gen, αF, b0, bL, map_sub, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply,
        one_zsmul, zsmul_sub]
    rw [Finset.sum_congr rfl fun x _ ↦ hs x, Finset.sum_sub_distrib, ← Finset.sum_smul, hn,
      zero_smul, sub_zero]
  · simp only [γW, AddMonoidHom.coprod_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply,
      MonoidHom.coe_toAdditiveLeft,
      Function.comp_apply, toMul_ofMul, Abelianization.lift_apply_of]
    rw [Finset.sum_eq_zero fun x _ ↦ zero_zsmul _, zero_add]
    change αbar hconn hζ (τgen g) = _
    simp only [τgen, αbar_mk, gen, αF, b0, actL0, map_sub, Finsupp.liftAddHom_apply_single,
      zmultiplesHom_apply, one_zsmul]

include hζ in
theorem αbar_βW (w : WP Q c v₀ D) : αbar hconn hζ (βW hconn w) = w := by
  rw [βW, AddMonoidHom.comp_apply, αbar_γW hconn hζ _ (ΨW_mem hconn w), ΦW_ΨW]

include hζ in
/-- **The identification `W(P) = (I_𝓛)_G`** (Proposition 7.2(1)): `[Σ v_o e_o] ↦ Σ v_o ζ(o)`,
for the base component `𝓛₀` and its deck group `G`. -/
def coinvEquiv : Coinv Q c v₀ D x₀ ≃+ WP Q c v₀ D where
  toFun := αbar hconn hζ
  invFun := βW hconn
  left_inv := βW_αbar hconn hζ
  right_inv := αbar_βW hconn hζ
  map_add' := map_add _

include hζ in
/-- **The identification on rays** (Proposition 7.2(1)): the class of
`e_{o'} − e_o = (e_{o'} − e_{o₀}) − (e_o − e_{o₀})` for a lifted ray `o → o'` corresponds to the
weight class of that ray. -/
theorem coinvEquiv_line (o o' : L0 Q c v₀ D x₀) (h : Thin.Line o.1 o'.1) :
    coinvEquiv hconn hζ (QuotientAddGroup.mk (gen o') - QuotientAddGroup.mk (gen o)) =
      wtL Q c v₀ D o.1 o'.1 := by
  have hg : ∀ p : L0 Q c v₀ D x₀, coinvEquiv hconn hζ (QuotientAddGroup.mk (gen p)) =
      ζ p.1 - ζ (o₀ Q c v₀ D x₀) := fun p ↦ by
    rw [show coinvEquiv hconn hζ (QuotientAddGroup.mk (gen p)) =
      αbar hconn hζ (QuotientAddGroup.mk (gen p)) from rfl, αbar_mk]
    simp only [gen, b0, αF, map_sub, Finsupp.liftAddHom_apply_single,
      zmultiplesHom_apply, one_zsmul]
  rw [map_sub, hg, hg, hζ _ _ h]
  abel

include hζ in
/-- The inverse direction of `coinvEquiv_line`: a lifted ray `r : o → o'` goes to `[e_{o'} − e_o]`. -/
theorem coinvEquiv_symm_line (o o' : L0 Q c v₀ D x₀) (h : Thin.Line o.1 o'.1) :
    (coinvEquiv hconn hζ).symm (wtL Q c v₀ D o.1 o'.1) =
      QuotientAddGroup.mk (gen o') - QuotientAddGroup.mk (gen o) := by
  rw [← coinvEquiv_line hconn hζ o o' h, AddEquiv.symm_apply_apply]

end Coinvariants

end MeshWalk

end MultiplicativeBasisDeformations
