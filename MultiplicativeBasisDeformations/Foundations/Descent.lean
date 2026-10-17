import MultiplicativeBasisDeformations.Foundations.CoverCategory
import MultiplicativeBasisDeformations.Foundations.WeightDivisibility

/-!
# Proposition 4.14: descent of a multiplicative basis along a free deck group

`prop:scalar-normalization` (`scalar-normalization.tex`): "Let `b_{xy}`
be the multiplicative basis constructed on `L`. For a free deck generator `g`,
write `g(b_{xy}) = d_g(x, y) b_{gx,gy}`. The coefficients form a multiplicative
weight. By Lemma 4.13, write `d_g(x, y) = a_g(y)/a_g(x)`. On each orbit of
objects solve `f(gx) = a_g(x) f(x)` for all free generators. The orbit graph is a
Cayley tree, so a value at one root determines consistent values everywhere.
Then `b'_{xy} = (f(y)/f(x)) b_{xy}` is still multiplicative and is deck
invariant."

For a graded family with a thin cover, a multiplicative basis `β` on the cover,
a free grading group, and Lemma 4.13 as a hypothesis (`hratio`), we build the
deck-invariant multiplicative basis `b'` (`invBasis`). The deck group acts on
the cover by translating sheets (`tr`), with the same morphisms (`trHom`). The
values `f` are the transport of `(root, 1)` under the homomorphism from the free
group to permutations of `objects × kˣ` lifting the generators (`Ψ`): this is
"a value at one root determines consistent values everywhere".
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

namespace CatAlg

variable {k : Type u} [Field k] {𝒞 : Type v} [Category.{u} 𝒞] [Preadditive 𝒞] [Linear k 𝒞]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : ι → 𝒞} {G : Type} [Group G] [DecidableEq G]
  {D : HomGrading (k := k) F G}

/-! ### Deck translations of the cover -/

/-- Translation of the sheet by `g`. -/
def tr (g : G) (o : CovObj D) : CovObj D := (show ι × G from o).map id (g * ·)

@[simp] theorem tr_fst (g : G) (o : CovObj D) : (tr g o).1 = o.1 := rfl
@[simp] theorem tr_snd (g : G) (o : CovObj D) : (tr g o).2 = g * o.2 := rfl

theorem tr_mul (g h : G) (o : CovObj D) : tr (g * h) o = tr g (tr h o) :=
  Prod.ext rfl (mul_assoc _ _ _)

theorem tr_one (o : CovObj D) : tr 1 o = o := Prod.ext rfl (one_mul _)

theorem tr_inv_tr (g : G) (o : CovObj D) : tr g⁻¹ (tr g o) = o :=
  Prod.ext rfl (inv_mul_cancel_left _ _)

theorem tr_tr_inv (g : G) (o : CovObj D) : tr g (tr g⁻¹ o) = o :=
  Prod.ext rfl (mul_inv_cancel_left _ _)

theorem tr_part (g : G) (o o' : CovObj D) :
    CovHom (tr g o) (tr g o') = CovHom o o' := by
  change D.part ((g * o.2)⁻¹ * (g * o'.2)) o.1 o'.1 = D.part (o.2⁻¹ * o'.2) o.1 o'.1
  rw [show (g * o.2)⁻¹ * (g * o'.2) = o.2⁻¹ * o'.2 by group]

/-- The translated morphism (the same morphism of the family). -/
def trHom (g : G) {o o' : CovObj D} (f : o ⟶ o') : tr g o ⟶ tr g o' :=
  ⟨f.1, by rw [tr_part]; exact f.2⟩

@[simp] theorem trHom_val (g : G) {o o' : CovObj D} (f : o ⟶ o') : (trHom g f).1 = f.1 := rfl

theorem trHom_comp (g : G) {o o' o'' : CovObj D} (f : o ⟶ o') (f' : o' ⟶ o'') :
    trHom g (f ≫ f') = trHom g f ≫ trHom g f' := rfl

theorem trHom_smul (g : G) {o o' : CovObj D} (c : k) (f : o ⟶ o') :
    trHom g (c • f) = c • trHom g f := rfl

theorem trHom_ne_zero (g : G) {o o' : CovObj D} {f : o ⟶ o'} (hf : f ≠ 0) : trHom g f ≠ 0 :=
  fun h ↦ hf (Subtype.ext (show f.1 = 0 from congrArg Subtype.val h))

/-- Morphisms back from the translated objects. -/
def untrHom (g : G) {o o' : CovObj D} (f : tr g o ⟶ tr g o') : o ⟶ o' :=
  ⟨f.1, by rw [← tr_part g]; exact f.2⟩

/-! ### The weights `d_g` -/

variable (hT : Thin.IsThin k (CovObj D)) {β : ∀ o o' : CovObj D, o ⟶ o'}
  (hβ : Thin.MultBasis Set.univ β)

include hβ in
theorem β_ne_zero_iff {o o' : CovObj D} : β o o' ≠ 0 ↔ ∃ f : o ⟶ o', f ≠ 0 :=
  ⟨fun h ↦ ⟨_, h⟩, fun ⟨f, hf⟩ ↦ hβ.ne_zero o trivial o' trivial f hf⟩

variable (β) in
/-- **The coefficients of a deck translation**: `g(b_{xy}) = d_g(x, y) b_{gx,gy}`. -/
def dg (g : G) (o o' : CovObj D) : k := Thin.coef hT (β (tr g o) (tr g o')) (trHom g (β o o'))

include hβ in
theorem dg_spec (g : G) {o o' : CovObj D} (h : β o o' ≠ 0) :
    trHom g (β o o') = dg hT β g o o' • β (tr g o) (tr g o') := by
  have hne : β (tr g o) (tr g o') ≠ 0 :=
    (β_ne_zero_iff hβ).2 ⟨_, trHom_ne_zero g h⟩
  exact Thin.coef_spec hT hne _

include hβ in
/-- **The coefficients form a multiplicative weight.** -/
theorem dg_isWeight (g : G) : Thin.IsWeight Set.univ (dg hT β g) := by
  refine ⟨fun o _ o' _ f hf ↦ ?_, fun o _ o' _ o'' _ f f' hff' ↦ ?_⟩
  · have h := hβ.ne_zero o trivial o' trivial f hf
    intro h0
    apply trHom_ne_zero g h
    rw [dg_spec hT hβ g h, h0, zero_smul]
  · have hf : f ≠ 0 := fun h ↦ hff' (by rw [h, Limits.zero_comp])
    have hf' : f' ≠ 0 := fun h ↦ hff' (by rw [h, Limits.comp_zero])
    have h1 := hβ.ne_zero o trivial o' trivial f hf
    have h2 := hβ.ne_zero o' trivial o'' trivial f' hf'
    -- the basis composite is nonzero
    have hbb : β o o' ≫ β o' o'' ≠ 0 := by
      obtain ⟨c, rfl⟩ := Thin.exists_smul hT h1 f
      obtain ⟨c', rfl⟩ := Thin.exists_smul hT h2 f'
      intro h
      apply hff'
      rw [Linear.smul_comp, Linear.comp_smul, h, smul_zero, smul_zero]
    have hb := hβ.comp_eq hT trivial trivial trivial hbb
    have h3 : β o o'' ≠ 0 := hb ▸ hbb
    have e := dg_spec hT hβ g h3
    rw [← hb, trHom_comp, dg_spec hT hβ g h1, dg_spec hT hβ g h2, Linear.smul_comp,
      Linear.comp_smul, smul_smul] at e
    have hne : β (tr g o) (tr g o') ≫ β (tr g o') (tr g o'') ≠ 0 := by
      intro h0
      apply trHom_ne_zero g h3
      rw [← hb, trHom_comp, dg_spec hT hβ g h1, dg_spec hT hβ g h2, Linear.smul_comp,
        Linear.comp_smul, h0, smul_zero, smul_zero]
    rw [hβ.comp_eq hT trivial trivial trivial hne] at e
    have hne3 : β (tr g o) (tr g o'') ≠ 0 := (β_ne_zero_iff hβ).2 ⟨_, trHom_ne_zero g h3⟩
    exact smul_left_injective k hne3 e.symm

/-! ### Object values on the orbits -/

variable [IsFreeGroup G]
  (hratio : ∀ d : CovObj D → CovObj D → k, Thin.IsWeight Set.univ d →
    ∃ ζ : CovObj D → k, (∀ o, ζ o ≠ 0) ∧
      ∀ (o o' : CovObj D) (f : o ⟶ o'), f ≠ 0 → d o o' = ζ o' / ζ o)

include hβ hratio in
/-- Lemma 4.13 applied to `d_g`: `d_g(x, y) = a_g(y)/a_g(x)`. -/
theorem exists_aG (g : G) : ∃ a : CovObj D → k, (∀ o, a o ≠ 0) ∧
    ∀ (o o' : CovObj D) (f : o ⟶ o'), f ≠ 0 → dg hT β g o o' = a o' / a o :=
  hratio _ (dg_isWeight hT hβ g)

/-- The values `a_g`. -/
def aG (g : G) (o : CovObj D) : kˣ :=
  Units.mk0 (Classical.choose (exists_aG hT hβ hratio g) o)
    ((Classical.choose_spec (exists_aG hT hβ hratio g)).1 o)

theorem aG_spec (g : G) {o o' : CovObj D} (h : β o o' ≠ 0) :
    dg hT β g o o' = (aG hT hβ hratio g o' : k) / aG hT hβ hratio g o :=
  (Classical.choose_spec (exists_aG hT hβ hratio g)).2 o o' _ h

/-- The permutation of `objects × kˣ` lifting a free generator:
`(o, λ) ↦ (g o, a_g(o) λ)`. -/
def πs (a : IsFreeGroup.Generators G) : Equiv.Perm (CovObj D × kˣ) where
  toFun p := (tr (IsFreeGroup.of a) p.1, aG hT hβ hratio (IsFreeGroup.of a) p.1 * p.2)
  invFun p := (tr (IsFreeGroup.of a)⁻¹ p.1,
    (aG hT hβ hratio (IsFreeGroup.of a) (tr (IsFreeGroup.of a)⁻¹ p.1))⁻¹ * p.2)
  left_inv p := Prod.ext (tr_inv_tr _ _) (by simp only [tr_inv_tr, inv_mul_cancel_left])
  right_inv p := Prod.ext (tr_tr_inv _ _) (by simp only [mul_inv_cancel_left])

/-- **The lift to the free group**. -/
def Ψd : G →* Equiv.Perm (CovObj D × kˣ) := IsFreeGroup.lift (πs hT hβ hratio)

/-- The transports have the form `(o, λ) ↦ (g o, c(o) λ)`. -/
def HasForm (σ : Equiv.Perm (CovObj D × kˣ)) (g : G) : Prop :=
  ∃ c : CovObj D → kˣ, ∀ p, σ p = (tr g p.1, c p.1 * p.2)

theorem hasForm_mul {σ τ : Equiv.Perm (CovObj D × kˣ)} {g h : G} (hσ : HasForm σ g)
    (hτ : HasForm τ h) : HasForm (σ * τ) (g * h) := by
  obtain ⟨c, hc⟩ := hσ
  obtain ⟨c', hc'⟩ := hτ
  refine ⟨fun o ↦ c (tr h o) * c' o, fun p ↦ ?_⟩
  rw [Equiv.Perm.mul_apply, hc', hc, tr_mul, mul_assoc]

theorem hasForm_inv {σ : Equiv.Perm (CovObj D × kˣ)} {g : G} (hσ : HasForm σ g) :
    HasForm σ⁻¹ g⁻¹ := by
  obtain ⟨c, hc⟩ := hσ
  refine ⟨fun o ↦ (c (tr g⁻¹ o))⁻¹, fun p ↦ ?_⟩
  rw [Equiv.Perm.inv_eq_iff_eq, hc]
  exact Prod.ext (tr_tr_inv _ _).symm (by simp only [mul_inv_cancel_left])

/-- Induction over a free group. -/
theorem free_induction {P : G → Prop} (h1 : P 1) (hof : ∀ a, P (IsFreeGroup.of a))
    (hmul : ∀ g h, P g → P h → P (g * h)) (hinv : ∀ g, P g → P g⁻¹) (g : G) : P g := by
  obtain ⟨w, rfl⟩ : ∃ w, (IsFreeGroup.toFreeGroup G).symm w = g :=
    ⟨_, MulEquiv.symm_apply_apply _ g⟩
  induction w using FreeGroup.induction_on with
  | C1 => rw [map_one]; exact h1
  | of a => exact hof a
  | inv_of a ih => rw [map_inv]; exact hinv _ ih
  | mul x y hx hy => rw [map_mul]; exact hmul _ _ hx hy

theorem Ψd_form (g : G) : HasForm (Ψd hT hβ hratio g) g := by
  refine free_induction (P := fun g ↦ HasForm (Ψd hT hβ hratio g) g) ?_ ?_ ?_ ?_ g
  · exact ⟨fun _ ↦ 1, fun p ↦ by rw [map_one, Equiv.Perm.one_apply, tr_one, one_mul]⟩
  · intro a
    refine ⟨aG hT hβ hratio (IsFreeGroup.of a), fun p ↦ ?_⟩
    rw [Ψd, IsFreeGroup.lift_of]
    rfl
  · intro g h hg hh
    rw [map_mul]; exact hasForm_mul hg hh
  · intro g hg
    rw [map_inv]; exact hasForm_inv hg

/-- The root of the orbit of `o`. -/
def root (o : CovObj D) : CovObj D := (show ι × G from (o.1, 1))

theorem tr_root (o : CovObj D) : tr o.2 (root o) = o := Prod.ext rfl (mul_one _)

/-- **The object values `f`**: the transport of `(root, 1)`. -/
def fv (o : CovObj D) : kˣ := (Ψd hT hβ hratio o.2 (root o, 1)).2

theorem Ψd_root (o : CovObj D) : Ψd hT hβ hratio o.2 (root o, 1) = (o, fv hT hβ hratio o) := by
  obtain ⟨c, hc⟩ := Ψd_form hT hβ hratio o.2
  refine Prod.ext ?_ rfl
  rw [hc]
  exact tr_root o

/-- **`f(g x) = a_g(x) f(x)`** for the free generators. -/
theorem fv_tr (a : IsFreeGroup.Generators G) (o : CovObj D) :
    fv hT hβ hratio (tr (IsFreeGroup.of a) o) =
      aG hT hβ hratio (IsFreeGroup.of a) o * fv hT hβ hratio o := by
  change (Ψd hT hβ hratio (IsFreeGroup.of a * o.2) (root o, 1)).2 = _
  rw [map_mul, Equiv.Perm.mul_apply, Ψd_root, Ψd, IsFreeGroup.lift_of]
  rfl

/-! ### The invariant basis -/

/-- **`b'_{xy} = (f(y)/f(x)) b_{xy}`.** -/
def bInv (o o' : CovObj D) : o ⟶ o' :=
  ((fv hT hβ hratio o' : k) / fv hT hβ hratio o) • β o o'

/-- The object `(x, g)` of the cover. -/
def pt (x : ι) (g : G) : CovObj D := (x, g)

@[simp] theorem pt_fst (x : ι) (g : G) : (pt (D := D) x g).1 = x := rfl
@[simp] theorem pt_snd (x : ι) (g : G) : (pt (D := D) x g).2 = g := rfl

theorem bInv_sheet {x y : ι} {g g' h h' : G} (hg : g = g') (hh : h = h') :
    (bInv hT hβ hratio (pt x g) (pt y h)).1 = (bInv hT hβ hratio (pt x g') (pt y h')).1 := by
  subst hg hh; rfl

/-- `b'` is still multiplicative. -/
theorem bInv_mul (o o' o'' : CovObj D) :
    bInv hT hβ hratio o o' ≫ bInv hT hβ hratio o' o'' = 0 ∨
      bInv hT hβ hratio o o' ≫ bInv hT hβ hratio o' o'' = bInv hT hβ hratio o o'' := by
  unfold bInv
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul]
  rcases hβ.mul o trivial o' trivial o'' trivial with h | h
  · left; rw [h, smul_zero]
  · right
    rw [h]
    congr 1
    field_simp

theorem bInv_id (o : CovObj D) : bInv hT hβ hratio o o = 𝟙 o := by
  rw [bInv, div_self (Units.ne_zero _), one_smul, hβ.id o trivial]

theorem bInv_ne_zero {o o' : CovObj D} (h : β o o' ≠ 0) : bInv hT hβ hratio o o' ≠ 0 :=
  smul_ne_zero (div_ne_zero (Units.ne_zero _) (Units.ne_zero _)) h

/-- **`b'` is invariant under the free generators.** -/
theorem bInv_tr_of (a : IsFreeGroup.Generators G) (o o' : CovObj D) :
    (bInv hT hβ hratio (tr (IsFreeGroup.of a) o) (tr (IsFreeGroup.of a) o')).1 =
      (bInv hT hβ hratio o o').1 := by
  set s := IsFreeGroup.of a
  by_cases h : β o o' = 0
  · have ht : β (tr s o) (tr s o') = 0 := by
      by_contra ht
      exact ((β_ne_zero_iff hβ).2 ⟨untrHom s (β (tr s o) (tr s o')),
        fun h0 ↦ ht (Subtype.ext (show (β (tr s o) (tr s o')).1 = 0 from
          congrArg Subtype.val h0))⟩) h
    simp only [bInv, ht, h, smul_zero]
    rfl
  · have e := dg_spec hT hβ s h
    rw [aG_spec hT hβ hratio s h] at e
    have key : ((fv hT hβ hratio (tr s o') : k) / fv hT hβ hratio (tr s o)) =
        ((fv hT hβ hratio o' : k) / fv hT hβ hratio o) *
          ((aG hT hβ hratio s o' : k) / aG hT hβ hratio s o) := by
      rw [fv_tr, fv_tr]
      simp only [Units.val_mul]
      field_simp
      ring
    have e1 : ((aG hT hβ hratio s o' : k) / aG hT hβ hratio s o) • (β (tr s o) (tr s o')).1 =
        (β o o').1 := (congrArg Subtype.val e).symm
    change ((fv hT hβ hratio (tr s o') : k) / fv hT hβ hratio (tr s o)) •
        (β (tr s o) (tr s o')).1 =
      ((fv hT hβ hratio o' : k) / fv hT hβ hratio o) • (β o o').1
    rw [key, mul_smul, e1]
    rfl

/-- **`b'` is deck invariant.** -/
theorem bInv_tr (g : G) (o o' : CovObj D) :
    (bInv hT hβ hratio (tr g o) (tr g o')).1 = (bInv hT hβ hratio o o').1 := by
  refine free_induction (P := fun g ↦ ∀ o o' : CovObj D,
    (bInv hT hβ hratio (tr g o) (tr g o')).1 = (bInv hT hβ hratio o o').1) ?_ ?_ ?_ ?_ g o o'
  · intro o o'
    exact bInv_sheet hT hβ hratio (x := o.1) (y := o'.1) (one_mul o.2) (one_mul o'.2)
  · exact bInv_tr_of hT hβ hratio
  · intro g h hg hh o o'
    rw [← hh o o', ← hg (tr h o) (tr h o')]
    exact bInv_sheet hT hβ hratio (x := o.1) (y := o'.1) (mul_assoc g h o.2) (mul_assoc g h o'.2)
  · intro g hg o o'
    rw [← hg (tr g⁻¹ o) (tr g⁻¹ o')]
    exact bInv_sheet hT hβ hratio (x := o.1) (y := o'.1) (mul_inv_cancel_left g o.2)
      (mul_inv_cancel_left g o'.2)

/-! ### Descent -/

/-- **The descended vectors**: `b(x, y, g) = b'_{(x,1),(y,g)}`. -/
def bD (x y : ι) (g : G) : F x ⟶ F y :=
  (bInv hT hβ hratio (pt x 1) (pt y g)).1

theorem bD_mem (x y : ι) (g : G) : bD hT hβ hratio x y g ∈ D.part g x y := by
  have := (bInv hT hβ hratio (pt x 1) (pt y g)).2
  change _ ∈ D.part ((1 : G)⁻¹ * g) x y at this
  rwa [inv_one, one_mul] at this

theorem bD_ne_zero {x y : ι} {g : G} (h : D.part g x y ≠ ⊥) : bD hT hβ hratio x y g ≠ 0 := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hf' : f ∈ CovHom (D := D) (pt x 1) (pt y g) := by
    change f ∈ D.part ((1 : G)⁻¹ * g) x y
    rwa [inv_one, one_mul]
  have hβ0 := (β_ne_zero_iff hβ).2 ⟨(⟨f, hf'⟩ : pt (D := D) x 1 ⟶ pt y g),
    fun h0 ↦ hf0 (show f = 0 from congrArg Subtype.val h0)⟩
  intro h0
  exact bInv_ne_zero hT hβ hratio hβ0 (Subtype.ext h0)

theorem bD_span {x y : ι} {g : G} {f : F x ⟶ F y} (hf : f ∈ D.part g x y) :
    ∃ c : k, f = c • bD hT hβ hratio x y g := by
  by_cases h : D.part g x y = ⊥
  · rw [h, Submodule.mem_bot] at hf
    exact ⟨0, by rw [hf, zero_smul]⟩
  · have hf' : f ∈ CovHom (D := D) (pt x 1) (pt y g) := by
      change f ∈ D.part ((1 : G)⁻¹ * g) x y
      rwa [inv_one, one_mul]
    have hne : bInv hT hβ hratio (pt x 1) (pt y g) ≠ 0 :=
      fun h0 ↦ bD_ne_zero hT hβ hratio h (show bD hT hβ hratio x y g = 0 from
        congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := Thin.exists_smul hT hne (⟨f, hf'⟩ : pt (D := D) x 1 ⟶ pt y g)
    exact ⟨c, congrArg Subtype.val hc⟩

theorem bD_id (x : ι) : bD hT hβ hratio x x 1 = 𝟙 (F x) := by
  unfold bD
  rw [bInv_id]
  rfl

/-- **The descended vectors are multiplicative.** -/
theorem bD_mul (x y z : ι) (g h : G) :
    bD hT hβ hratio x y g ≫ bD hT hβ hratio y z h = 0 ∨
      bD hT hβ hratio x y g ≫ bD hT hβ hratio y z h = bD hT hβ hratio x z (g * h) := by
  have e : bD hT hβ hratio y z h =
      (bInv hT hβ hratio (pt y g) (pt z (g * h))).1 := by
    unfold bD
    rw [← bInv_tr hT hβ hratio g (pt y 1) (pt z h)]
    exact bInv_sheet hT hβ hratio (mul_one g) rfl
  rw [e]
  rcases bInv_mul hT hβ hratio (pt x 1) (pt y g) (pt z (g * h)) with h0 | h1
  · left; exact congrArg Subtype.val h0
  · right; exact congrArg Subtype.val h1

end CatAlg

end MultiplicativeBasisDeformations
