import MultiplicativeBasisDeformations.Foundations.CoverWeights
import MultiplicativeBasisDeformations.Foundations.ScalarNormalization

/-!
# The scalar-weight group `W(P)` of `A₀` (Definition 7.1, Proposition 7.2)

`weights-and-parameters.tex:44–152`. For a finite ray category `Q`,
`W(Q) = ℤ⟨[r] : r ≠ 0, 1⟩ / ⟨[rs] − [r] − [s] : rs ≠ 0⟩` (`def:scalar-weight-group`).
For `P = ray A₀` we use the deck-homogeneous pieces of `A₀` as the nonzero rays
(Proposition 4.14: each homogeneous ray line lies in one deck degree and the
products of the normed basis are the ray products): generators `[x, y, g]` for
the nonzero pieces `A₀(x, y)_g`, relations `[x, z, gh] = [x, y, g] + [y, z, h]`
when a product of the two pieces is nonzero (`WP`).

"Every additive weight on `L`, with values in any abelian group, is a difference
of object values" (Proposition 7.2(2), `L_addWeight_eq_diff`), from the generic
`cov_addWeight_eq_diff` and Lemma 4.13 (`ratio_hyp`). For Proposition 7.2(1) see
`Ψ`, `Φ` below.

Deviation in Proposition 7.2(1): the deck group of the formalization is the
fundamental group of the coned complex (`DeckGrading.lean`), so the lifted
projective category need not be connected. We use the stabilizer `H` of the
component of a base object in place of `G = π₁(K)`; for connected `A` the paper's
argument then gives `W(P) ≅ ℤ^{n−1} ⊕ H_ab` (`Φ ∘ Ψ = 1`). Its freeness, needed
later, follows: `W(P)` is finitely generated and embeds in a torsion-free group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u z

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {k : Type u} [Field k] [IsAlgClosed k] [Infinite k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {c : MeshCoefficients k Q} {v₀ : V}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]
  (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ)

variable (Q c v₀ D) in
/-- The lifted projective category `L`. -/
abbrev LObj := CovObj (D0 Q c v₀ D)

include hF in
/-- **Lemma 4.13, additively**: an `Additive kˣ`-valued weight on `L` is a
difference of object values. -/
theorem ratio_add (w' : LObj Q c v₀ D → LObj Q c v₀ D → Additive kˣ)
    (hw : Thin.IsAddWeight Set.univ w') :
    ∃ ζ : LObj Q c v₀ D → Additive kˣ, ∀ o o', Thin.Line o o' → w' o o' = ζ o' - ζ o := by
  classical
  let d : LObj Q c v₀ D → LObj Q c v₀ D → k := fun o o' ↦
    ((Additive.toMul (w' o o') : kˣ) : k)
  have hd : Thin.IsWeight Set.univ d := by
    refine ⟨fun _ _ _ _ _ _ ↦ Units.ne_zero _, fun o _ o' _ o'' _ f g hfg ↦ ?_⟩
    simp only [d, hw.mul o trivial o' trivial o'' trivial f g hfg, toMul_add, Units.val_mul]
  obtain ⟨ζ', hζ'0, hζ'⟩ := ratio_hyp (Q := Q) (c := c) (v₀ := v₀) hF d hd
  refine ⟨fun o ↦ Additive.ofMul (Units.mk0 (ζ' o) (hζ'0 o)), fun o o' ⟨f, hf⟩ ↦ ?_⟩
  have h := hζ' o o' f hf
  apply Additive.toMul.injective
  rw [toMul_sub, toMul_ofMul, toMul_ofMul]
  apply Units.ext
  rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0]
  exact h

include hF in
/-- **Proposition 7.2(2)** (`prop:integral-ray-weights`) for `A₀`: every additive
weight on `L`, with values in any abelian group, is a difference of object values. -/
theorem L_addWeight_eq_diff {M : Type z} [AddCommGroup M]
    (w' : LObj Q c v₀ D → LObj Q c v₀ D → M) (hw : Thin.IsAddWeight Set.univ w') :
    ∃ ζ : LObj Q c v₀ D → M, ∀ o o', Thin.Line o o' → w' o o' = ζ o' - ζ o := by
  have hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y) :=
    fun x y ↦ hfd x y
  let H0 := (deckHeight Q c v₀).comp (Subtype.val : D.PV → V) Subtype.val_injective
  exact cov_addWeight_eq_diff H0 hF (ratio_add hF) w' hw

/-! ### The group `W(P)` -/

variable (Q c v₀ D) in
/-- A deck piece `A₀(x, y)_g`. -/
abbrev Piece := D.PV × D.PV × Deck Q v₀

variable (Q c v₀ D) in
/-- A nonzero piece, that is, a nonzero ray of `P`. -/
def NZ (t : Piece Q c v₀ D) : Prop := (D0 Q c v₀ D).part t.2.2 t.1 t.2.1 ≠ ⊥

variable (Q c v₀ D) in
/-- The relations of `W(P)`. -/
def relW : AddSubgroup (Piece Q c v₀ D →₀ ℤ) := AddSubgroup.closure
  ({r | ∃ (x y z : D.PV) (g h : Deck Q v₀) (f : D.F0 x ⟶ D.F0 y) (f' : D.F0 y ⟶ D.F0 z),
     f ∈ (D0 Q c v₀ D).part g x y ∧ f' ∈ (D0 Q c v₀ D).part h y z ∧ f ≫ f' ≠ 0 ∧
     r = Finsupp.single (x, z, g * h) 1 - Finsupp.single (x, y, g) 1 -
       Finsupp.single (y, z, h) 1} ∪
   {r | ∃ t, ¬ NZ Q c v₀ D t ∧ r = Finsupp.single t 1})

variable (Q c v₀ D) in
/-- **The scalar-weight group** `W(P)` (Definition 7.1). -/
abbrev WP := (Piece Q c v₀ D →₀ ℤ) ⧸ relW Q c v₀ D

variable (Q c v₀ D) in
/-- The class `[r]` of a ray. -/
def cls (t : Piece Q c v₀ D) : WP Q c v₀ D := QuotientAddGroup.mk (Finsupp.single t 1)

theorem grp_cancel {G : Type*} [Group G] (a b d : G) : a⁻¹ * b * (b⁻¹ * d) = a⁻¹ * d := by group

theorem grp_shift {G : Type*} [Group G] (g a b : G) : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group

theorem deck_cancel (a b d : Deck Q v₀) : a⁻¹ * b * (b⁻¹ * d) = a⁻¹ * d := grp_cancel a b d

theorem deck_shift (g a b : Deck Q v₀) : (g * a)⁻¹ * (g * b) = a⁻¹ * b := grp_shift g a b

theorem cls_mul {x y z : D.PV} {g h : Deck Q v₀} {f : D.F0 x ⟶ D.F0 y} {f' : D.F0 y ⟶ D.F0 z}
    (hf : f ∈ (D0 Q c v₀ D).part g x y) (hf' : f' ∈ (D0 Q c v₀ D).part h y z) (hff : f ≫ f' ≠ 0) :
    cls Q c v₀ D (x, z, g * h) = cls Q c v₀ D (x, y, g) + cls Q c v₀ D (y, z, h) := by
  have hmem : Finsupp.single (x, z, g * h) (1 : ℤ) - Finsupp.single (x, y, g) 1 -
      Finsupp.single (y, z, h) 1 ∈ relW Q c v₀ D :=
    AddSubgroup.subset_closure (Or.inl ⟨x, y, z, g, h, f, f', hf, hf', hff, rfl⟩)
  have := (QuotientAddGroup.eq_zero_iff _).2 hmem
  simp only [QuotientAddGroup.mk_sub] at this
  rw [← sub_eq_zero, ← this]
  simp only [cls]
  abel

theorem cls_of_not_nz {t : Piece Q c v₀ D} (ht : ¬ NZ Q c v₀ D t) : cls Q c v₀ D t = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.subset_closure (Or.inr ⟨t, ht, rfl⟩))

/-! ### The tautological weight on `L` and its object values -/

variable (Q c v₀ D) in
/-- The weight of a line of `L`: the class of its ray. -/
def wtL (o o' : LObj Q c v₀ D) : WP Q c v₀ D := cls Q c v₀ D (o.1, o'.1, o.2⁻¹ * o'.2)

theorem wtL_isAddWeight : Thin.IsAddWeight Set.univ (wtL Q c v₀ D) := by
  refine ⟨fun o _ o' _ o'' _ f g hfg ↦ ?_⟩
  have hfg' : f.1 ≫ g.1 ≠ 0 := fun h ↦ hfg (Subtype.ext h)
  have := cls_mul (Q := Q) (c := c) (v₀ := v₀) (D := D) f.2 g.2 hfg'
  rw [deck_cancel] at this
  exact this

include hF in
theorem exists_zetaW : ∃ ζ : LObj Q c v₀ D → WP Q c v₀ D,
    ∀ o o', Thin.Line o o' → wtL Q c v₀ D o o' = ζ o' - ζ o :=
  L_addWeight_eq_diff hF _ wtL_isAddWeight

variable (Q c v₀ D) in
/-- The deck action on `L`. -/
def gL (g : Deck Q v₀) (o : LObj Q c v₀ D) : LObj Q c v₀ D := (o.1, g * o.2)

theorem gL_mul (g h : Deck Q v₀) (o : LObj Q c v₀ D) :
    gL Q c v₀ D (g * h) o = gL Q c v₀ D g (gL Q c v₀ D h o) := by
  show (o.1, g * h * o.2) = (o.1, g * (h * o.2))
  rw [mul_assoc]

theorem line_gL {o o' : LObj Q c v₀ D} (g : Deck Q v₀) (h : Thin.Line o o') :
    Thin.Line (gL Q c v₀ D g o) (gL Q c v₀ D g o') := by
  obtain ⟨f, hf⟩ := h
  have he : (g * o.2)⁻¹ * (g * o'.2) = o.2⁻¹ * o'.2 := deck_shift g o.2 o'.2
  have hmem : f.1 ∈ (D0 Q c v₀ D).part ((g * o.2)⁻¹ * (g * o'.2)) o.1 o'.1 := by
    rw [he]; exact f.2
  exact ⟨⟨f.1, hmem⟩, cov_ne_zero.2 ((cov_ne_zero (f := f)).1 hf)⟩

theorem wtL_gL (g : Deck Q v₀) (o o' : LObj Q c v₀ D) :
    wtL Q c v₀ D (gL Q c v₀ D g o) (gL Q c v₀ D g o') = wtL Q c v₀ D o o' := by
  have he : (g * o.2)⁻¹ * (g * o'.2) = o.2⁻¹ * o'.2 := deck_shift g o.2 o'.2
  simp only [wtL, gL]
  rw [he]

variable (Q c v₀ D) in
/-- An object of `L`. -/
abbrev mkL (x : D.PV) (a : Deck Q v₀) : LObj Q c v₀ D := (x, a)

variable (Q c v₀ D) in
/-- Connectedness in `L`. -/
def conn (o o' : LObj Q c v₀ D) : Prop :=
  Relation.EqvGen (fun a b : LObj Q c v₀ D ↦ Thin.Line a b) o o'

theorem conn_gL {o o' : LObj Q c v₀ D} (g : Deck Q v₀) (h : conn Q c v₀ D o o') :
    conn Q c v₀ D (gL Q c v₀ D g o) (gL Q c v₀ D g o') := by
  induction h with
  | rel a b h => exact Relation.EqvGen.rel _ _ (line_gL g h)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b d _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem zeta_shift {ζ : LObj Q c v₀ D → WP Q c v₀ D}
    (hζ : ∀ o o', Thin.Line o o' → wtL Q c v₀ D o o' = ζ o' - ζ o)
    (g : Deck Q v₀) {o o' : LObj Q c v₀ D} (h : conn Q c v₀ D o o') :
    ζ (gL Q c v₀ D g o') - ζ (gL Q c v₀ D g o) = ζ o' - ζ o := by
  induction h with
  | rel a b h => rw [← hζ _ _ h, ← hζ _ _ (line_gL g h), wtL_gL]
  | refl a => simp
  | symm a b _ ih => rw [← neg_sub, ih, neg_sub]
  | trans a b d _ _ ih ih' =>
    rw [show ζ (gL Q c v₀ D g d) - ζ (gL Q c v₀ D g a) =
      (ζ (gL Q c v₀ D g d) - ζ (gL Q c v₀ D g b)) + (ζ (gL Q c v₀ D g b) - ζ (gL Q c v₀ D g a))
      by abel, ih, ih']
    abel

/-! ### The stabilizer of the base component -/

variable (x₀ : D.PV)

variable (Q c v₀ D) in
/-- The base object `(x₀, 1)`. -/
def o₀ : LObj Q c v₀ D := (x₀, 1)

variable (Q c v₀ D) in
/-- **The stabilizer `H`** of the component of the base object. -/
def Hs : Subgroup (Deck Q v₀) where
  carrier := {g | conn Q c v₀ D (o₀ Q c v₀ D x₀) (x₀, g)}
  one_mem' := Relation.EqvGen.refl _
  mul_mem' {a b} ha hb := by
    have h := conn_gL a hb
    have e1 : a * (1 : Deck Q v₀) = a := mul_one _
    simp only [o₀, gL] at h
    rw [e1] at h
    exact Relation.EqvGen.trans _ _ _ ha h
  inv_mem' {a} ha := by
    have h := conn_gL a⁻¹ ha
    have e1 : a⁻¹ * (1 : Deck Q v₀) = a⁻¹ := mul_one _
    have e2 : a⁻¹ * a = (1 : Deck Q v₀) := inv_mul_cancel a
    simp only [o₀, gL] at h
    rw [e1, e2] at h
    exact Relation.EqvGen.symm _ _ h

variable (Q c v₀ D) in
/-- The connectedness of `A₀`: a zigzag of nonzero pieces from `x₀` to every label. -/
def A0Conn : Prop :=
  ∀ x : D.PV, Relation.EqvGen (fun x y : D.PV ↦ ∃ g, NZ Q c v₀ D (x, y, g)) x₀ x

theorem line_of_nz {x y : D.PV} {g : Deck Q v₀} (h : NZ Q c v₀ D (x, y, g)) (a : Deck Q v₀) :
    Thin.Line (show LObj Q c v₀ D from (x, a)) (y, a * g) := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have e : a⁻¹ * (a * g) = g := inv_mul_cancel_left a g
  have hmem : f ∈ (D0 Q c v₀ D).part (a⁻¹ * (a * g)) x y := by rwa [e]
  exact ⟨⟨f, hmem⟩, fun h0 ↦ hf0 (congrArg Subtype.val h0)⟩

theorem exists_lift {x y : D.PV}
    (h : Relation.EqvGen (fun x y : D.PV ↦ ∃ g, NZ Q c v₀ D (x, y, g)) x y) :
    ∀ a, ∃ b, conn Q c v₀ D (x, a) (y, b) := by
  induction h with
  | rel x y h =>
    obtain ⟨g, hg⟩ := h
    exact fun a ↦ ⟨a * g, Relation.EqvGen.rel _ _ (line_of_nz hg a)⟩
  | refl x => exact fun a ↦ ⟨a, Relation.EqvGen.refl _⟩
  | symm x y _ ih =>
    intro a
    obtain ⟨b, hb⟩ := ih 1
    have := conn_gL (a * b⁻¹) hb
    have e1 : a * b⁻¹ * (1 : Deck Q v₀) = a * b⁻¹ := mul_one _
    have e2 : a * b⁻¹ * b = a := inv_mul_cancel_right a b
    simp only [gL] at this
    rw [e1, e2] at this
    exact ⟨a * b⁻¹, Relation.EqvGen.symm _ _ this⟩
  | trans x y z _ _ ih ih' =>
    intro a
    obtain ⟨b, hb⟩ := ih a
    obtain ⟨d, hd⟩ := ih' b
    exact ⟨d, Relation.EqvGen.trans _ _ _ hb hd⟩

variable {x₀}

/-- A lift of each label in the base component. -/
def aL (hconn : A0Conn Q c v₀ D x₀) (x : D.PV) : Deck Q v₀ :=
  Classical.choose (exists_lift (hconn x) 1)

theorem aL_spec (hconn : A0Conn Q c v₀ D x₀) (x : D.PV) :
    conn Q c v₀ D (o₀ Q c v₀ D x₀) (x, aL hconn x) :=
  Classical.choose_spec (exists_lift (hconn x) 1)

theorem mem_Hs (hconn : A0Conn Q c v₀ D x₀) {x : D.PV} {b : Deck Q v₀}
    (h : conn Q c v₀ D (o₀ Q c v₀ D x₀) (x, b)) : b * (aL hconn x)⁻¹ ∈ Hs Q c v₀ D x₀ := by
  have h1 := conn_gL (b * (aL hconn x)⁻¹) (aL_spec hconn x)
  have e1 : b * (aL hconn x)⁻¹ * (1 : Deck Q v₀) = b * (aL hconn x)⁻¹ := mul_one _
  have e2 : b * (aL hconn x)⁻¹ * aL hconn x = b := inv_mul_cancel_right b _
  simp only [o₀, gL] at h1
  rw [e1, e2] at h1
  exact Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.symm _ _ h1)

theorem conn_nz (hconn : A0Conn Q c v₀ D x₀) {x y : D.PV} {g : Deck Q v₀}
    (h : NZ Q c v₀ D (x, y, g)) :
    conn Q c v₀ D (o₀ Q c v₀ D x₀) (y, aL hconn x * g) :=
  Relation.EqvGen.trans _ _ _ (aL_spec hconn x) (Relation.EqvGen.rel _ _ (line_of_nz h _))

/-! ### The comparison `W(P) → ℤ^{labels} × H_ab` and its left inverse -/

theorem grp_mid {G : Type*} [Group G] (a g b h d : G) :
    a * g * b⁻¹ * (b * h * d⁻¹) = a * (g * h) * d⁻¹ := by group

theorem grp_back {G : Type*} [Group G] (a g b : G) : a * g * b⁻¹ * b = a * g := by group

variable (hconn : A0Conn Q c v₀ D x₀)

variable (Q c v₀ D x₀) in
/-- The target `ℤ^{labels} × H_ab`. -/
abbrev Tgt := (D.PV → ℤ) × Additive (Abelianization (Hs Q c v₀ D x₀))

open Classical in
/-- The value of the comparison on a generator. -/
def ψgen (t : Piece Q c v₀ D) : Tgt Q c v₀ D x₀ :=
  if h : NZ Q c v₀ D t then
    (Pi.single t.2.1 1 - Pi.single t.1 1, Additive.ofMul (Abelianization.of
      ⟨aL hconn t.1 * t.2.2 * (aL hconn t.2.1)⁻¹,
        mem_Hs hconn (conn_nz (x := t.1) (y := t.2.1) (g := t.2.2) hconn h)⟩))
  else 0

theorem nz_of_comp {x y z : D.PV} {g h : Deck Q v₀} {f : D.F0 x ⟶ D.F0 y} {f' : D.F0 y ⟶ D.F0 z}
    (hf : f ∈ (D0 Q c v₀ D).part g x y) (hf' : f' ∈ (D0 Q c v₀ D).part h y z)
    (hff : f ≫ f' ≠ 0) :
    NZ Q c v₀ D (x, y, g) ∧ NZ Q c v₀ D (y, z, h) ∧ NZ Q c v₀ D (x, z, g * h) := by
  refine ⟨fun h0 ↦ hff ?_, fun h0 ↦ hff ?_, fun h0 ↦ hff ?_⟩
  · have : f = 0 := by rw [← Submodule.mem_bot k, ← h0]; exact hf
    rw [this, Limits.zero_comp]
  · have : f' = 0 := by rw [← Submodule.mem_bot k, ← h0]; exact hf'
    rw [this, Limits.comp_zero]
  · have hc : f ≫ f' ∈ (D0 Q c v₀ D).part (g * h) x z := by
      rw [HomGrading.mem_part_iff] at hf hf' ⊢
      exact (D0 Q c v₀ D).isHom_comp hf hf'
    rw [← Submodule.mem_bot k, ← h0]; exact hc

/-- **The comparison** `Ψ : W(P) → ℤ^{labels} × H_ab`. -/
def ΨW : WP Q c v₀ D →+ Tgt Q c v₀ D x₀ :=
  QuotientAddGroup.lift (relW Q c v₀ D)
    (Finsupp.liftAddHom fun t ↦ zmultiplesHom _ (ψgen hconn t)) (by
      intro r hr
      rw [AddMonoidHom.mem_ker]
      induction hr using AddSubgroup.closure_induction with
      | mem r hr =>
        rcases hr with ⟨x, y, z, g, h, f, f', hf, hf', hff, rfl⟩ | ⟨t, ht, rfl⟩
        · obtain ⟨h1, h2, h3⟩ := nz_of_comp hf hf' hff
          simp only [map_sub, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_smul]
          simp only [ψgen, dif_pos h1, dif_pos h2, dif_pos h3]
          refine Prod.ext ?_ ?_
          · simp only [Prod.fst_sub, Prod.fst_zero]
            abel
          · simp only [Prod.snd_sub, Prod.snd_zero]
            have e : (⟨aL hconn x * (g * h) * (aL hconn z)⁻¹, mem_Hs hconn (conn_nz hconn h3)⟩ :
                Hs Q c v₀ D x₀) =
                ⟨aL hconn x * g * (aL hconn y)⁻¹, mem_Hs hconn (conn_nz hconn h1)⟩ *
                ⟨aL hconn y * h * (aL hconn z)⁻¹, mem_Hs hconn (conn_nz hconn h2)⟩ :=
              Subtype.ext (grp_mid (G := Deck Q v₀) _ _ _ _ _).symm
            rw [e, map_mul, ofMul_mul]
            abel
        · simp [ψgen, dif_neg ht]
      | zero => exact map_zero _
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | neg a _ ha => rw [map_neg, ha, neg_zero])

theorem ΨW_cls (t : Piece Q c v₀ D) : ΨW hconn (cls Q c v₀ D t) = ψgen hconn t := by
  simp [ΨW, cls]

variable {ζ : LObj Q c v₀ D → WP Q c v₀ D}
  (hζ : ∀ o o', Thin.Line o o' → wtL Q c v₀ D o o' = ζ o' - ζ o)

include hζ in
/-- The deck classes `θ_h = [e_{h x} − e_x]`, `h ∈ H`. -/
def γH : Hs Q c v₀ D x₀ →* Multiplicative (WP Q c v₀ D) where
  toFun h := Multiplicative.ofAdd (ζ (gL Q c v₀ D h.1 (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀))
  map_one' := by
    have e : (1 : Deck Q v₀) * 1 = 1 := one_mul 1
    simp only [OneMemClass.coe_one, gL, o₀]
    rw [e, sub_self, ofAdd_zero]
  map_mul' a b := by
    have hb : conn Q c v₀ D (o₀ Q c v₀ D x₀) (gL Q c v₀ D b.1 (o₀ Q c v₀ D x₀)) := by
      have e : b.1 * (1 : Deck Q v₀) = b.1 := mul_one _
      have := b.2
      simp only [gL, o₀]
      rw [e]
      exact this
    have hs := zeta_shift hζ a.1 hb
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, gL_mul]
    rw [show ζ (gL Q c v₀ D a.1 (gL Q c v₀ D b.1 (o₀ Q c v₀ D x₀))) - ζ (o₀ Q c v₀ D x₀) =
      (ζ (gL Q c v₀ D a.1 (gL Q c v₀ D b.1 (o₀ Q c v₀ D x₀))) -
        ζ (gL Q c v₀ D a.1 (o₀ Q c v₀ D x₀))) +
      (ζ (gL Q c v₀ D a.1 (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀)) by abel, hs]
    abel

include hζ in
/-- **The inverse comparison** `Φ : ℤ^{labels} × H_ab → W(P)`. -/
def ΦW : Tgt Q c v₀ D x₀ →+ WP Q c v₀ D :=
  AddMonoidHom.coprod
    { toFun := fun n ↦ ∑ x, n x • ζ (x, aL hconn x)
      map_zero' := by simp
      map_add' := fun n n' ↦ by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib] }
    (MonoidHom.toAdditiveLeft (Abelianization.lift (γH hζ)))

include hζ in
/-- **`Φ ∘ Ψ = 1`** (Proposition 7.2(1), injectivity of the comparison). -/
theorem ΦW_ΨW (w : WP Q c v₀ D) : ΦW hconn hζ (ΨW hconn w) = w := by
  induction w using QuotientAddGroup.induction_on with
  | H u =>
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' h h' =>
    rw [QuotientAddGroup.mk_add, map_add, map_add, h, h']
  | single t n =>
    have hsingle : (QuotientAddGroup.mk (Finsupp.single t n) : WP Q c v₀ D) = n • cls Q c v₀ D t := by
      rw [cls, ← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, map_zsmul, map_zsmul, ΨW_cls]
    congr 1
    obtain ⟨x, y, g⟩ := t
    by_cases ht : NZ Q c v₀ D (x, y, g)
    · simp only [ψgen, dif_pos ht, ΦW, AddMonoidHom.coprod_apply, AddMonoidHom.coe_mk,
        ZeroHom.coe_mk, MonoidHom.coe_toAdditiveLeft, Function.comp_apply, toMul_ofMul]
      rw [Abelianization.lift_apply_of]
      simp only [γH, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single y (fun v _ hv ↦ by simp [Pi.single_apply, hv])
        (fun h ↦ absurd (Finset.mem_univ y) h),
        Finset.sum_eq_single x (fun v _ hv ↦ by simp [Pi.single_apply, hv])
        (fun h ↦ absurd (Finset.mem_univ x) h)]
      simp only [Pi.single_eq_same, one_smul]
      -- the deck class
      have hs := zeta_shift hζ (aL hconn x * g * (aL hconn y)⁻¹) (aL_spec hconn y)
      have e : aL hconn x * g * (aL hconn y)⁻¹ * aL hconn y = aL hconn x * g := grp_back (G := Deck Q v₀) _ _ _
      simp only [gL] at hs
      rw [e] at hs
      have hline := hζ _ _ (line_of_nz ht (aL hconn x))
      have e2 : (aL hconn x)⁻¹ * (aL hconn x * g) = g := inv_mul_cancel_left (G := Deck Q v₀) _ _
      simp only [wtL] at hline
      rw [e2] at hline
      rw [hline]
      set p := aL hconn x * g * (aL hconn y)⁻¹
      have hs2 : ζ (mkL Q c v₀ D y (aL hconn x * g)) - ζ (gL Q c v₀ D p (o₀ Q c v₀ D x₀)) =
          ζ (mkL Q c v₀ D y (aL hconn y)) - ζ (o₀ Q c v₀ D x₀) := hs
      have hs' : ζ (gL Q c v₀ D p (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀) =
          ζ (mkL Q c v₀ D y (aL hconn x * g)) - ζ (mkL Q c v₀ D y (aL hconn y)) := by
        calc ζ (gL Q c v₀ D p (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀)
            = (ζ (mkL Q c v₀ D y (aL hconn x * g)) - ζ (mkL Q c v₀ D y (aL hconn y))) -
              ((ζ (mkL Q c v₀ D y (aL hconn x * g)) - ζ (gL Q c v₀ D p (o₀ Q c v₀ D x₀))) -
                (ζ (mkL Q c v₀ D y (aL hconn y)) - ζ (o₀ Q c v₀ D x₀))) := by abel
          _ = _ := by rw [hs2, sub_self, sub_zero]
      change ζ (mkL Q c v₀ D y (aL hconn y)) - ζ (mkL Q c v₀ D x (aL hconn x)) +
        (ζ (gL Q c v₀ D p (o₀ Q c v₀ D x₀)) - ζ (o₀ Q c v₀ D x₀)) = _
      rw [hs']
      abel
    · simp only [ψgen, dif_neg ht, map_zero]
      exact (cls_of_not_nz ht).symm

/-! ### Freeness of `W(P)` -/

theorem finite_nz : {t : Piece Q c v₀ D | NZ Q c v₀ D t}.Finite := by
  classical
  have hxy : ∀ x y : D.PV, {g : Deck Q v₀ | NZ Q c v₀ D (x, y, g)}.Finite := by
    intro x y
    let B := Module.finBasis k (D.F0 x ⟶ D.F0 y)
    choose s hs using fun i ↦ (D0 Q c v₀ D).sum x y (B i)
    refine Set.Finite.subset (Finset.univ.biUnion s).finite_toSet fun g hg ↦ ?_
    by_contra hgs
    apply hg
    rw [eq_bot_iff]
    rintro _ ⟨f, rfl⟩
    rw [Submodule.mem_bot, ← B.sum_repr f, map_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [map_smul, hs i, map_sum, Finset.sum_eq_zero, smul_zero]
    intro h hh
    rw [(D0 Q c v₀ D).proj_proj, if_neg]
    rintro rfl
    exact hgs (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hh⟩))
  have : {t : Piece Q c v₀ D | NZ Q c v₀ D t} ⊆
      ⋃ x : D.PV, ⋃ y : D.PV, (fun g ↦ (x, y, g)) '' {g | NZ Q c v₀ D (x, y, g)} := by
    rintro ⟨x, y, g⟩ h
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, ⟨g, h, rfl⟩⟩⟩
  exact Set.Finite.subset (Set.finite_iUnion fun x ↦ Set.finite_iUnion fun y ↦
    (hxy x y).image _) this

/-- `W(P)` is finitely generated. -/
theorem WP_finite : Module.Finite ℤ (WP Q c v₀ D) := by
  classical
  have hfin := (finite_nz (Q := Q) (c := c) (v₀ := v₀) (D := D)).toFinset
  refine ⟨⟨(finite_nz (Q := Q) (c := c) (v₀ := v₀) (D := D)).toFinset.image (cls Q c v₀ D), ?_⟩⟩
  rw [eq_top_iff]
  rintro w -
  induction w using QuotientAddGroup.induction_on with
  | H u =>
  induction u using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add u u' h h' => rw [QuotientAddGroup.mk_add]; exact Submodule.add_mem _ h h'
  | single t n =>
    have hsingle : (QuotientAddGroup.mk (Finsupp.single t n) : WP Q c v₀ D) = n • cls Q c v₀ D t := by
      rw [cls, ← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle]
    by_cases ht : NZ Q c v₀ D t
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2
        (Finset.mem_image.2 ⟨t, (Set.Finite.mem_toFinset _).2 ht, rfl⟩)))
    · rw [cls_of_not_nz ht, smul_zero]; exact Submodule.zero_mem _

theorem abelianization_torsionFree {Hg : Type*} [Group Hg] [IsFreeGroup Hg] :
    Module.IsTorsionFree ℤ (Additive (Abelianization Hg)) := by
  let e : Additive (Abelianization Hg) ≃+ FreeAbelianGroup (IsFreeGroup.Generators Hg) :=
    (MulEquiv.abelianizationCongr (IsFreeGroup.toFreeGroup Hg)).toAdditive
  have : Module.IsTorsionFree ℤ (FreeAbelianGroup (IsFreeGroup.Generators Hg)) := inferInstance
  refine ⟨fun n hn x y hxy ↦ ?_⟩
  apply e.injective
  have := congrArg e hxy
  rw [map_zsmul, map_zsmul] at this
  exact (Module.IsTorsionFree.isSMulRegular (R := ℤ) hn) this

include hF hconn in
/-- **`W(P)` is a free abelian group of finite rank** (Proposition 7.2(1)). -/
theorem WP_free : Module.Free ℤ (WP Q c v₀ D) := by
  have hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y) :=
    fun x y ↦ hfd x y
  haveI : IsFreeGroup (Deck Q v₀) := isFreeGroup_deck Q v₀ c hfin
  haveI : Module.Finite ℤ (WP Q c v₀ D) := WP_finite
  obtain ⟨ζ, hζ⟩ := exists_zetaW (Q := Q) (c := c) (v₀ := v₀) (D := D) hF
  have : Module.IsTorsionFree ℤ (Additive (Abelianization (Hs Q c v₀ D x₀))) :=
    abelianization_torsionFree
  have : Module.IsTorsionFree ℤ (WP Q c v₀ D) := by
    refine ⟨fun n hn w w' hww ↦ ?_⟩
    have h := congrArg (ΨW hconn) hww
    rw [map_zsmul, map_zsmul] at h
    have h' := (Module.IsTorsionFree.isSMulRegular (R := ℤ) (M := Tgt Q c v₀ D x₀) hn) h
    rw [← ΦW_ΨW hconn hζ w, ← ΦW_ΨW hconn hζ w', h']
  exact Module.free_of_finite_type_torsion_free'

end MeshWalk

end MultiplicativeBasisDeformations
