import MultiplicativeBasisDeformations.Foundations.CharBasis

/-!
# Connectedness of the Auslander–Reiten quiver in Lemma 7.4 and Proposition 7.5

`weights-and-parameters.tex`, `scalar-normalization.tex`: "we assume that `A` is
connected. Then `Γ_A` is connected by [ARS, Theorem VII.2.1]." The generic statements of
Lemma 7.4 and Proposition 7.5 (`exists_meshWt_lift`, `res_eq_zero_iff`, `eq_zero_of_diff`,
`chars_part_of_basis`) assume that every vertex is reached from a base projective by a lifted
walk (`hK`), and Proposition 7.2(1) assumes that the projectives of `A₀` are connected
(`A0Conn`). Both follow from the connectedness of the quiver (`QConn`): walks lift to the cover
(`aconn_of_walk`, `hK_of_QConn`), and lifted projectives in one component of the lifted quiver
are connected in `L` (`conn_of_aconn`), hence by nonzero pieces of `A₀` (`A0Conn_of_QConn`).
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

variable {k : Type u} [Field k] [IsAlgClosed k] [Infinite k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {c : MeshCoefficients k Q} {v₀ : V}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

variable (V) in
/-- **The quiver is connected**: any two vertices are joined by a walk of arrows. -/
def QConn : Prop := ∀ X Y : V, Relation.EqvGen (fun X Y : V ↦ Nonempty (X ⟶ Y)) X Y

/-- Walks lift to the cover from any sheet. -/
theorem aconn_of_walk {X Y : V} (h : Relation.EqvGen (fun X Y : V ↦ Nonempty (X ⟶ Y)) X Y) :
    ∀ g : Deck Q v₀, ∃ g', aconn Q v₀ (X, g) (Y, g') := by
  induction h with
  | rel X Y hXY => intro g; obtain ⟨a⟩ := hXY; exact ⟨_, aconn_arrow (X, g) a⟩
  | refl X => intro g; exact ⟨g, Relation.EqvGen.refl _⟩
  | symm X Y _ ih =>
    intro g
    obtain ⟨h, hh⟩ := ih 1
    have := aconn_shV (g * h⁻¹) hh
    simp only [shV] at this
    rw [grp_cancel_r (G := Deck Q v₀)] at this
    exact ⟨_, Relation.EqvGen.symm _ _ this⟩
  | trans X Y Z _ _ ih ih' =>
    intro g
    obtain ⟨g₁, h₁⟩ := ih g
    obtain ⟨g₂, h₂⟩ := ih' g₁
    exact ⟨g₂, Relation.EqvGen.trans _ _ _ h₁ h₂⟩

/-- **Every vertex is reached from the base projective by a lifted walk.** -/
theorem hK_of_QConn (hQ : QConn V) (x₀ : D.PV) : ∀ X : V, ∃ g, aconn Q v₀ (x₀.1, 1) (X, g) :=
  fun X ↦ aconn_of_walk (hQ x₀.1 X) 1

/-- **The projectives of `A₀` are connected by nonzero pieces.** -/
theorem A0Conn_of_QConn (hQ : QConn V) (x₀ : D.PV) : A0Conn Q c v₀ D x₀ := by
  intro x
  obtain ⟨g, hg⟩ := hK_of_QConn (D := D) hQ x₀ x.1
  have hc := conn_of_aconn (D := D) (p := x₀) (q := x) (a := 1) (b := g) hg
  have key : ∀ o o' : LObj Q c v₀ D, conn Q c v₀ D o o' →
      Relation.EqvGen (fun x y : D.PV ↦ ∃ g, NZ Q c v₀ D (x, y, g)) o.1 o'.1 := by
    intro o o' h
    induction h with
    | rel o o' hl =>
      obtain ⟨f, hf⟩ := hl
      refine Relation.EqvGen.rel _ _ ⟨o.2⁻¹ * o'.2, fun hbot ↦ hf (Subtype.ext ?_)⟩
      have hm : f.1 ∈ (D0 Q c v₀ D).part (o.2⁻¹ * o'.2) o.1 o'.1 := f.2
      rw [hbot, Submodule.mem_bot] at hm
      exact hm
    | refl o => exact Relation.EqvGen.refl _
    | symm o o' _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans o o' o'' _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  exact key _ _ hc

/-! ### From connectedness of `A₀` -/

/-- A nonzero morphism between lifted labels contains the image of a path of its degree. -/
theorem exists_path_of_mem {x y : V} {g : Deck Q v₀} {f : meshFam Q c x ⟶ meshFam Q c y}
    (hf : f ∈ (deckGrading Q c v₀).part g x y) (hf0 : f ≠ 0) :
    ∃ p : Quiver.Path x y, (degW Q v₀).deg p = g := by
  by_contra hne
  push Not at hne
  apply hf0
  have hf' : f ∈ wPart c (degW Q v₀) g x y := by
    have : (deckGrading Q c v₀).IsHom g f := (HomGrading.mem_part_iff _).1 hf
    exact (isHom_iff (Q := Q) (c := c) (v₀ := v₀)).1 this
  have := wPart_le_span (Q := Q) (c := c) (v₀ := v₀) g x y hf'
  have hempty : {f | ∃ p : Quiver.Path x y, (degW Q v₀).deg p = g ∧ pathMor c p = f} = ∅ := by
    ext f; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, hp, -⟩; exact hne p hp
  rw [hempty, Submodule.span_empty] at this
  exact (Submodule.mem_bot k).1 this

/-- A nonzero morphism of `A₀` has a nonzero deck piece. -/
theorem exists_nz_of_ne_zero {p q : D.PV} {u : D.F0 p ⟶ D.F0 q} (hu : u ≠ 0) :
    ∃ g, NZ Q c v₀ D (p, q, g) := by
  by_contra h
  push Not at h
  apply hu
  obtain ⟨s, hs⟩ := (D0 Q c v₀ D).sum p q u
  rw [hs]
  refine Finset.sum_eq_zero fun g _ ↦ ?_
  have hmem : (D0 Q c v₀ D).proj g p q u ∈ (D0 Q c v₀ D).part g p q := ⟨u, rfl⟩
  have hbot : (D0 Q c v₀ D).part g p q = ⊥ := by
    by_contra hb; exact h g hb
  rw [hbot] at hmem
  exact (Submodule.mem_bot k).1 hmem

theorem idem_apply₀ (x y z : D.PV) : idem (F := D.F0) x y z = idTo y x ≫ idTo x z := rfl

theorem idem_mul_mul_idem_apply (u : Alg D.F0) (p q y z : D.PV) :
    (idem (F := D.F0) q * u * idem p : Alg D.F0) y z = idTo y q ≫ u q p ≫ idTo p z := by
  have e1 : ∀ w, (idem (F := D.F0) q * u : Alg D.F0) y w = idTo y q ≫ u q w := by
    intro w
    calc (idem (F := D.F0) q * u : Alg D.F0) y w = ∑ v, idem (F := D.F0) q y v ≫ u v w := rfl
      _ = ∑ v, idTo y q ≫ (idTo q v ≫ u v w) := by
          refine Finset.sum_congr rfl fun v _ ↦ ?_
          rw [idem_apply₀, Category.assoc]
      _ = idTo y q ≫ u q w := by rw [← Preadditive.comp_sum, CatAlg.sum_idTo_comp]
  calc (idem (F := D.F0) q * u * idem p : Alg D.F0) y z
      = ∑ w, (idem (F := D.F0) q * u : Alg D.F0) y w ≫ idem (F := D.F0) p w z := rfl
    _ = ∑ w, idTo y q ≫ ((u q w ≫ idTo w p) ≫ idTo p z) := by
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [e1, idem_apply₀]; simp only [Category.assoc]
    _ = idTo y q ≫ u q p ≫ idTo p z := by
        rw [← Preadditive.comp_sum, ← Preadditive.sum_comp, CatAlg.sum_comp_idTo]

/-- Nonzero corners `e_p A₀ e_q` give nonzero pieces. -/
theorem exists_nz_of_corner {p q : D.PV} {x : (Alg D.F0)ᵐᵒᵖ}
    (h : MulOpposite.op (idem (F := D.F0) p) * x * MulOpposite.op (idem (F := D.F0) q) ≠ 0) :
    ∃ g, NZ Q c v₀ D (q, p, g) := by
  refine exists_nz_of_ne_zero (u := x.unop q p) fun h0 ↦ h ?_
  apply MulOpposite.unop_injective
  rw [MulOpposite.unop_mul, MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_op,
    MulOpposite.unop_zero, ← mul_assoc]
  refine CatAlg.ext fun y z ↦ ?_
  rw [idem_mul_mul_idem_apply, h0, Limits.zero_comp, Limits.comp_zero]
  rfl

/-- **Connectedness of `A₀` by its corners gives `A0Conn`.** -/
theorem A0Conn_of_corners
    (h : ∀ p q : D.PV, Relation.EqvGen (fun p q : D.PV ↦ ∃ x : (Alg D.F0)ᵐᵒᵖ,
      MulOpposite.op (idem (F := D.F0) p) * x * MulOpposite.op (idem (F := D.F0) q) ≠ 0) p q)
    (x₀ : D.PV) : A0Conn Q c v₀ D x₀ := by
  intro x
  have key : ∀ p q, Relation.EqvGen (fun p q : D.PV ↦ ∃ x : (Alg D.F0)ᵐᵒᵖ,
      MulOpposite.op (idem (F := D.F0) p) * x * MulOpposite.op (idem (F := D.F0) q) ≠ 0) p q →
      Relation.EqvGen (fun x y : D.PV ↦ ∃ g, NZ Q c v₀ D (x, y, g)) p q := by
    intro p q hpq
    induction hpq with
    | rel p q hr =>
      obtain ⟨x, hx⟩ := hr
      exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (exists_nz_of_corner hx))
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  exact key _ _ (h x₀ x)

/-- **Every vertex is reached from the base projective by a lifted walk**, when `A₀` is
connected: projectives are joined by paths of nonzero pieces, and every lifted object receives a
nonzero map, hence a path, from a lifted projective. -/
theorem hK_of_A0Conn (x₀ : D.PV) (hconn : A0Conn Q c v₀ D x₀) :
    ∀ X : V, ∃ g, aconn Q v₀ (x₀.1, 1) (X, g) := by
  have step : ∀ a b : D.PV, Relation.EqvGen (fun x y : D.PV ↦ ∃ g, NZ Q c v₀ D (x, y, g)) a b →
      ∀ h : Deck Q v₀, ∃ h', aconn Q v₀ (a.1, h) (b.1, h') := by
    intro a b hab
    induction hab with
    | rel a b hr =>
      intro h
      obtain ⟨g, hg⟩ := hr
      obtain ⟨p, -⟩ := exists_path_of_nz hg
      exact ⟨_, aconn_path p h⟩
    | refl a => intro h; exact ⟨h, Relation.EqvGen.refl _⟩
    | symm a b _ ih =>
      intro g
      obtain ⟨h, hh⟩ := ih 1
      have := aconn_shV (g * h⁻¹) hh
      simp only [shV] at this
      rw [grp_cancel_r (G := Deck Q v₀)] at this
      exact ⟨_, Relation.EqvGen.symm _ _ this⟩
    | trans a b d _ _ ih ih' =>
      intro g
      obtain ⟨g₁, h₁⟩ := ih g
      obtain ⟨g₂, h₂⟩ := ih' g₁
      exact ⟨g₂, Relation.EqvGen.trans _ _ _ h₁ h₂⟩
  intro X
  obtain ⟨z, m, hm, hm0⟩ := exists_supp (D := D) (c := c) ((X, 1) : V × Deck Q v₀)
  obtain ⟨p, -⟩ := exists_path_of_mem hm hm0
  obtain ⟨h, hh⟩ := step x₀ z.1 (hconn z.1) 1
  exact ⟨_, Relation.EqvGen.trans _ _ _ hh (aconn_path p h)⟩

end MeshWalk

end MultiplicativeBasisDeformations
