module

public import MultiplicativeBasisDeformations.Foundations.RayWeights

/-!
# Integer mesh weights and their restriction to rays (Lemma 7.4)

`weights-and-parameters.tex` (`def:integer-weights`,
`lem:integer-weight-lifting`). An *integer mesh weight* assigns `w(a)` to arrows
and `ν_v` to mesh rows with `w(σa) + w(a) = ν_v`; it restricts to an integer ray
weight, and "this restriction gives an exact sequence
`0 → {ζ : ζ_P = 0} → H^mesh → H → 0`".

The proof works on the lifted complex. "Pull a ray weight `h` back to `L`. By
Proposition 7.2, write `h(r : x → y) = b_y − b_x` […] Choose one lift of each
nonprojective label and assign it any integer. Extend by `ζ_{gX} = ζ_X + γ(g)`.
Differences along arrows and translation edges are deck invariant, hence descend
to a mesh weight."

Formalization. The deck group of the formalization is the fundamental group of
the coned complex, so we work in the component `K₀` of a base vertex in the
lifted Auslander–Reiten quiver (`aconn`), whose stabilizer plays the role of the
paper's `G = π₁(K)`. The connectivity of the lifted projective category used by
the paper is replaced by the **support lemma** (`supp_conn`): the lifted
projectives with nonzero maps to one lifted object are connected in `L`, by
Lemma 4.8 and the locality of degree-one endomorphisms; hence the lifted
projectives of `K₀` lie in one component of `L` (`conn_of_aconn`).
-/

@[expose] public section

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

theorem line_iff {z z' : LObj Q c v₀ D} : Thin.Line z z' ↔
    ∃ f : meshFam Q c z.1.1 ⟶ meshFam Q c z'.1.1,
      f ∈ (deckGrading Q c v₀).part (z.2⁻¹ * z'.2) z.1.1 z'.1.1 ∧ f ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.1, f.2, fun h ↦ hf (Subtype.ext h)⟩
  · rintro ⟨f, hf, hf0⟩
    exact ⟨⟨f, hf⟩, fun h ↦ hf0 (congrArg Subtype.val h)⟩

variable (Q c v₀ D) in
/-- A lifted projective vertex as an object of `L`. -/
def toL (z : D.PV × Deck Q v₀) : LObj Q c v₀ D := z

variable (Q c v₀ D) in
/-- An object of `L` as a lifted projective vertex. -/
def ofL (o : LObj Q c v₀ D) : D.PV × Deck Q v₀ := o

/-- **The support lemma**: two lifted projectives with nonzero maps to one lifted
object are connected in `L`. -/
theorem supp_conn (X : V × Deck Q v₀) {z₁ z₂ : D.PV × Deck Q v₀}
    {m₁ : meshFam Q c z₁.1.1 ⟶ meshFam Q c X.1}
    (hm₁ : m₁ ∈ (deckGrading Q c v₀).part (z₁.2⁻¹ * X.2) z₁.1.1 X.1) (h₁ : m₁ ≠ 0)
    {m₂ : meshFam Q c z₂.1.1 ⟶ meshFam Q c X.1}
    (hm₂ : m₂ ∈ (deckGrading Q c v₀).part (z₂.2⁻¹ * X.2) z₂.1.1 X.1) (h₂ : m₂ ≠ 0) :
    conn Q c v₀ D (toL Q c v₀ D z₁) (toL Q c v₀ D z₂) := by
  classical
  have hfin : ∀ x y : V, FiniteDimensional k (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y) :=
    fun x y ↦ hfd x y
  let φ : ∀ z : D.PV × Deck Q v₀, (meshFam Q c z.1.1 ⟶ meshFam Q c X.1) →ₗ[k]
      (meshFam Q c z.1.1 ⟶ meshFam Q c X.1) := fun z ↦
    if conn Q c v₀ D (toL Q c v₀ D z₁) (toL Q c v₀ D z) then LinearMap.id else 0
  let N : NatFam D (deckGrading Q c v₀) X X :=
    { φ := φ
      mem := fun z m hm ↦ by
        simp only [φ]
        split_ifs
        · exact hm
        · exact Submodule.zero_mem _
      nat := fun z z' u m hu hm ↦ by
        by_cases hu0 : u = 0
        · simp only [φ, hu0, Limits.zero_comp, map_zero]
        · have hl : Thin.Line (toL Q c v₀ D z') (toL Q c v₀ D z) :=
            line_iff.2 ⟨u, hu, hu0⟩
          have hiff : conn Q c v₀ D (toL Q c v₀ D z₁) (toL Q c v₀ D z') ↔
              conn Q c v₀ D (toL Q c v₀ D z₁) (toL Q c v₀ D z) :=
            ⟨fun h ↦ Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ hl),
              fun h ↦ Relation.EqvGen.trans _ _ _ h
                (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hl))⟩
          simp only [φ]
          by_cases h : conn Q c v₀ D (toL Q c v₀ D z₁) (toL Q c v₀ D z)
          · rw [if_pos h, if_pos (hiff.2 h)]; rfl
          · rw [if_neg h, if_neg (fun h' ↦ h (hiff.1 h'))]
            simp }
  obtain ⟨f, hf, hφ⟩ := N.exists_hom
  have hf1 : (deckGrading Q c v₀).IsHom 1 f := by
    have e : X.2⁻¹ * X.2 = (1 : Deck Q v₀) := inv_mul_cancel (G := Deck Q v₀) _
    rwa [e] at hf
  obtain ⟨t, ht⟩ := HeightData.scalar_one (deckHeight Q c v₀) hf1
  have hc : conn Q c v₀ D (toL Q c v₀ D z₁) (toL Q c v₀ D z₁) := Relation.EqvGen.refl _
  have h1 := hφ z₁ m₁ hm₁
  simp only [N, φ, if_pos hc, LinearMap.id_apply, ht, Linear.comp_smul, Category.comp_id] at h1
  have ht1 : t = 1 := by
    by_contra hne
    apply h₁
    have : (1 - t) • m₁ = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  by_contra hnc
  have h2 := hφ z₂ m₂ hm₂
  simp only [N, φ, if_neg hnc, LinearMap.zero_apply, ht, ht1, one_smul, Category.comp_id] at h2
  exact h₂ h2.symm

/-! ### Supports along arrows -/

variable (Q v₀) in
/-- Arrow-connectedness of lifted vertices. -/
def aconn (A B : V × Deck Q v₀) : Prop :=
  Relation.EqvGen (fun A B : V × Deck Q v₀ ↦ ∃ a : A.1 ⟶ B.1, B.2 = A.2 * dg Q v₀ a) A B

variable (Q c v₀ D) in
/-- `z` lies in the support of the lifted object `A`. -/
def InSupp (A : V × Deck Q v₀) (z : D.PV × Deck Q v₀) : Prop :=
  ∃ m : meshFam Q c z.1.1 ⟶ meshFam Q c A.1,
    m ∈ (deckGrading Q c v₀).part (z.2⁻¹ * A.2) z.1.1 A.1 ∧ m ≠ 0

theorem exists_supp (A : V × Deck Q v₀) : ∃ z, InSupp Q c v₀ D A z := by
  by_contra hne
  push Not at hne
  apply id_ne_zero (L := L) A.1
  refine eq_zero_of_lifted (D := D) (Dg := deckGrading Q c v₀) (X := A) (Y := A) _
    fun z m hm ↦ ?_
  rw [Category.comp_id]
  by_contra h
  exact hne z ⟨m, hm, h⟩

theorem grp_assoc3 {G : Type*} [Group G] (a h d : G) : a * h * (h⁻¹ * (h * d)) = a * (h * d) := by
  group

theorem common_supp {Y X : V} (a : Y ⟶ X) (h : Deck Q v₀) :
    ∃ z, InSupp Q c v₀ D (Y, h) z ∧ InSupp Q c v₀ D (X, h * dg Q v₀ a) z := by
  by_contra hne
  push Not at hne
  apply arrowMor_ne_zero (c := c) a
  refine eq_zero_of_lifted (D := D) (Dg := deckGrading Q c v₀) (X := (Y, h))
    (Y := (X, h * dg Q v₀ a)) _ fun z m hm ↦ ?_
  by_contra hmf
  have hm0 : m ≠ 0 := fun h0 ↦ hmf (by rw [h0, Limits.zero_comp])
  refine hne z ⟨m, hm, hm0⟩ ⟨_, ?_, hmf⟩
  have h2 := arrow_mem (c := c) h a
  rw [HomGrading.mem_part_iff] at hm h2 ⊢
  have := (deckGrading Q c v₀).isHom_comp hm h2
  have e : z.2⁻¹ * h * (h⁻¹ * (h * dg Q v₀ a)) = z.2⁻¹ * (h * dg Q v₀ a) :=
    grp_assoc3 (G := Deck Q v₀) _ _ _
  rwa [e] at this

theorem supp_aconn {A B : V × Deck Q v₀} (hAB : aconn Q v₀ A B) :
    ∀ {z z'}, InSupp Q c v₀ D A z → InSupp Q c v₀ D B z' →
      conn Q c v₀ D (toL Q c v₀ D z) (toL Q c v₀ D z') := by
  induction hAB with
  | rel A B h =>
    obtain ⟨a, ha⟩ := h
    intro z z' hz hz'
    obtain ⟨w, hw, hw'⟩ := common_supp (D := D) a A.2
    obtain ⟨m, hm, hm0⟩ := hz
    obtain ⟨m', hm', hm0'⟩ := hz'
    obtain ⟨n, hn, hn0⟩ := hw
    obtain ⟨n', hn', hn0'⟩ := hw'
    rw [ha] at hm'
    exact Relation.EqvGen.trans _ _ _ (supp_conn A hm hm0 hn hn0)
      (supp_conn (B.1, A.2 * dg Q v₀ a) hn' hn0' hm' hm0')
  | refl A =>
    intro z z' hz hz'
    obtain ⟨m, hm, hm0⟩ := hz
    obtain ⟨m', hm', hm0'⟩ := hz'
    exact supp_conn A hm hm0 hm' hm0'
  | symm A B _ ih =>
    intro z z' hz hz'
    exact Relation.EqvGen.symm _ _ (ih hz' hz)
  | trans A B C _ _ ih ih' =>
    intro z z' hz hz'
    obtain ⟨w, hw⟩ := exists_supp (D := D) B
    exact Relation.EqvGen.trans _ _ _ (ih hz hw) (ih' hw hz')

theorem self_supp (p : D.PV) (g : Deck Q v₀) : InSupp Q c v₀ D (p.1, g) (p, g) := by
  refine ⟨𝟙 _, ?_, id_ne_zero (L := L) p.1⟩
  rw [HomGrading.mem_part_iff]
  have e : g⁻¹ * g = (1 : Deck Q v₀) := inv_mul_cancel (G := Deck Q v₀) g
  change (deckGrading Q c v₀).IsHom ((p, g).2⁻¹ * (p.1, g).2) _
  simp only
  rw [e]
  exact (deckGrading Q c v₀).isHom_id _

/-- **Lifted projectives in one arrow-component lie in one component of `L`.** -/
theorem conn_of_aconn {p q : D.PV} {a b : Deck Q v₀} (h : aconn Q v₀ (p.1, a) (q.1, b)) :
    conn Q c v₀ D (toL Q c v₀ D (p, a)) (toL Q c v₀ D (q, b)) :=
  supp_aconn h (self_supp p a) (self_supp q b)

/-- A nonzero piece contains the image of a path of its degree. -/
theorem exists_path_of_nz {x y : D.PV} {g : Deck Q v₀} (h : NZ Q c v₀ D (x, y, g)) :
    ∃ p : Quiver.Path x.1 y.1, (degW Q v₀).deg p = g := by
  by_contra hne
  push Not at hne
  apply h
  rw [eq_bot_iff]
  intro f hf
  have hf' : f ∈ wPart c (degW Q v₀) g x.1 y.1 := by
    have : (deckGrading Q c v₀).IsHom g f := (HomGrading.mem_part_iff _).1 hf
    exact (isHom_iff (Q := Q) (c := c) (v₀ := v₀)).1 this
  have := wPart_le_span (Q := Q) (c := c) (v₀ := v₀) g x.1 y.1 hf'
  have hempty : {f | ∃ p : Quiver.Path x.1 y.1, (degW Q v₀).deg p = g ∧ pathMor c p = f} = ∅ := by
    ext f; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, hp, -⟩; exact hne p hp
  rw [hempty, Submodule.span_empty] at this
  exact this

/-! ### Integer mesh weights -/

variable (Q) in
/-- **An integer mesh weight** (Definition 7.3(2)), with values in an abelian group:
`w(σa) + w(a) = ν_v`. -/
structure MeshWt (M : Type*) [AddCommGroup M] where
  w : ∀ {y x : V}, (y ⟶ x) → M
  ν : Q.nonprojective → M
  mesh : ∀ (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1), w (Q.mate x a.1 a.2) + w a.2 = ν x

variable {M : Type z} [AddCommGroup M]

/-- The weight of a path: the sum of its arrow weights. -/
def MeshWt.pw (W : MeshWt Q M) : ∀ {y x : V}, Quiver.Path y x → M
  | _, _, Quiver.Path.nil => 0
  | _, _, Quiver.Path.cons p a => W.pw p + W.w a

/-- The edge weights on the coned complex: arrows, rows, and zero on cone edges. -/
def MeshWt.WE (W : MeshWt Q M) :
    ∀ e : Ed Q ⊕ V, (obC Q v₀ v₀ ⟶ obC Q v₀ (srcC Q v₀ e)) → Multiplicative M
  | Sum.inl (Sum.inl ⟨_, _, a⟩), _ => Multiplicative.ofAdd (W.w a)
  | Sum.inl (Sum.inr x), _ => Multiplicative.ofAdd (W.ν x)
  | Sum.inr _, _ => 1

theorem MeshWt.WE_tri (W : MeshWt Q M) (x : Q.nonprojective) (a : Σ y : V, y ⟶ x.1)
    (γ : obC Q v₀ v₀ ⟶ obC Q v₀ (Q.tau x).1) :
    W.WE (Sum.inl (Sum.inl ⟨(Q.tau x).1, a.1, Q.mate x a.1 a.2⟩)) γ *
      W.WE (Sum.inl (Sum.inl ⟨a.1, x.1, a.2⟩)) (γ ≫ arrC Q v₀ (Q.mate x a.1 a.2)) =
    W.WE (Sum.inl (Sum.inr x)) γ := by
  change Multiplicative.ofAdd _ * Multiplicative.ofAdd _ = Multiplicative.ofAdd _
  rw [← ofAdd_add, W.mesh x a]

variable (v₀) in
/-- **The object values of a mesh weight on the lifted vertices.** -/
def MeshWt.pot (W : MeshWt Q M) (A : V × Deck Q v₀) : M :=
  Multiplicative.toAdd (potW W.WE W.WE_tri (liftW Q v₀ A.2 A.1))

theorem MeshWt.pot_arrow (W : MeshWt Q M) (h : Deck Q v₀) {y x : V} (a : y ⟶ x) :
    W.pot v₀ (x, h * dg Q v₀ a) = W.pot v₀ (y, h) + W.w a := by
  have := potW_comp W.WE W.WE_tri (Sum.inl (Sum.inl ⟨y, x, a⟩)) (liftW Q v₀ h y)
  change potW W.WE W.WE_tri (liftW Q v₀ h y ≫ arrC Q v₀ a) = _ at this
  rw [liftW_arr] at this
  unfold MeshWt.pot
  rw [this, toAdd_mul]
  rfl

theorem liftW_t (h : Deck Q v₀) (x : Q.nonprojective) :
    liftW Q v₀ h (Q.tau x).1 ≫ tC Q v₀ x = liftW Q v₀ (h * tdeg x) x.1 := by
  simp only [liftW, tdeg, MulOpposite.unop_mul, MulOpposite.unop_op, End.mul_def,
    Category.assoc, Groupoid.inv_comp, Category.comp_id]

theorem MeshWt.pot_t (W : MeshWt Q M) (h : Deck Q v₀) (x : Q.nonprojective) :
    W.pot v₀ (x.1, h * tdeg x) = W.pot v₀ ((Q.tau x).1, h) + W.ν x := by
  have := potW_comp W.WE W.WE_tri (Sum.inl (Sum.inr x)) (liftW Q v₀ h (Q.tau x).1)
  change potW W.WE W.WE_tri (liftW Q v₀ h (Q.tau x).1 ≫ tC Q v₀ x) = _ at this
  rw [liftW_t] at this
  unfold MeshWt.pot
  rw [this, toAdd_mul]
  rfl

theorem grp_mul_one {G : Type*} [Group G] (h : G) : h * 1 = h := mul_one h

theorem grp_assoc {G : Type*} [Group G] (a b d : G) : a * (b * d) = a * b * d := (mul_assoc _ _ _).symm

theorem deg_cons {y x z : V} (p : Quiver.Path y x) (a : x ⟶ z) :
    (degW Q v₀).deg (p.cons a) = (degW Q v₀).deg p * dg Q v₀ a :=
  (degW Q v₀).deg_comp p a.toPath

/-- **Potentials along paths**: `ζ(x, h·deg p) = ζ(y, h) + w(p)`. -/
theorem MeshWt.pot_path (W : MeshWt Q M) (h : Deck Q v₀) {y x : V} (p : Quiver.Path y x) :
    W.pot v₀ (x, h * (degW Q v₀).deg p) = W.pot v₀ (y, h) + W.pw p := by
  induction p with
  | nil =>
    have e : h * (degW Q v₀).deg (Quiver.Path.nil : Quiver.Path y y) = h := by
      rw [(degW Q v₀).deg_nil]; exact grp_mul_one (G := Deck Q v₀) h
    rw [e, MeshWt.pw, add_zero]
  | cons p a ih =>
    have e : h * (degW Q v₀).deg (p.cons a) = h * (degW Q v₀).deg p * dg Q v₀ a := by
      rw [deg_cons]; exact grp_assoc (G := Deck Q v₀) _ _ _
    rw [e, W.pot_arrow, ih, MeshWt.pw, add_assoc]

/-! ### Restriction to rays -/

open Classical in
/-- The restriction on a generator: the weight of the paths of the ray. -/
def MeshWt.rv (W : MeshWt Q M) (t : Piece Q c v₀ D) : M :=
  if NZ Q c v₀ D t then W.pot v₀ (t.2.1.1, t.2.2) - W.pot v₀ (t.1.1, 1) else 0

theorem grp_one_mul {G : Type*} [Group G] (h : G) : 1 * h = h := one_mul h

theorem MeshWt.rv_path (W : MeshWt Q M) {x y : D.PV} {g : Deck Q v₀}
    (h : NZ Q c v₀ D (x, y, g)) {p : Quiver.Path x.1 y.1} (hp : (degW Q v₀).deg p = g) :
    W.rv (c := c) (D := D) (x, y, g) = W.pw p := by
  have := W.pot_path (v₀ := v₀) 1 p
  rw [hp, grp_one_mul (G := Deck Q v₀)] at this
  simp only [MeshWt.rv, if_pos h]
  rw [this]
  abel

variable (c D) in
/-- **The restriction of a mesh weight to an integer ray weight** (Lemma 7.4). -/
def MeshWt.res (W : MeshWt Q M) : WP Q c v₀ D →+ M :=
  QuotientAddGroup.lift (relW Q c v₀ D)
    (Finsupp.liftAddHom fun t ↦ zmultiplesHom _ (W.rv (c := c) (D := D) t)) (by
      intro r hr
      rw [AddMonoidHom.mem_ker]
      induction hr using AddSubgroup.closure_induction with
      | mem r hr =>
        rcases hr with ⟨x, y, z, g, h, f, f', hf, hf', hff, rfl⟩ | ⟨t, ht, rfl⟩
        · obtain ⟨h1, h2, h3⟩ := nz_of_comp hf hf' hff
          simp only [map_sub, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_smul]
          obtain ⟨p, hp⟩ := exists_path_of_nz h2
          have e1 := W.pot_path (v₀ := v₀) g p
          have e2 := W.pot_path (v₀ := v₀) 1 p
          rw [hp] at e1 e2
          rw [grp_one_mul (G := Deck Q v₀)] at e2
          simp only [MeshWt.rv, if_pos h1, if_pos h2, if_pos h3]
          rw [e1, e2]
          abel
        · simp [MeshWt.rv, if_neg ht]
      | zero => exact map_zero _
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | neg a _ ha => rw [map_neg, ha, neg_zero])

theorem MeshWt.res_cls (W : MeshWt Q M) (t : Piece Q c v₀ D) :
    W.res c D (cls Q c v₀ D t) = W.rv (c := c) (D := D) t := by
  simp [MeshWt.res, cls]

/-! ### Lemma 7.4: lifting ray weights to mesh weights -/

theorem grp_shift1 {G : Type*} [Group G] (u : G) : u * 1 = u := mul_one u

theorem grp_cancel_r {G : Type*} [Group G] (g k' : G) : g * k'⁻¹ * k' = g := by group

theorem grp_split {G : Type*} [Group G] (v gY d gX : G) :
    v * d * gX⁻¹ = v * gY⁻¹ * (gY * d * gX⁻¹) := by group

theorem grp_conj {G : Type*} [Group G] (g' g : G) : g' * g⁻¹ * g = g' := by group

variable (Q v₀) in
/-- Translating a lifted vertex by a deck element. -/
def shV (u : Deck Q v₀) (A : V × Deck Q v₀) : V × Deck Q v₀ := (A.1, u * A.2)

theorem aconn_shV {A B : V × Deck Q v₀} (u : Deck Q v₀) (h : aconn Q v₀ A B) :
    aconn Q v₀ (shV Q v₀ u A) (shV Q v₀ u B) := by
  induction h with
  | rel A B h =>
    obtain ⟨a, ha⟩ := h
    refine Relation.EqvGen.rel _ _ ⟨a, ?_⟩
    simp only [shV]
    rw [ha]
    exact grp_assoc (G := Deck Q v₀) _ _ _
  | refl A => exact Relation.EqvGen.refl _
  | symm A B _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans A B C _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

theorem aconn_arrow (A : V × Deck Q v₀) {X : V} (a : A.1 ⟶ X) :
    aconn Q v₀ A (X, A.2 * dg Q v₀ a) := Relation.EqvGen.rel _ _ ⟨a, rfl⟩

theorem aconn_path {Y X : V} (p : Quiver.Path Y X) (v : Deck Q v₀) :
    aconn Q v₀ (Y, v) (X, v * (degW Q v₀).deg p) := by
  induction p with
  | nil =>
    have e : v * (degW Q v₀).deg (Quiver.Path.nil : Quiver.Path Y Y) = v := by
      rw [(degW Q v₀).deg_nil]; exact grp_shift1 (G := Deck Q v₀) v
    rw [e]; exact Relation.EqvGen.refl _
  | cons p a ih =>
    have e : v * (degW Q v₀).deg (p.cons a) = v * (degW Q v₀).deg p * dg Q v₀ a := by
      rw [deg_cons]; exact grp_assoc (G := Deck Q v₀) _ _ _
    rw [e]
    exact Relation.EqvGen.trans _ _ _ ih (aconn_arrow (_, v * (degW Q v₀).deg p) a)

section Lift

variable (hF : IsRepresentationFinite k (Alg D.F0)ᵐᵒᵖ) (x₀ : D.PV)
  (hK : ∀ X : V, ∃ g, aconn Q v₀ (x₀.1, 1) (X, g))

/-- The base lift of each label. -/
def gK (X : V) : Deck Q v₀ := Classical.choose (hK X)

theorem gK_spec (X : V) : aconn Q v₀ (x₀.1, 1) (X, gK x₀ hK X) := Classical.choose_spec (hK X)

theorem inK_diff {X : V} {g g' : Deck Q v₀} (h : aconn Q v₀ (x₀.1, 1) (X, g))
    (h' : aconn Q v₀ (x₀.1, 1) (X, g')) : aconn Q v₀ (x₀.1, 1) (x₀.1, g' * g⁻¹) := by
  have := aconn_shV (g' * g⁻¹) h
  simp only [shV] at this
  rw [grp_shift1 (G := Deck Q v₀), grp_conj (G := Deck Q v₀)] at this
  exact Relation.EqvGen.trans _ _ _ h' (Relation.EqvGen.symm _ _ this)

variable {hF x₀ hK} (h : WP Q c v₀ D →+ M)

theorem hwt_isAddWeight : Thin.IsAddWeight Set.univ (fun o o' : LObj Q c v₀ D ↦ h (wtL Q c v₀ D o o')) :=
  ⟨fun o ho o' ho' o'' ho'' f g hfg ↦ by
    rw [wtL_isAddWeight.mul o ho o' ho' o'' ho'' f g hfg, map_add]⟩

theorem b_shift {b : LObj Q c v₀ D → M}
    (hb : ∀ o o', Thin.Line o o' → h (wtL Q c v₀ D o o') = b o' - b o)
    (u : Deck Q v₀) {o o' : LObj Q c v₀ D} (hc : conn Q c v₀ D o o') :
    b (gL Q c v₀ D u o') - b (gL Q c v₀ D u o) = b o' - b o := by
  induction hc with
  | rel a d hl => rw [← hb _ _ hl, ← hb _ _ (line_gL u hl), wtL_gL]
  | refl a => simp
  | symm a d _ ih => rw [← neg_sub, ih, neg_sub]
  | trans a d e _ _ ih ih' =>
    rw [show b (gL Q c v₀ D u e) - b (gL Q c v₀ D u a) =
      (b (gL Q c v₀ D u e) - b (gL Q c v₀ D u d)) + (b (gL Q c v₀ D u d) - b (gL Q c v₀ D u a))
      by abel, ih, ih']
    abel

include hF hK in
/-- **Lemma 7.4, surjectivity**: every ray weight is the restriction of a mesh weight. -/
theorem exists_meshWt_lift : ∃ W : MeshWt Q M, W.res c D = h := by
  classical
  obtain ⟨b, hb⟩ := L_addWeight_eq_diff hF _ (hwt_isAddWeight h)
  set g₀ := gK x₀ hK
  let γ : Deck Q v₀ → M := fun u ↦ b (toL Q c v₀ D (x₀, u)) - b (toL Q c v₀ D (x₀, 1))
  have hγ1 : γ 1 = 0 := sub_self _
  have hγmul : ∀ u v, aconn Q v₀ (x₀.1, 1) (x₀.1, v) → γ (u * v) = γ u + γ v := by
    intro u v hv
    have hc := conn_of_aconn (D := D) (p := x₀) (q := x₀) hv
    have hs := b_shift h hb u hc
    have e1 : gL Q c v₀ D u (toL Q c v₀ D (x₀, v)) = toL Q c v₀ D (x₀, u * v) := rfl
    have e2 : gL Q c v₀ D u (toL Q c v₀ D (x₀, 1)) = toL Q c v₀ D (x₀, u) := by
      show toL Q c v₀ D (x₀, u * 1) = _
      rw [grp_shift1 (G := Deck Q v₀)]
    rw [e1, e2] at hs
    simp only [γ]
    rw [show b (toL Q c v₀ D (x₀, u * v)) - b (toL Q c v₀ D (x₀, 1)) =
      (b (toL Q c v₀ D (x₀, u * v)) - b (toL Q c v₀ D (x₀, u))) +
        (b (toL Q c v₀ D (x₀, u)) - b (toL Q c v₀ D (x₀, 1))) by abel, hs]
    abel
  -- projective lifts
  have hproj : ∀ (p : D.PV) (g : Deck Q v₀),
      b (toL Q c v₀ D (p, g)) = b (toL Q c v₀ D (p, g₀ p.1)) + γ (g * (g₀ p.1)⁻¹) := by
    intro p g
    have hc := conn_of_aconn (D := D) (p := x₀) (q := p) (gK_spec x₀ hK p.1)
    have hs := b_shift h hb (g * (g₀ p.1)⁻¹) hc
    have e1 : gL Q c v₀ D (g * (g₀ p.1)⁻¹) (toL Q c v₀ D (p, g₀ p.1)) = toL Q c v₀ D (p, g) := by
      show toL Q c v₀ D (p, g * (g₀ p.1)⁻¹ * g₀ p.1) = _
      rw [grp_cancel_r (G := Deck Q v₀)]
    have e2 : gL Q c v₀ D (g * (g₀ p.1)⁻¹) (toL Q c v₀ D (x₀, 1)) =
        toL Q c v₀ D (x₀, g * (g₀ p.1)⁻¹) := by
      show toL Q c v₀ D (x₀, g * (g₀ p.1)⁻¹ * 1) = _
      rw [grp_shift1 (G := Deck Q v₀)]
    rw [e1, e2] at hs
    simp only [γ]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at hs
    rw [← hs]
    abel
  let ζ₀ : V → M := fun X ↦ if hX : D.proj X then b (toL Q c v₀ D (⟨X, hX⟩, g₀ X)) else 0
  let ζ : V × Deck Q v₀ → M := fun A ↦ ζ₀ A.1 + γ (A.2 * (g₀ A.1)⁻¹)
  have hζproj : ∀ (p : D.PV) (g : Deck Q v₀), ζ (p.1, g) = b (toL Q c v₀ D (p, g)) := by
    intro p g
    simp only [ζ, ζ₀, dif_pos p.2, hproj p g]
  -- equivariance along arrows
  have hinK : ∀ {X : V} {v : Deck Q v₀}, aconn Q v₀ (x₀.1, 1) (X, v) →
      aconn Q v₀ (x₀.1, 1) (x₀.1, v * (g₀ X)⁻¹) := fun h' ↦ inK_diff x₀ (gK_spec x₀ hK _) h'
  have harrow : ∀ {Y X : V} (a : Y ⟶ X) {v : Deck Q v₀}, aconn Q v₀ (x₀.1, 1) (Y, v) →
      ζ (X, v * dg Q v₀ a) - ζ (Y, v) =
        ζ (X, g₀ Y * dg Q v₀ a) - ζ (Y, g₀ Y) := by
    intro Y X a v hv
    have hYa : aconn Q v₀ (x₀.1, 1) (X, g₀ Y * dg Q v₀ a) :=
      Relation.EqvGen.trans _ _ _ (gK_spec x₀ hK Y) (aconn_arrow (Y, g₀ Y) a)
    have e1 : v * dg Q v₀ a * (g₀ X)⁻¹ = v * (g₀ Y)⁻¹ * (g₀ Y * dg Q v₀ a * (g₀ X)⁻¹) :=
      grp_split (G := Deck Q v₀) _ _ _ _
    have e2 : g₀ Y * (g₀ Y)⁻¹ = (1 : Deck Q v₀) := mul_inv_cancel (G := Deck Q v₀) _
    simp only [ζ]
    rw [e1, hγmul _ _ (hinK hYa), e2, hγ1]
    abel
  -- the mesh weight
  let W : MeshWt Q M :=
    { w := fun {Y X} a ↦ ζ (X, g₀ Y * dg Q v₀ a) - ζ (Y, g₀ Y)
      ν := fun x ↦ ζ (x.1, g₀ (Q.tau x).1 * tdeg x) - ζ ((Q.tau x).1, g₀ (Q.tau x).1)
      mesh := fun x a ↦ by
        have hv : aconn Q v₀ (x₀.1, 1) (a.1, g₀ (Q.tau x).1 * dg Q v₀ (Q.mate x a.1 a.2)) :=
          Relation.EqvGen.trans _ _ _ (gK_spec x₀ hK _) (aconn_arrow _ _)
        have h2 := harrow a.2 hv
        have e : g₀ (Q.tau x).1 * dg Q v₀ (Q.mate x a.1 a.2) * dg Q v₀ a.2 =
            g₀ (Q.tau x).1 * tdeg x := by
          rw [← dg_mesh x a]; exact (grp_assoc (G := Deck Q v₀) _ _ _).symm
        rw [e] at h2
        rw [← h2]
        abel }
  refine ⟨W, ?_⟩
  -- the restriction
  have hpath : ∀ {Y X : V} (p : Quiver.Path Y X) {v : Deck Q v₀},
      aconn Q v₀ (x₀.1, 1) (Y, v) → ζ (X, v * (degW Q v₀).deg p) - ζ (Y, v) = W.pw p := by
    intro Y X p
    induction p with
    | nil =>
      intro v _
      have e : v * (degW Q v₀).deg (Quiver.Path.nil : Quiver.Path Y Y) = v := by
        rw [(degW Q v₀).deg_nil]; exact grp_shift1 (G := Deck Q v₀) v
      rw [e, sub_self, MeshWt.pw]
    | cons p a ih =>
      intro v hv
      have e : v * (degW Q v₀).deg (p.cons a) = v * (degW Q v₀).deg p * dg Q v₀ a := by
        rw [deg_cons]; exact grp_assoc (G := Deck Q v₀) _ _ _
      have hv' := Relation.EqvGen.trans _ _ _ hv (aconn_path (v₀ := v₀) p v)
      rw [e, show ζ (_, v * (degW Q v₀).deg p * dg Q v₀ a) - ζ (Y, v) =
        (ζ (_, v * (degW Q v₀).deg p * dg Q v₀ a) - ζ (_, v * (degW Q v₀).deg p)) +
          (ζ (_, v * (degW Q v₀).deg p) - ζ (Y, v)) by abel, harrow a hv', ih hv]
      rw [MeshWt.pw]
      change _ = W.pw p + (ζ (_, g₀ _ * dg Q v₀ a) - ζ (_, g₀ _))
      abel
  refine QuotientAddGroup.addMonoidHom_ext _ (Finsupp.addHom_ext fun t n ↦ ?_)
  simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
  have hsingle : (QuotientAddGroup.mk (Finsupp.single t n) : WP Q c v₀ D) = n • cls Q c v₀ D t := by
    rw [cls, ← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hsingle, map_zsmul, map_zsmul, MeshWt.res_cls]
  congr 1
  obtain ⟨x, y, g⟩ := t
  by_cases ht : NZ Q c v₀ D (x, y, g)
  · obtain ⟨p, hp⟩ := exists_path_of_nz ht
    rw [W.rv_path ht hp, ← hpath p (gK_spec x₀ hK x.1), hp, hζproj, hζproj]
    have hl := line_of_nz ht (g₀ x.1)
    have := hb _ _ hl
    simp only [wtL] at this
    have e : (g₀ x.1)⁻¹ * (g₀ x.1 * g) = g := inv_mul_cancel_left (G := Deck Q v₀) _ _
    rw [e] at this
    rw [this]
    rfl
  · simp only [MeshWt.rv, if_neg ht]
    rw [cls_of_not_nz ht, map_zero]

theorem MeshWt.pw_of_diff (W : MeshWt Q M) {ζ : V → M}
    (hζ : ∀ {y x : V} (a : y ⟶ x), W.w a = ζ x - ζ y) {Y X : V} (p : Quiver.Path Y X) :
    W.pw p = ζ X - ζ Y := by
  induction p with
  | nil => rw [MeshWt.pw, sub_self]
  | cons p a ih => rw [MeshWt.pw, ih, hζ]; abel

include hK in
/-- **Lemma 7.4, exactness in the middle**: a mesh weight restricts to zero exactly
when it is the difference of object values vanishing at the projectives. Every mesh
row is assumed to have an arrow (`hmid`), as in an Auslander–Reiten quiver. -/
theorem res_eq_zero_iff (hmid : ∀ x : Q.nonprojective, Nonempty (Σ y : V, y ⟶ x.1))
    (W : MeshWt Q M) :
    W.res (v₀ := v₀) c D = 0 ↔ ∃ ζ : V → M, (∀ p : D.PV, ζ p.1 = 0) ∧
      (∀ {y x : V} (a : y ⟶ x), W.w a = ζ x - ζ y) ∧
      ∀ x : Q.nonprojective, W.ν x = ζ x.1 - ζ (Q.tau x).1 := by
  classical
  constructor
  · intro hres
    set g₀ := gK x₀ hK
    -- constant along lines of `L`
    have hline : ∀ z z' : D.PV × Deck Q v₀, Thin.Line (toL Q c v₀ D z) (toL Q c v₀ D z') →
        W.pot v₀ (z'.1.1, z'.2) = W.pot v₀ (z.1.1, z.2) := by
      intro z z' hl
      obtain ⟨f, hf, hf0⟩ := line_iff.1 hl
      have hnz : NZ Q c v₀ D (z.1, z'.1, z.2⁻¹ * z'.2) := fun h0 ↦ hf0 (by
        have : f ∈ (D0 Q c v₀ D).part (z.2⁻¹ * z'.2) z.1 z'.1 := hf
        rw [h0] at this; exact this)
      obtain ⟨p, hp⟩ := exists_path_of_nz hnz
      have h1 := W.pot_path (v₀ := v₀) z.2 p
      have e : z.2 * (z.2⁻¹ * z'.2) = z'.2 := mul_inv_cancel_left (G := Deck Q v₀) _ _
      rw [hp, e] at h1
      have h2 := congrArg (fun φ ↦ φ (cls Q c v₀ D (z.1, z'.1, z.2⁻¹ * z'.2))) hres
      simp only [AddMonoidHom.zero_apply, MeshWt.res_cls, W.rv_path hnz hp] at h2
      rw [h1, h2, add_zero]
    have hconst : ∀ {o o' : LObj Q c v₀ D}, conn Q c v₀ D o o' →
        W.pot v₀ ((ofL Q c v₀ D o').1.1, (ofL Q c v₀ D o').2) =
          W.pot v₀ ((ofL Q c v₀ D o).1.1, (ofL Q c v₀ D o).2) := by
      intro o o' h
      induction h with
      | rel a d hl => exact hline (ofL Q c v₀ D a) (ofL Q c v₀ D d) hl
      | refl a => rfl
      | symm a d _ ih => exact ih.symm
      | trans a d e _ _ ih ih' => exact ih'.trans ih
    -- deck shifts by elements of the stabilizer act trivially on `K₀`
    have hδ : ∀ (u : Deck Q v₀) {A B : V × Deck Q v₀}, aconn Q v₀ A B →
        W.pot v₀ (shV Q v₀ u B) - W.pot v₀ B = W.pot v₀ (shV Q v₀ u A) - W.pot v₀ A := by
      intro u A B h
      induction h with
      | rel A B h =>
        obtain ⟨a, ha⟩ := h
        have e1 : shV Q v₀ u B = (B.1, u * A.2 * dg Q v₀ a) := by
          simp only [shV]; rw [ha]; exact Prod.ext rfl (grp_assoc (G := Deck Q v₀) _ _ _)
        have hB : W.pot v₀ B = W.pot v₀ A + W.w a := by
          have := W.pot_arrow (v₀ := v₀) A.2 a
          rw [← ha] at this
          exact this
        rw [e1, W.pot_arrow, hB]
        simp only [shV]
        abel
      | refl A => rfl
      | symm A B _ ih => exact ih.symm
      | trans A B C _ _ ih ih' => exact ih'.trans ih
    have hstab : ∀ {u : Deck Q v₀}, aconn Q v₀ (x₀.1, 1) (x₀.1, u) →
        ∀ {A : V × Deck Q v₀}, aconn Q v₀ (x₀.1, 1) A → W.pot v₀ (shV Q v₀ u A) = W.pot v₀ A := by
      intro u hu A hA
      have h1 := hδ u hA
      have e : shV Q v₀ u (x₀.1, 1) = (x₀.1, u) := by
        simp only [shV]; exact Prod.ext rfl (grp_shift1 (G := Deck Q v₀) u)
      rw [e] at h1
      have h2 := hconst (conn_of_aconn (D := D) (p := x₀) (q := x₀) hu)
      have h2' : W.pot v₀ (x₀.1, u) = W.pot v₀ (x₀.1, 1) := h2
      rw [h2', sub_self, sub_eq_zero] at h1
      exact h1
    have hmove : ∀ {X : V} {v : Deck Q v₀}, aconn Q v₀ (x₀.1, 1) (X, v) →
        W.pot v₀ (X, v) = W.pot v₀ (X, g₀ X) := by
      intro X v hv
      have hu := inK_diff x₀ (gK_spec x₀ hK X) hv
      have := hstab hu (gK_spec x₀ hK X)
      have e : shV Q v₀ (v * (g₀ X)⁻¹) (X, g₀ X) = (X, v) := by
        simp only [shV]; exact Prod.ext rfl (grp_cancel_r (G := Deck Q v₀) _ _)
      rw [e] at this
      exact this
    refine ⟨fun X ↦ W.pot v₀ (X, g₀ X) - W.pot v₀ (x₀.1, 1), fun p ↦ ?_, fun {y x} a ↦ ?_, fun x ↦ ?_⟩
    · have := hconst (conn_of_aconn (D := D) (p := x₀) (q := p) (gK_spec x₀ hK p.1))
      have h' : W.pot v₀ (p.1, g₀ p.1) = W.pot v₀ (x₀.1, 1) := this
      show W.pot v₀ (p.1, g₀ p.1) - W.pot v₀ (x₀.1, 1) = 0
      rw [h', sub_self]
    · have hv := Relation.EqvGen.trans _ _ _ (gK_spec x₀ hK y) (aconn_arrow (y, g₀ y) a)
      show W.w a = (W.pot v₀ (x, g₀ x) - W.pot v₀ (x₀.1, 1)) -
        (W.pot v₀ (y, g₀ y) - W.pot v₀ (x₀.1, 1))
      rw [← hmove hv, W.pot_arrow]
      abel
    · obtain ⟨a⟩ := hmid x
      have hv := Relation.EqvGen.trans _ _ _ (gK_spec x₀ hK (Q.tau x).1)
        (aconn_arrow ((Q.tau x).1, g₀ (Q.tau x).1) (Q.mate x a.1 a.2))
      have hv' := Relation.EqvGen.trans _ _ _ hv (aconn_arrow _ a.2)
      have e : g₀ (Q.tau x).1 * dg Q v₀ (Q.mate x a.1 a.2) * dg Q v₀ a.2 =
          g₀ (Q.tau x).1 * tdeg x := by
        rw [← dg_mesh x a]; exact (grp_assoc (G := Deck Q v₀) _ _ _).symm
      have hv'' : aconn Q v₀ (x₀.1, 1) (x.1, g₀ (Q.tau x).1 * tdeg x) := by
        rw [← e]; exact hv'
      have ht := W.pot_t (v₀ := v₀) (g₀ (Q.tau x).1) x
      rw [hmove hv''] at ht
      show W.ν x = (W.pot v₀ (x.1, g₀ x.1) - W.pot v₀ (x₀.1, 1)) -
        (W.pot v₀ ((Q.tau x).1, g₀ (Q.tau x).1) - W.pot v₀ (x₀.1, 1))
      rw [ht]
      abel
  · rintro ⟨ζ, hζ0, hζ, -⟩
    refine QuotientAddGroup.addMonoidHom_ext _ (Finsupp.addHom_ext fun t n ↦ ?_)
    simp only [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, AddMonoidHom.zero_apply]
    have hsingle : (QuotientAddGroup.mk (Finsupp.single t n) : WP Q c v₀ D) = n • cls Q c v₀ D t := by
      rw [cls, ← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, map_zsmul, MeshWt.res_cls]
    obtain ⟨x, y, g⟩ := t
    by_cases ht : NZ Q c v₀ D (x, y, g)
    · obtain ⟨p, hp⟩ := exists_path_of_nz ht
      rw [W.rv_path ht hp, W.pw_of_diff hζ, hζ0, hζ0, sub_self, smul_zero]
    · simp only [MeshWt.rv, if_neg ht, smul_zero]

include hK in
/-- **Lemma 7.4, injectivity on the left**: object values vanishing at the projectives
are determined by their differences along arrows. -/
theorem eq_zero_of_diff (ζ : V → M) (h0 : ∀ p : D.PV, ζ p.1 = 0)
    (harr : ∀ {y x : V} (_ : y ⟶ x), ζ x = ζ y) : ζ = 0 := by
  funext X
  have key : ∀ {A B : V × Deck Q v₀}, aconn Q v₀ A B → ζ B.1 = ζ A.1 := by
    intro A B h
    induction h with
    | rel A B h => obtain ⟨a, -⟩ := h; exact harr a
    | refl A => rfl
    | symm A B _ ih => exact ih.symm
    | trans A B C _ _ ih ih' => exact ih'.trans ih
  obtain ⟨g, hg⟩ := hK X
  rw [Pi.zero_apply, key hg]
  exact h0 x₀

end Lift

end MeshWalk

end MultiplicativeBasisDeformations
