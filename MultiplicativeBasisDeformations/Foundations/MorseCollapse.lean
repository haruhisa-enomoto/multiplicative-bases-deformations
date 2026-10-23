module

public import MultiplicativeBasisDeformations.Foundations.FreeGroupoidVertex

/-!
# Collapsing a 2-complex along an acyclic matching

Combinatorial tool for Lemma 4.2 (`lem:mesh-walk-free`,
`scalar-normalization.tex`). A 2-complex is given by edges `Ed` with
endpoints and triangles `t` with relation `f_t g_t = h_t`; its fundamental
groupoid `Π` is the free groupoid on the edges modulo these relations. Given
an injective choice of one edge per triangle (a matching) with a potential
strictly decreasing from a triangle to the triangles matching its other
edges, each matched edge is expressed through the remaining ones — the
source's "eliminate these edges and triangles from one end of the chain" —
and `Π` is isomorphic to the free groupoid on the unmatched edges.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.Morse

variable {V : Type} {Ed : Type} (src tgt : Ed → V)

/-- The quiver on `V` whose arrows are the edges. -/
@[nolint unusedArguments]
def EQ (_src _tgt : Ed → V) : Type := V

instance : Quiver (EQ src tgt) where
  Hom X Y := {e : Ed // src e = X ∧ tgt e = Y}

/-- The free groupoid on the edges. -/
abbrev FG := Quiver.FreeGroupoid (EQ src tgt)

/-- A vertex as an object of the free groupoid. -/
abbrev ob (X : V) : FG src tgt := (Quiver.FreeGroupoid.of (EQ src tgt)).obj X

/-- An edge as a morphism of the free groupoid. -/
abbrev ofE (e : Ed) : ob src tgt (src e) ⟶ ob src tgt (tgt e) :=
  (Quiver.FreeGroupoid.of (EQ src tgt)).map
    (show @Quiver.Hom (EQ src tgt) _ (src e) (tgt e) from ⟨e, rfl, rfl⟩)

/-- Triangles `f g = h`. -/
structure Tris where
  T : Type
  f : T → Ed
  g : T → Ed
  h : T → Ed
  hfg : ∀ t, tgt (f t) = src (g t)
  hfh : ∀ t, src (f t) = src (h t)
  hgh : ∀ t, tgt (g t) = tgt (h t)

variable {src tgt} (S : Tris src tgt)

/-- The triangle relations. -/
inductive TriRel : HomRel (FG src tgt)
  | tri (t : S.T) : TriRel (ofE src tgt (S.f t) ≫ eqToHom (congrArg (ob src tgt) (S.hfg t)) ≫
      ofE src tgt (S.g t))
      (eqToHom (congrArg (ob src tgt) (S.hfh t)) ≫ ofE src tgt (S.h t) ≫
        eqToHom (congrArg (ob src tgt) (S.hgh t).symm))

/-- The fundamental groupoid of the 2-complex. -/
abbrev Pi := CategoryTheory.Quotient (TriRel S)

/-- The three edges of a triangle. -/
def Tris.edge (t : S.T) : Fin 3 → Ed
  | 0 => S.f t
  | 1 => S.g t
  | 2 => S.h t

/-- An acyclic matching: one edge per triangle, injectively, with a potential
decreasing from a triangle to the triangles matching its other edges. -/
structure Matching where
  m : S.T → Fin 3
  inj : Function.Injective fun t ↦ S.edge t (m t)
  pot : S.T → ℕ
  dec : ∀ t (i : Fin 3), i ≠ m t → ∀ t', S.edge t' (m t') = S.edge t i → pot t' < pot t

variable {S} (M : Matching S)

/-- An edge is matched if it is the chosen edge of a triangle. -/
def Matched (e : Ed) : Prop := ∃ t, S.edge t (M.m t) = e

/-- The quiver of unmatched edges. -/
@[nolint unusedArguments]
def UQ (_M : Matching S) : Type := V

instance : Quiver (UQ M) where
  Hom X Y := {e : Ed // src e = X ∧ tgt e = Y ∧ ¬ Matched M e}

/-- The free groupoid on the unmatched edges. -/
abbrev FGU := Quiver.FreeGroupoid (UQ M)

/-- A vertex as an object of `FGU`. -/
abbrev obU (X : V) : FGU M := (Quiver.FreeGroupoid.of (UQ M)).obj X

/-- An unmatched edge as a morphism of `FGU`. -/
abbrev ofU (e : Ed) (he : ¬ Matched M e) : obU M (src e) ⟶ obU M (tgt e) :=
  (Quiver.FreeGroupoid.of (UQ M)).map
    (show @Quiver.Hom (UQ M) _ (src e) (tgt e) from ⟨e, rfl, rfl, he⟩)

open Classical in
/-- The recursion measure. -/
def μ (e : Ed) : ℕ := if h : Matched M e then M.pot (Classical.choose h) + 1 else 0

theorem μ_lt_of_other {e : Ed} (h : Matched M e) (i : Fin 3)
    (hi : i ≠ M.m (Classical.choose h)) : μ M (S.edge (Classical.choose h) i) < μ M e := by
  classical
  have hμe : μ M e = M.pot (Classical.choose h) + 1 := by rw [μ, dif_pos h]
  rw [hμe, μ]
  split_ifs with h'
  · have := M.dec _ i hi _ (Classical.choose_spec h')
    omega
  · omega

/-- The type of values of an edge in `FGU`. -/
abbrev Val (e : Ed) := obU M (src e) ⟶ obU M (tgt e)

open Classical in
/-- The value of an edge, given values on the triangles of smaller potential. -/
def edgeVal (e : Ed) (bound : ℕ) (rec : ∀ t', M.pot t' < bound → Val M (S.edge t' (M.m t')))
    (hb : ∀ t', S.edge t' (M.m t') = e → M.pot t' < bound) : Val M e :=
  if h : Matched M e then
    (Classical.choose_spec h) ▸ rec (Classical.choose h) (hb _ (Classical.choose_spec h))
  else ofU M e h

/-- The value of the matched edge `i` of `t` through the other two edges. -/
def triVal (t : S.T) : ∀ (i : Fin 3), i = M.m t → (∀ j, j ≠ M.m t → Val M (S.edge t j)) →
    Val M (S.edge t i)
  | 0, hi, other => eqToHom (congrArg (obU M) (S.hfh t)) ≫ other 2 (by rw [← hi]; decide) ≫
      eqToHom (congrArg (obU M) (S.hgh t).symm) ≫
      Groupoid.inv (other 1 (by rw [← hi]; decide)) ≫ eqToHom (congrArg (obU M) (S.hfg t).symm)
  | 1, hi, other => eqToHom (congrArg (obU M) (S.hfg t).symm) ≫
      Groupoid.inv (other 0 (by rw [← hi]; decide)) ≫
      eqToHom (congrArg (obU M) (S.hfh t)) ≫ other 2 (by rw [← hi]; decide) ≫
      eqToHom (congrArg (obU M) (S.hgh t).symm)
  | 2, hi, other => eqToHom (congrArg (obU M) (S.hfh t).symm) ≫ other 0 (by rw [← hi]; decide) ≫
      eqToHom (congrArg (obU M) (S.hfg t)) ≫ other 1 (by rw [← hi]; decide) ≫
      eqToHom (congrArg (obU M) (S.hgh t))

/-- The values of the matched edges, by recursion on the potential. -/
def ψ : ∀ t : S.T, Val M (S.edge t (M.m t)) :=
  (measure M.pot).wf.fix fun t rec ↦
    triVal M t (M.m t) rfl fun i hi ↦ edgeVal M (S.edge t i) (M.pot t) (fun t' h' ↦ rec t' h')
      (fun t' ht' ↦ M.dec t i hi t' ht')

theorem ψ_eq (t : S.T) :
    ψ M t = triVal M t (M.m t) rfl fun i hi ↦ edgeVal M (S.edge t i) (M.pot t)
      (fun t' _ ↦ ψ M t') (fun t' ht' ↦ M.dec t i hi t' ht') := by
  rw [ψ, WellFounded.fix_eq]

open Classical in
/-- The value of an arbitrary edge. -/
def φ (e : Ed) : Val M e :=
  if h : Matched M e then (Classical.choose_spec h) ▸ ψ M (Classical.choose h) else ofU M e h

/-- `edgeVal` agrees with `φ`. -/
theorem edgeVal_eq (e : Ed) (bound : ℕ) (hb : ∀ t', S.edge t' (M.m t') = e → M.pot t' < bound) :
    edgeVal M e bound (fun t' _ ↦ ψ M t') hb = φ M e := by
  classical
  unfold edgeVal φ
  split_ifs <;> rfl

/-- `φ` at the matched edge of `t` is `ψ t`. -/
theorem φ_matched (t : S.T) : φ M (S.edge t (M.m t)) = ψ M t := by
  classical
  have h : Matched M (S.edge t (M.m t)) := ⟨t, rfl⟩
  have key : ∀ t' (ht' : S.edge t' (M.m t') = S.edge t (M.m t)), (ht' ▸ ψ M t' :
      Val M (S.edge t (M.m t))) = ψ M t := by
    intro t' ht'
    have := M.inj ht'
    subst this
    rfl
  unfold φ
  rw [dif_pos h]
  exact key _ _

theorem φ_unmatched (e : Ed) (h : ¬ Matched M e) : φ M e = ofU M e h := by
  classical
  unfold φ
  rw [dif_neg h]

theorem φ_tri (t : S.T) (i : Fin 3) (hi : i = M.m t) :
    φ M (S.edge t i) = triVal M t i hi fun j _ ↦ φ M (S.edge t j) := by
  subst hi
  rw [φ_matched, ψ_eq]
  congr 1

theorem φ_f (t : S.T) (h0 : M.m t = 0) :
    φ M (S.f t) = eqToHom (congrArg (obU M) (S.hfh t)) ≫ φ M (S.h t) ≫
      eqToHom (congrArg (obU M) (S.hgh t).symm) ≫ Groupoid.inv (φ M (S.g t)) ≫
      eqToHom (congrArg (obU M) (S.hfg t).symm) :=
  φ_tri M t 0 h0.symm

theorem φ_g (t : S.T) (h1 : M.m t = 1) :
    φ M (S.g t) = eqToHom (congrArg (obU M) (S.hfg t).symm) ≫ Groupoid.inv (φ M (S.f t)) ≫
      eqToHom (congrArg (obU M) (S.hfh t)) ≫ φ M (S.h t) ≫
      eqToHom (congrArg (obU M) (S.hgh t).symm) :=
  φ_tri M t 1 h1.symm

theorem φ_h (t : S.T) (h2 : M.m t = 2) :
    φ M (S.h t) = eqToHom (congrArg (obU M) (S.hfh t).symm) ≫ φ M (S.f t) ≫
      eqToHom (congrArg (obU M) (S.hfg t)) ≫ φ M (S.g t) ≫
      eqToHom (congrArg (obU M) (S.hgh t)) :=
  φ_tri M t 2 h2.symm

/-- **The triangle relations hold in `FGU`.** -/
theorem φ_rel (t : S.T) :
    φ M (S.f t) ≫ eqToHom (congrArg (obU M) (S.hfg t)) ≫ φ M (S.g t) =
      eqToHom (congrArg (obU M) (S.hfh t)) ≫ φ M (S.h t) ≫
        eqToHom (congrArg (obU M) (S.hgh t).symm) := by
  rcases h : M.m t with ⟨i, hi⟩
  interval_cases i
  · rw [φ_f M t h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Groupoid.inv_comp, Category.comp_id]
  · rw [φ_g M t h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (φ M (S.f t)), Groupoid.comp_inv, Category.id_comp]
  · rw [φ_h M t h]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      eqToHom_trans, Category.comp_id]

/-- The prefunctor sending an edge to its value. -/
def Φ0 : EQ src tgt ⥤q FGU M where
  obj X := obU M X
  map {X Y} a := eqToHom (congrArg (obU M) a.2.1.symm) ≫ φ M a.1 ≫ eqToHom (congrArg (obU M) a.2.2)

/-- Its extension to the free groupoid. -/
def Φ1 : FG src tgt ⥤ FGU M := Quiver.FreeGroupoid.lift (Φ0 M)

theorem Φ1_obj (X : V) : (Φ1 M).obj (ob src tgt X) = obU M X := rfl

theorem Φ1_ofE (e : Ed) : (Φ1 M).map (ofE src tgt e) = φ M e := by
  have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (Φ0 M))
    (show @Quiver.Hom (EQ src tgt) _ (src e) (tgt e) from ⟨e, rfl, rfl⟩)
  have h' := eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))
  change (Φ1 M).map (ofE src tgt e) = _ at h'
  rw [h']
  simp [Φ0]
  rfl

theorem Φ1_rel : ∀ (X Y : FG src tgt) (f₁ f₂ : X ⟶ Y), TriRel S f₁ f₂ →
    (Φ1 M).map f₁ = (Φ1 M).map f₂ := by
  rintro _ _ _ _ ⟨t⟩
  simp only [Functor.map_comp, eqToHom_map, Φ1_ofE]
  exact φ_rel M t

/-- **The collapse functor** `Π → FGU`. -/
def Φ : Pi S ⥤ FGU M := CategoryTheory.Quotient.lift _ (Φ1 M) (Φ1_rel M)

/-- The inclusion of the unmatched edges, as a prefunctor into `Π`. -/
def Ψ0 : UQ M ⥤q Pi S where
  obj X := (CategoryTheory.Quotient.functor (TriRel S)).obj (ob src tgt X)
  map {X Y} a := (CategoryTheory.Quotient.functor (TriRel S)).map
    ((Quiver.FreeGroupoid.of (EQ src tgt)).map
      (show @Quiver.Hom (EQ src tgt) _ X Y from ⟨a.1, a.2.1, a.2.2.1⟩))

/-- The inclusion functor `FGU → Π`. -/
def Ψ : FGU M ⥤ Pi S := Quiver.FreeGroupoid.lift (Ψ0 M)

theorem Ψ_ofU (e : Ed) (he : ¬ Matched M e) :
    (Ψ M).map (ofU M e he) = (CategoryTheory.Quotient.functor (TriRel S)).map (ofE src tgt e) := by
  have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (Ψ0 M))
    (show @Quiver.Hom (UQ M) _ (src e) (tgt e) from ⟨e, rfl, rfl, he⟩)
  have h' := eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))
  exact h'


theorem eqToHom_sandwich {C : Type*} [Category C] {X X' Y Y' : C} (p : X = X') (q : X' = X)
    (f : X ⟶ Y) (r : Y = Y') (s : Y' = Y) :
    eqToHom p ≫ eqToHom q ≫ f ≫ eqToHom r ≫ eqToHom s = f := by
  subst p r; simp

theorem eqToHom_conj_self {C : Type*} [Category C] {X Y : C} (p : X = X) (q : Y = Y)
    (f : X ⟶ Y) : eqToHom p ≫ f ≫ eqToHom q = f := by simp

/-- The quotient functor onto `Π`. -/
abbrev Qf := CategoryTheory.Quotient.functor (TriRel S)

theorem Q_rel (t : S.T) :
    (Qf (S := S)).map (ofE src tgt (S.f t)) ≫ eqToHom (by rw [S.hfg t]) ≫
        (Qf (S := S)).map (ofE src tgt (S.g t)) =
      eqToHom (by rw [S.hfh t]) ≫ (Qf (S := S)).map (ofE src tgt (S.h t)) ≫
        eqToHom (by rw [S.hgh t]) := by
  have := CategoryTheory.Quotient.sound (TriRel S) (TriRel.tri t)
  simp only [Functor.map_comp, eqToHom_map] at this
  exact this

theorem Ψ_φ (e : Ed) : (Ψ M).map (φ M e) = (Qf (S := S)).map (ofE src tgt e) := by
  classical
  -- strong induction on the potential of the matching triangle
  suffices H : ∀ n, ∀ e, (∀ t', S.edge t' (M.m t') = e → M.pot t' < n) →
      (Ψ M).map (φ M e) = (Qf (S := S)).map (ofE src tgt e) by
    by_cases h : Matched M e
    · obtain ⟨t, ht⟩ := h
      exact H (M.pot t + 1) e fun t' ht' ↦ by rw [M.inj (ht'.trans ht.symm)]; omega
    · exact H 0 e fun t' ht' ↦ absurd ⟨t', ht'⟩ h
  intro n
  induction n with
  | zero =>
      intro e he
      have hu : ¬ Matched M e := fun ⟨t', ht'⟩ ↦ by have := he t' ht'; omega
      rw [φ_unmatched M e hu, Ψ_ofU]
  | succ n ih =>
      intro e he
      by_cases hm : Matched M e
      swap
      · rw [φ_unmatched M e hm, Ψ_ofU]
      obtain ⟨t, rfl⟩ := hm
      have hpt := he t rfl
      have hother : ∀ i, i ≠ M.m t →
          (Ψ M).map (φ M (S.edge t i)) = (Qf (S := S)).map (ofE src tgt (S.edge t i)) := by
        intro i hi
        exact ih _ fun t' ht' ↦ by have := M.dec t i hi t' ht'; omega
      rcases hmt : M.m t with ⟨i, hi⟩
      interval_cases i
      · have h1 := hother 1 (by rw [hmt]; intro h; simp at h)
        have h2 := hother 2 (by rw [hmt]; intro h; simp at h)
        change (Ψ M).map (φ M (S.g t)) = _ at h1
        change (Ψ M).map (φ M (S.h t)) = _ at h2
        change (Ψ M).map (φ M (S.f t)) = (Qf (S := S)).map (ofE src tgt (S.f t))
        rw [φ_f M t hmt]
        simp only [Functor.map_comp, eqToHom_map, Groupoid.inv_eq_inv, Functor.map_inv, h1, h2]
        have hrel := Q_rel (S := S) t
        rw [(IsIso.eq_comp_inv _).2 hrel]
        simp
        rfl
      · have h0 := hother 0 (by rw [hmt]; intro h; simp at h)
        have h2 := hother 2 (by rw [hmt]; intro h; simp at h)
        change (Ψ M).map (φ M (S.f t)) = _ at h0
        change (Ψ M).map (φ M (S.h t)) = _ at h2
        change (Ψ M).map (φ M (S.g t)) = (Qf (S := S)).map (ofE src tgt (S.g t))
        rw [φ_g M t hmt]
        simp only [Functor.map_comp, eqToHom_map, Groupoid.inv_eq_inv, Functor.map_inv, h0, h2]
        have hrel := Q_rel (S := S) t
        rw [← Category.assoc] at hrel
        rw [(IsIso.eq_inv_comp _).2 hrel]
        simp
        rfl
      · have h0 := hother 0 (by rw [hmt]; intro h; simp at h)
        have h1 := hother 1 (by rw [hmt]; intro h; simp at h)
        change (Ψ M).map (φ M (S.f t)) = _ at h0
        change (Ψ M).map (φ M (S.g t)) = _ at h1
        change (Ψ M).map (φ M (S.h t)) = (Qf (S := S)).map (ofE src tgt (S.h t))
        rw [φ_h M t hmt]
        simp only [Functor.map_comp, eqToHom_map, h0, h1]
        have hrel := Q_rel (S := S) t
        change eqToHom _ ≫ (Qf (S := S)).map (ofE src tgt (S.f t)) ≫ eqToHom _ ≫
          (Qf (S := S)).map (ofE src tgt (S.g t)) ≫ eqToHom _ = _
        rw [reassoc_of% hrel]
        exact eqToHom_sandwich _ _ _ _ _

theorem Φ_Qf_map {X Y : FG src tgt} (f : X ⟶ Y) : (Φ M).map ((Qf (S := S)).map f) = (Φ1 M).map f :=
  rfl

theorem ΨΦ : Ψ M ⋙ Φ M = 𝟭 (FGU M) := by
  have h1 : Ψ M ⋙ Φ M = Quiver.FreeGroupoid.lift (Quiver.FreeGroupoid.of (UQ M)) := by
    apply Quiver.FreeGroupoid.lift_unique
    refine Prefunctor.ext (fun X ↦ rfl) fun X Y a ↦ ?_
    obtain ⟨e, hs, ht, hu⟩ := a
    subst hs ht
    have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec (Ψ0 M))
      (show @Quiver.Hom (UQ M) _ (src e) (tgt e) from ⟨e, rfl, rfl, hu⟩)
    have h' := eq_of_heq ((Quiver.homOfEq_heq _ _ _).symm.trans (heq_of_eq h))
    change (Φ M).map ((Ψ M).map (ofU M e hu)) = ofU M e hu
    change (Ψ M).map (ofU M e hu) = (Qf (S := S)).map (ofE src tgt e) at h'
    rw [h']
    exact (Φ1_ofE M e).trans (φ_unmatched M e hu)
  have h2 : 𝟭 (FGU M) = Quiver.FreeGroupoid.lift (Quiver.FreeGroupoid.of (UQ M)) := by
    apply Quiver.FreeGroupoid.lift_unique
    rfl
  rw [h1, h2]

theorem ΦΨ : Φ M ⋙ Ψ M = 𝟭 (Pi S) := by
  have key : Qf (S := S) ⋙ Φ M ⋙ Ψ M = Qf (S := S) := by
    have e1 : Qf (S := S) ⋙ Φ M ⋙ Ψ M = Quiver.FreeGroupoid.lift
        (Quiver.FreeGroupoid.of (EQ src tgt) ⋙q (Qf (S := S)).toPrefunctor) := by
      apply Quiver.FreeGroupoid.lift_unique
      refine Prefunctor.ext (fun X ↦ rfl) fun X Y a ↦ ?_
      obtain ⟨e, hs, ht⟩ := a
      subst hs ht
      change (Ψ M).map ((Φ M).map ((Qf (S := S)).map (ofE src tgt e))) =
        (Qf (S := S)).map (ofE src tgt e)
      change (Ψ M).map ((Φ1 M).map (ofE src tgt e)) = _
      rw [Φ1_ofE]
      exact Ψ_φ M e
    have e2 : Qf (S := S) = Quiver.FreeGroupoid.lift
        (Quiver.FreeGroupoid.of (EQ src tgt) ⋙q (Qf (S := S)).toPrefunctor) := by
      apply Quiver.FreeGroupoid.lift_unique
      rfl
    rw [e1, ← e2]
  have h1 := CategoryTheory.Quotient.lift_unique (TriRel S) (Qf (S := S) ⋙ Φ M ⋙ Ψ M)
    (fun X Y f₁ f₂ h ↦ by
      simp only [Functor.comp_map]
      rw [CategoryTheory.Quotient.sound _ h]) (Φ M ⋙ Ψ M) rfl
  have h2 := CategoryTheory.Quotient.lift_unique (TriRel S) (Qf (S := S))
    (fun X Y f₁ f₂ h ↦ CategoryTheory.Quotient.sound _ h) (𝟭 (Pi S)) (Functor.comp_id _)
  rw [h1, h2]
  congr 1

/-- **Collapse** on vertex groups: `π₁(K, X)` is the vertex group of the free
groupoid on the unmatched edges. -/
def endMulEquiv (X : V) : End ((Qf (S := S)).obj (ob src tgt X)) ≃* End (obU M X) where
  toFun f := (Φ M).map f
  invFun g := (Ψ M).map g
  left_inv f := by
    have := Functor.congr_hom (ΦΨ M) f
    simp only [Functor.comp_map, Functor.id_map] at this
    exact this.trans (eqToHom_conj_self _ _ _)
  right_inv g := by
    have := Functor.congr_hom (ΨΦ M) g
    simp only [Functor.comp_map, Functor.id_map] at this
    exact this.trans (eqToHom_conj_self _ _ _)
  map_mul' f g := (Φ M).map_comp g f

include M in
/-- **The vertex groups of a collapsible 2-complex are free.** -/
theorem isFreeGroup_end (X : V) : IsFreeGroup (End ((Qf (S := S)).obj (ob src tgt X))) :=
  have := FreeVertex.isFreeGroup_end (U := UQ M) X
  IsFreeGroup.ofMulEquiv (endMulEquiv M X).symm

end MultiplicativeBasisDeformations.Morse
