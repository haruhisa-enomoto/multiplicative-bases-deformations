module

public import MultiplicativeBasisDeformations.Foundations.SectionalTree

/-!
# The covering `ℤΔ → Q` of a periodic component

Proof of Proposition 4.1, Step 1 (`periodic-mesh-calculations.tex`):
"Define `π(p, j) = τ^{-j}(end p)`. ... At the root the children give all
outgoing arrows. At a nonroot path ending in `a`, the children give all
outgoing arrows except `σ^{-1} a`; the repetition edge towards the parent gives
that arrow. Thus `π` is bijective on outgoing stars, and mates give the same
conclusion on incoming stars."

In height coordinates the vertex `(p, t)` of `ℤΔ` has `t = 2j + |p|`, and
`π(p, t) = τ^{-j}(end p)`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Function

namespace MultiplicativeBasisDeformations

universe u v w v' w'

section Subsingleton

variable {W : Type v'} [Quiver.{w'} W] {V : Type v} [Quiver.{w} V]
  [∀ x y : W, Subsingleton (x ⟶ y)] [∀ x y : V, Subsingleton (x ⟶ y)] (φ : W ⥤q V)

/-- Bijectivity on outgoing stars, for quivers with at most one arrow between
two vertices. -/
theorem star_bijective_of {X : W}
    (hinj : ∀ {Y Y' : W}, Nonempty (X ⟶ Y) → Nonempty (X ⟶ Y') → φ.obj Y = φ.obj Y' → Y = Y')
    (hsurj : ∀ y : V, Nonempty (φ.obj X ⟶ y) → ∃ Y, Nonempty (X ⟶ Y) ∧ φ.obj Y = y) :
    Bijective (φ.star X) := by
  constructor
  · rintro ⟨Y, a⟩ ⟨Y', a'⟩ h
    simp only [Prefunctor.star_apply, Sigma.mk.inj_iff] at h
    obtain rfl := hinj ⟨a⟩ ⟨a'⟩ h.1
    exact congrArg _ (Subsingleton.elim a a')
  · rintro ⟨y, b⟩
    obtain ⟨Y, ⟨a⟩, rfl⟩ := hsurj y ⟨b⟩
    exact ⟨⟨Y, a⟩, by simp only [Prefunctor.star_apply]; exact congrArg _ (Subsingleton.elim _ _)⟩

/-- Bijectivity on incoming stars, for quivers with at most one arrow between
two vertices. -/
theorem costar_bijective_of {X : W}
    (hinj : ∀ {Y Y' : W}, Nonempty (Y ⟶ X) → Nonempty (Y' ⟶ X) → φ.obj Y = φ.obj Y' → Y = Y')
    (hsurj : ∀ y : V, Nonempty (y ⟶ φ.obj X) → ∃ Y, Nonempty (Y ⟶ X) ∧ φ.obj Y = y) :
    Bijective (φ.costar X) := by
  constructor
  · rintro ⟨Y, a⟩ ⟨Y', a'⟩ h
    simp only [Prefunctor.costar_apply, Sigma.mk.inj_iff] at h
    obtain rfl := hinj ⟨a⟩ ⟨a'⟩ h.1
    exact congrArg _ (Subsingleton.elim a a')
  · rintro ⟨y, b⟩
    obtain ⟨Y, ⟨a⟩, rfl⟩ := hsurj y ⟨b⟩
    exact ⟨⟨Y, a⟩, by simp only [Prefunctor.costar_apply]; exact congrArg _ (Subsingleton.elim _ _)⟩

theorem eq_of_star_bijective {X : W} (h : Bijective (φ.star X)) {Y Y' : W}
    (hY : Nonempty (X ⟶ Y)) (hY' : Nonempty (X ⟶ Y')) (he : φ.obj Y = φ.obj Y') : Y = Y' := by
  obtain ⟨a⟩ := hY
  obtain ⟨a'⟩ := hY'
  have : φ.star X ⟨Y, a⟩ = φ.star X ⟨Y', a'⟩ := by
    simp only [Prefunctor.star_apply]
    exact Sigma.ext he (Subsingleton.helim (congrArg _ he) _ _)
  exact congrArg Sigma.fst (h.1 this)

theorem exists_of_star_bijective {X : W} (h : Bijective (φ.star X)) {y : V}
    (hy : Nonempty (φ.obj X ⟶ y)) : ∃ Y, Nonempty (X ⟶ Y) ∧ φ.obj Y = y := by
  obtain ⟨b⟩ := hy
  obtain ⟨⟨Y, a⟩, h'⟩ := h.2 ⟨y, b⟩
  simp only [Prefunctor.star_apply, Sigma.mk.inj_iff] at h'
  exact ⟨Y, ⟨a⟩, h'.1⟩

theorem exists_of_costar_bijective {X : W} (h : Bijective (φ.costar X)) {y : V}
    (hy : Nonempty (y ⟶ φ.obj X)) : ∃ Y, Nonempty (Y ⟶ X) ∧ φ.obj Y = y := by
  obtain ⟨b⟩ := hy
  obtain ⟨⟨Y, a⟩, h'⟩ := h.2 ⟨y, b⟩
  simp only [Prefunctor.costar_apply, Sigma.mk.inj_iff] at h'
  exact ⟨Y, ⟨a⟩, h'.1⟩

end Subsingleton

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable)

/-- In a stable quiver with at most one arrow between two vertices, consecutive
arrows `u → e → w` form a mesh pair exactly when `u = τ w`. -/
theorem isMeshPair_iff {u e w : V} (a : u ⟶ e) (b : e ⟶ w) :
    Q.IsMeshPair ⟨u, e, a⟩ ⟨e, w, b⟩ ↔ u = hQ.tauE w := by
  constructor
  · rintro ⟨x, y, a', h1, h2⟩
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.1 h1
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.1 (eq_of_heq h1')
    obtain ⟨h3, -⟩ := Sigma.mk.inj_iff.1 h2
    rw [h3]
    rfl
  · intro h
    subst h
    refine ⟨⟨w, hQ.mem_nonprojective w⟩, e, b, rfl, ?_⟩
    exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _))))

namespace SecPath

variable {x₀ : V}

theorem not_isMeshPair_of_sectional {u e w : V} (p' : Quiver.Path x₀ u) (a : u ⟶ e) (b : e ⟶ w)
    (h : Q.IsSectional ((p'.cons a).cons b)) : ¬ Q.IsMeshPair ⟨u, e, a⟩ ⟨e, w, b⟩ := by
  unfold IsSectional at h
  simp only [Quiver.Path.arrowList_cons] at h
  have := h.infix (l₁ := [⟨u, e, a⟩, ⟨e, w, b⟩]) ⟨p'.arrowList, [], by simp⟩
  exact List.isChain_pair.1 this

theorem isSectional_cons {y w : V} (p : Quiver.Path x₀ y) (hp : Q.IsSectional p) (b : y ⟶ w)
    (hb : ∀ {u : V} (p' : Quiver.Path x₀ u) (a : u ⟶ y), p = p'.cons a →
      ¬ Q.IsMeshPair ⟨u, y, a⟩ ⟨y, w, b⟩) : Q.IsSectional (p.cons b) := by
  unfold IsSectional at hp ⊢
  rw [Quiver.Path.arrowList_cons, List.isChain_append]
  refine ⟨hp, List.isChain_singleton _, ?_⟩
  intro x hx z hz
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hz
  subst hz
  cases p with
  | nil => simp at hx
  | cons p' a =>
      simp only [Quiver.Path.arrowList_cons, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hb p' a rfl

end SecPath

namespace SecPath

variable (x₀ : V)

/-- The repetition coordinate `j` of a vertex `(p, t)` of `ℤΔ`, with
`t = 2j + |p|`. -/
def jco (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) : ℤ := (X.t - X.v.len) / 2

theorem two_mul_jco (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) :
    2 * jco x₀ X = X.t - X.v.len := by
  have h : (2 : ℤ) ∣ X.t - X.v.len := by
    have := X.ht
    change (X.t : ZMod 2) = ((X.v.len : ℤ) : ZMod 2) at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).1 this.symm
  exact Int.mul_ediv_cancel' h

/-- The covering map `π(p, t) = τ^{-j}(end p)`. -/
def piV (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) : V :=
  (hQ.tauE ^ (-jco x₀ X)) X.v.endv

theorem tauE_zpow_neg_sub_one (n : ℤ) (v : V) :
    (hQ.tauE ^ (-(n - 1))) v = hQ.tauE ((hQ.tauE ^ (-n)) v) := by
  rw [show -(n - 1) = 1 + -n by ring, zpow_add, zpow_one, Equiv.Perm.mul_apply]

theorem tauE_zpow_neg_add_one (n : ℤ) (v : V) :
    (hQ.tauE ^ (-n)) v = (hQ.tauE ^ (-(n + 1))) (hQ.tauE v) := by
  rw [← Equiv.Perm.mul_apply, ← zpow_add_one, show -(n + 1) + 1 = -n by ring]

variable {x₀}

theorem jco_child {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert} (h : IsParent X.v Y.v)
    (ht : Y.t = X.t + 1) : jco x₀ Y = jco x₀ X := by
  have h1 := two_mul_jco x₀ X
  have h2 := two_mul_jco x₀ Y
  have h3 := len_of_isParent h
  push_cast [h3] at h2
  omega

theorem jco_parent {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert} (h : IsParent Y.v X.v)
    (ht : Y.t = X.t + 1) : jco x₀ Y = jco x₀ X + 1 := by
  have h1 := two_mul_jco x₀ X
  have h2 := two_mul_jco x₀ Y
  have h3 := len_of_isParent h
  push_cast [h3] at h1
  omega

theorem endv_of_isParent {p q : Q.SecPath x₀} {w : V} {a : p.endv ⟶ w}
    (h : q.1 = ⟨w, p.1.2.cons a⟩) : q.endv = w := by
  unfold endv; rw [h]

/-- Arrows of `ℤΔ` map to arrows of `Q`. -/
theorem nonempty_piV {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert} (a : X ⟶ Y) :
    Nonempty (piV hQ x₀ X ⟶ piV hQ x₀ Y) := by
  obtain ⟨hadj, ht⟩ := a.down
  rcases hadj with h | h
  · have hj := jco_child h ht
    obtain ⟨w, b, hY⟩ := h
    unfold piV
    rw [hj, endv_of_isParent hY, hQ.nonempty_hom_zpow_iff]
    exact ⟨b⟩
  · have hj := jco_parent h ht
    obtain ⟨w, b, hX⟩ := h
    unfold piV
    rw [hj, tauE_zpow_neg_add_one hQ (jco x₀ X) X.v.endv, hQ.nonempty_hom_zpow_iff,
      endv_of_isParent hX, ← hQ.nonempty_hom_iff]
    exact ⟨b⟩

/-- The covering map `π : ℤΔ → Q`. -/
def piQ : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert ⥤q V where
  obj := piV hQ x₀
  map a := Classical.choice (nonempty_piV hQ a)

theorem piV_ztau (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) :
    piV hQ x₀ ((SecPath.tree (Q := Q) (x₀ := x₀)).ztau X) = hQ.tauE (piV hQ x₀ X) := by
  have : jco x₀ ((SecPath.tree (Q := Q) (x₀ := x₀)).ztau X) = jco x₀ X - 1 := by
    have h1 := two_mul_jco x₀ X
    have h2 := two_mul_jco x₀ ((SecPath.tree (Q := Q) (x₀ := x₀)).ztau X)
    change 2 * jco x₀ ((SecPath.tree (Q := Q) (x₀ := x₀)).ztau X) = (X.t - 2) - X.v.len at h2
    omega
  unfold piV
  rw [this, tauE_zpow_neg_sub_one]
  rfl

theorem piV_child {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert} {w : V} {b : X.v.endv ⟶ w}
    (hY : Y.v.1 = ⟨w, X.v.1.2.cons b⟩) (ht : Y.t = X.t + 1) :
    piV hQ x₀ Y = (hQ.tauE ^ (-jco x₀ X)) w := by
  unfold piV
  rw [jco_child ⟨w, b, hY⟩ ht, endv_of_isParent hY]

theorem piV_parent {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert} {e : V} {a : Y.v.endv ⟶ e}
    (hX : X.v.1 = ⟨e, Y.v.1.2.cons a⟩) (ht : Y.t = X.t + 1) :
    hQ.tauE (piV hQ x₀ Y) = (hQ.tauE ^ (-jco x₀ X)) Y.v.endv := by
  unfold piV
  rw [jco_parent ⟨e, a, hX⟩ ht, tauE_zpow_neg_add_one hQ (jco x₀ X), ← Equiv.Perm.mul_apply,
    ← Equiv.Perm.mul_apply]
  congr 1
  rw [← zpow_one_add, ← zpow_add_one]
  ring_nf

/-- A vertex of `ℤΔ` above the given sectional path, at height `t`. -/
def zv (p : Q.SecPath x₀) (t : ℤ) (ht : (t : ZMod 2) = (p.len : ZMod 2)) :
    (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert := ⟨p, t, ht⟩

theorem nonempty_hom_iff' {X Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert} :
    Nonempty (X ⟶ Y) ↔ (IsParent X.v Y.v ∨ IsParent Y.v X.v) ∧ Y.t = X.t + 1 :=
  ⟨fun ⟨a⟩ ↦ a.down, fun h ↦ ⟨⟨h⟩⟩⟩

/-- A child and the parent of a vertex of `Δ` have different images. -/
theorem piV_child_ne_parent {X Y Y' : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert}
    (hc : IsParent X.v Y.v) (ht : Y.t = X.t + 1) (hc' : IsParent Y'.v X.v) (ht' : Y'.t = X.t + 1) :
    piV hQ x₀ Y ≠ piV hQ x₀ Y' := by
  intro heq
  obtain ⟨w, b, h1⟩ := hc
  obtain ⟨e, a, h1'⟩ := hc'
  have h2 := piV_parent hQ h1' ht'
  rw [← heq, piV_child hQ h1 ht, ← Equiv.Perm.mul_apply, ← zpow_one_add, add_comm,
    zpow_add_one, Equiv.Perm.mul_apply] at h2
  have hu : hQ.tauE w = Y'.v.endv := (hQ.tauE ^ (-jco x₀ X)).injective h2
  obtain ⟨⟨⟨eX, pathX⟩, hsX⟩, tX, htX⟩ := X
  obtain ⟨⟨⟨eY, pathY⟩, hsY⟩, tY, htY⟩ := Y
  simp only at h1 h1'
  obtain ⟨rfl, h3⟩ := Sigma.mk.inj_iff.1 h1'
  obtain rfl := eq_of_heq h3
  obtain ⟨rfl, h4⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq h4
  exact not_isMeshPair_of_sectional _ a b hsY ((isMeshPair_iff hQ a b).2 hu.symm)

theorem exists_child (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) {z : V} (b : X.v.endv ⟶ z)
    (hsec : Q.IsSectional (X.v.1.2.cons b)) :
    ∃ Y, Nonempty (X ⟶ Y) ∧ piV hQ x₀ Y = (hQ.tauE ^ (-jco x₀ X)) z := by
  let Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert := ⟨⟨⟨z, X.v.1.2.cons b⟩, hsec⟩, X.t + 1, by
    have := X.ht
    change ((X.t + 1 : ℤ) : ZMod 2) = ((X.v.len + 1 : ℕ) : ZMod 2)
    change (X.t : ZMod 2) = (X.v.len : ZMod 2) at this
    push_cast; rw [this]⟩
  have hY : Y.v.1 = ⟨z, X.v.1.2.cons b⟩ := rfl
  exact ⟨Y, (nonempty_hom_iff').2 ⟨Or.inl ⟨z, b, hY⟩, rfl⟩, piV_child hQ hY rfl⟩

theorem exists_parent (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) {u : V}
    (p' : Quiver.Path x₀ u) (a : u ⟶ X.v.endv) (hX : X.v.1 = ⟨X.v.endv, p'.cons a⟩)
    (hsec : Q.IsSectional p') :
    ∃ Y, Nonempty (X ⟶ Y) ∧ hQ.tauE (piV hQ x₀ Y) = (hQ.tauE ^ (-jco x₀ X)) u := by
  let Y : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert := ⟨⟨⟨u, p'⟩, hsec⟩, X.t + 1, by
    have := X.ht
    have hl : X.v.len = p'.length + 1 := by unfold len; rw [hX]; rfl
    change ((X.t + 1 : ℤ) : ZMod 2) = ((p'.length : ℕ) : ZMod 2)
    change (X.t : ZMod 2) = (X.v.len : ZMod 2) at this
    rw [hl] at this
    push_cast at this ⊢
    rw [this, add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]⟩
  have hX' : X.v.1 = ⟨X.v.endv, Y.v.1.2.cons a⟩ := hX
  exact ⟨Y, (nonempty_hom_iff').2 ⟨Or.inr ⟨X.v.endv, a, hX'⟩, rfl⟩, piV_parent hQ hX' rfl⟩

/-- **`π` is bijective on outgoing stars.** -/
theorem piQ_star_bijective (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) :
    Bijective ((piQ hQ (x₀ := x₀)).star X) := by
  apply star_bijective_of
  · -- injectivity
    intro Y Y' hY hY' heq
    rw [nonempty_hom_iff'] at hY hY'
    change piV hQ x₀ Y = piV hQ x₀ Y' at heq
    have ht : Y.t = Y'.t := by omega
    suffices hv : Y.v = Y'.v from OrientedTree.ZVert.ext hv ht
    rcases hY.1 with hc | hc <;> rcases hY'.1 with hc' | hc'
    · obtain ⟨w, b, h1⟩ := hc
      obtain ⟨w', b', h1'⟩ := hc'
      rw [piV_child hQ h1 hY.2, piV_child hQ h1' hY'.2] at heq
      have hw : w = w' := (hQ.tauE ^ (-jco x₀ X)).injective heq
      subst hw
      obtain rfl : b = b' := Subsingleton.elim _ _
      exact Subtype.ext (h1.trans h1'.symm)
    · exact absurd heq (piV_child_ne_parent hQ hc hY.2 hc' hY'.2)
    · exact absurd heq.symm (piV_child_ne_parent hQ hc' hY'.2 hc hY.2)
    · exact (eq_parent_of_isParent hc (by have := len_of_isParent hc; omega)).trans
        (eq_parent_of_isParent hc' (by have := len_of_isParent hc'; omega)).symm
  · -- surjectivity
    intro y hy
    set j := jco x₀ X
    set z := (hQ.tauE ^ j) y
    have hz : (hQ.tauE ^ (-j)) z = y := by
      simp only [z, ← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
        Equiv.Perm.one_apply]
    have hb : Nonempty (X.v.endv ⟶ z) := by
      rw [← hQ.nonempty_hom_zpow_iff (-j), hz]; exact hy
    obtain ⟨b⟩ := hb
    have hcomm : ∀ v : V, hQ.tauE ((hQ.tauE ^ (-j)) v) = (hQ.tauE ^ (-j)) (hQ.tauE v) := by
      intro v
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← zpow_one_add, ← zpow_add_one,
        add_comm]
    obtain ⟨⟨⟨e, path⟩, hs⟩, t, ht⟩ := X
    cases path with
    | nil =>
        obtain ⟨Y, hXY, hY⟩ := exists_child hQ (X := ⟨⟨⟨x₀, Quiver.Path.nil⟩, hs⟩, t, ht⟩) b
          (isSectional_cons _ hs b (fun p' a h ↦ by cases h))
        exact ⟨Y, hXY, hY.trans hz⟩
    | @cons u _ p' a =>
        by_cases hu : u = hQ.tauE z
        · obtain ⟨Y, hXY, hY⟩ := exists_parent hQ (X := ⟨⟨⟨_, p'.cons a⟩, hs⟩, t, ht⟩) p' a rfl
            (isSectional_of_cons p' a hs)
          refine ⟨Y, hXY, (hQ.tauE).injective ?_⟩
          change hQ.tauE (piV hQ x₀ Y) = hQ.tauE y
          rw [hY]
          have h2 : (hQ.tauE ^ (-j)) u = hQ.tauE y := by rw [hu, ← hcomm, hz]
          exact h2
        · obtain ⟨Y, hXY, hY⟩ := exists_child hQ (X := ⟨⟨⟨_, p'.cons a⟩, hs⟩, t, ht⟩) b
            (isSectional_cons _ hs b (fun p'' a' h hm ↦ by
              cases h
              exact hu ((isMeshPair_iff hQ a b).1 hm)))
          exact ⟨Y, hXY, hY.trans hz⟩

/-- **`π` is bijective on incoming stars** ("mates give the same conclusion on
incoming stars"). -/
theorem piQ_costar_bijective (X : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert) :
    Bijective ((piQ hQ (x₀ := x₀)).costar X) := by
  have hZ := (SecPath.tree (Q := Q) (x₀ := x₀)).zQuiver_isStable
  have hmate : ∀ Y, Nonempty (Y ⟶ X) ↔
      Nonempty ((SecPath.tree (Q := Q) (x₀ := x₀)).ztau X ⟶ Y) := fun Y ↦ hZ.nonempty_hom_iff X Y
  apply costar_bijective_of
  · intro Y Y' hY hY' he
    exact eq_of_star_bijective _ (piQ_star_bijective hQ _) ((hmate Y).1 hY) ((hmate Y').1 hY') he
  · intro y hy
    rw [hQ.nonempty_hom_iff] at hy
    change Nonempty (hQ.tauE (piV hQ x₀ X) ⟶ y) at hy
    rw [← piV_ztau] at hy
    obtain ⟨Y, hY, rfl⟩ := exists_of_star_bijective _ (piQ_star_bijective hQ _) hy
    exact ⟨Y, (hmate Y).2 hY, rfl⟩

/-- **`π : ℤΔ → Q` is a covering of quivers.** -/
theorem piQ_isCovering : (piQ hQ (x₀ := x₀)).IsCovering :=
  ⟨piQ_star_bijective hQ, piQ_costar_bijective hQ⟩

/-- The root at height `0`. -/
def rootZ : (SecPath.tree (Q := Q) (x₀ := x₀)).ZVert := ⟨root Q x₀, 0, by simp [tree, root, len]⟩

theorem piV_rootZ : piV hQ x₀ rootZ = x₀ := by
  simp [piV, rootZ, jco, root, len, endv]

/-- Adjacency in `Q` together with the translation edges. -/
def ConnAdj (hQ : Q.IsStable) (a b : V) : Prop := Nonempty (a ⟶ b) ∨ b = hQ.tauE a

/-- **The image of `π` is the whole component** of `x₀`. -/
theorem piV_surjective_of_conn {v : V} (hv : Relation.EqvGen (ConnAdj hQ) x₀ v) :
    ∃ X, piV hQ x₀ X = v := by
  have key : ∀ a b, Relation.EqvGen (ConnAdj hQ) a b →
      ((∃ X, piV hQ x₀ X = a) ↔ (∃ X, piV hQ x₀ X = b)) := by
    intro a b hab
    induction hab with
    | rel a b h =>
        constructor
        · rintro ⟨X, rfl⟩
          rcases h with h | rfl
          · exact (exists_of_star_bijective _ (piQ_star_bijective hQ X) h).imp fun _ h ↦ h.2
          · exact ⟨_, piV_ztau hQ X⟩
        · rintro ⟨Y, rfl⟩
          rcases h with h | h
          · exact (exists_of_costar_bijective _ ((piQ_costar_bijective hQ Y)) h).imp fun _ h ↦ h.2
          · refine ⟨(SecPath.tree (Q := Q) (x₀ := x₀)).ztauInv Y, (hQ.tauE).injective ?_⟩
            have e : (SecPath.tree (Q := Q) (x₀ := x₀)).ztau
                ((SecPath.tree (Q := Q) (x₀ := x₀)).ztauInv Y) = Y := by
              ext <;> simp [OrientedTree.ztau, OrientedTree.ztauInv]
            rw [← piV_ztau, e, h]
    | refl => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key _ _ hv).1 ⟨rootZ, piV_rootZ hQ⟩

end SecPath

end TranslationQuiver

end MultiplicativeBasisDeformations
