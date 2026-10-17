import MultiplicativeBasisDeformations.Foundations.DeckGroup
import MultiplicativeBasisDeformations.Foundations.StarAut
import Mathlib.GroupTheory.Archimedean

/-!
# Deck transformations for star models

Proof of Proposition 4.1, Step 3 (`periodic-mesh-calculations.tex:142–166`), for
the repetition of a star model `Δ` covering a finite stable translation quiver
`Q` by `π`:

"For each `z` with `π z = π o`, construct a map `H_z : R → R` over `π` by
sending `o` to `z`, lifting the rooted tree edges, and extending by translation
and mates. Since `Δ` is a tree, these choices are consistent."

Here `o` is the centre at height `0`; the rooted tree edges are the arms.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Function

namespace MultiplicativeBasisDeformations

universe u w

variable {t : ℕ} (L : Fin t → ℕ)

namespace StarDeck

/-- The base vertex of `ℤΔ` over a star vertex: height equal to its depth. -/
def B (x : StarV L) : (starTree L).ZVert := ⟨x, starDepth x, rfl⟩

/-- The centre at height zero. -/
abbrev o : (starTree L).ZVert := B L none

theorem B_none_arrow (i : Fin t) : Nonempty (B L none ⟶ B L (some ⟨i, 0⟩)) :=
  ⟨⟨(rfl : ((0 : Fin (L i + 1)) : ℕ) = 0), rfl⟩⟩

theorem B_arm_arrow (i : Fin t) (k : Fin (L i)) :
    Nonempty (B L (some ⟨i, k.castSucc⟩) ⟶ B L (some ⟨i, k.succ⟩)) :=
  ⟨⟨⟨rfl, Or.inl (by simp)⟩, by simp [B, starDepth]⟩⟩

variable {L}

/-- A neighbour of each star vertex (when there is an arm). -/
def nb (ht : 0 < t) : StarV L → StarV L
  | none => some ⟨⟨0, ht⟩, 0⟩
  | some ⟨i, k⟩ => if hk : (k : ℕ) = 0 then none else some ⟨i, ⟨k - 1, by omega⟩⟩

theorem adj_nb (ht : 0 < t) (x : StarV L) : starAdj x (nb ht x) := by
  rcases x with _ | ⟨i, k⟩
  · simp [nb, starAdj]
  · simp only [nb]
    split_ifs with hk
    · simp [starAdj, hk]
    · simp only [starAdj, true_and]; right; omega

theorem zadj_up (ht : 0 < t) (X : (starTree L).ZVert) :
    Relation.EqvGen (starTree L).ZAdj X ((starTree L).upZ X 1) := by
  let Y : (starTree L).ZVert := (starTree L).aboveZ X (nb ht X.v) (adj_nb ht X.v)
  have h1 : (starTree L).ZAdj X Y := Or.inl ((starTree L).nonempty_hom_aboveZ _ _ _)
  have h2 : (starTree L).ZAdj Y ((starTree L).upZ X 1) := Or.inl
    ⟨⟨(starGraph L).symm.symm _ _ (adj_nb ht X.v), by
      simp [Y, OrientedTree.aboveZ, OrientedTree.upZ]; ring⟩⟩
  exact (Relation.EqvGen.rel _ _ h1).trans _ _ _ (Relation.EqvGen.rel _ _ h2)

theorem eqvGen_upZ (ht : 0 < t) (X : (starTree L).ZVert) (n : ℕ) :
    Relation.EqvGen (starTree L).ZAdj X ((starTree L).upZ X n) := by
  induction n with
  | zero =>
      have : (starTree L).upZ X 0 = X := by ext <;> simp [OrientedTree.upZ]
      rw [this]; exact Relation.EqvGen.refl _
  | succ n ih =>
      refine ih.trans _ _ _ ?_
      have : (starTree L).upZ X (n + 1) = (starTree L).upZ ((starTree L).upZ X n) 1 := by
        ext <;> simp [OrientedTree.upZ]; ring
      rw [this]
      exact zadj_up ht _

theorem eqvGen_B (x : StarV L) : Relation.EqvGen (starTree L).ZAdj (o L) (B L x) := by
  rcases x with _ | ⟨i, k⟩
  · exact Relation.EqvGen.refl _
  · obtain ⟨k, hk⟩ := k
    induction k with
    | zero => exact Relation.EqvGen.rel _ _ (Or.inl (B_none_arrow L i))
    | succ k ih =>
        refine (ih (by omega)).trans _ _ _ (Relation.EqvGen.rel _ _ (Or.inl ?_))
        have := B_arm_arrow L i ⟨k, by omega⟩
        simpa using this

/-- **`ℤΔ` is connected.** -/
theorem zconnected (ht : 0 < t) : (starTree L).ZConnected := by
  have key : ∀ X, Relation.EqvGen (starTree L).ZAdj (o L) X := by
    intro X
    refine (eqvGen_B X.v).trans _ _ _ ?_
    rcases (starTree L).eq_upZ_or (show (B L X.v).v = X.v from rfl) with ⟨n, hn⟩ | ⟨n, hn⟩
    · rw [hn]; exact eqvGen_upZ ht _ n
    · rw [hn]; exact (eqvGen_upZ ht _ n).symm
  exact fun X Y ↦ (key X).symm.trans _ _ _ (key Y)

variable (L)

/-- Translation of `ℤΔ`, as a permutation. -/
abbrev τW : Equiv.Perm (starTree L).ZVert := (starTree L).zQuiver_isStable.tauE

theorem τW_apply (X : (starTree L).ZVert) : τW L X = (starTree L).ztau X := rfl

theorem τW_zpow_v (n : ℤ) (X : (starTree L).ZVert) : ((τW L ^ n) X).v = X.v := by
  induction n using Int.induction_on generalizing X with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih, τW_apply]; rfl
  | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      have := congrArg OrientedTree.ZVert.v ((τW L).apply_symm_apply X)
      rw [τW_apply] at this
      exact this

theorem τW_zpow_t (n : ℤ) (X : (starTree L).ZVert) : ((τW L ^ n) X).t = X.t - 2 * n := by
  induction n using Int.induction_on generalizing X with
  | zero => simp
  | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, ih, τW_apply]
      simp only [OrientedTree.ztau]; ring
  | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
      have := congrArg OrientedTree.ZVert.t ((τW L).apply_symm_apply X)
      rw [τW_apply] at this
      simp only [OrientedTree.ztau] at this
      have e : ((τW L)⁻¹ X).t = X.t + 2 := by
        change ((τW L).symm X).t = X.t + 2; omega
      rw [e]; ring

/-- The repetition coordinate `j`, with `t = depth + 2j`. -/
def jco (X : (starTree L).ZVert) : ℤ := (X.t - starDepth X.v) / 2

theorem two_mul_jco (X : (starTree L).ZVert) : 2 * jco L X = X.t - starDepth X.v := by
  have h : (2 : ℤ) ∣ X.t - starDepth X.v := by
    have := X.ht
    change (X.t : ZMod 2) = ((starDepth X.v : ℤ) : ZMod 2) at this
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 2).1 this.symm
  exact Int.mul_ediv_cancel' h

theorem eq_τW_zpow_B (X : (starTree L).ZVert) : X = (τW L ^ (-jco L X)) (B L X.v) := by
  ext
  · rw [τW_zpow_v]; rfl
  · rw [τW_zpow_t]; have := two_mul_jco L X; simp only [B]; omega

section Lift

variable {V : Type u} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V) (hπ : π.IsCovering)
  (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))

include hτ in
theorem π_τW_zpow (n : ℤ) (Y : (starTree L).ZVert) :
    π.obj ((τW L ^ n) Y) = (hQ.tauE ^ n) (π.obj Y) := by
  induction n using Int.induction_on generalizing Y with
  | zero => simp
  | succ n ih => rw [zpow_add_one, Equiv.Perm.mul_apply, ih, zpow_add_one,
      Equiv.Perm.mul_apply, τW_apply, hτ]
  | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, ih, zpow_sub_one, Equiv.Perm.mul_apply]
      congr 1
      apply hQ.tauE.injective
      have e1 : ∀ x, hQ.tauE (hQ.tauE⁻¹ x) = x := fun x ↦ by simp
      have e2 : ∀ X, τW L ((τW L)⁻¹ X) = X := fun X ↦ by simp
      rw [e1, ← hτ, ← τW_apply, e2]

/-- One lifting step: the out-neighbour of `X` over a given out-neighbour of
`π X`. -/
def stepLift (X : (starTree L).ZVert) (y : V) (h : Nonempty (π.obj X ⟶ y)) :
    (starTree L).ZVert :=
  Classical.choose (exists_of_star_bijective π (hπ.1 X) h)

theorem stepLift_spec (X : (starTree L).ZVert) (y : V) (h : Nonempty (π.obj X ⟶ y)) :
    Nonempty (X ⟶ stepLift L π hπ X y h) ∧ π.obj (stepLift L π hπ X y h) = y :=
  Classical.choose_spec (exists_of_star_bijective π (hπ.1 X) h)

/-- Lifting the arm `i` from `z`. -/
def liftArm (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (i : Fin t) :
    ∀ k : ℕ, ∀ hk : k < L i + 1, {Y : (starTree L).ZVert //
      π.obj Y = π.obj (B L (some ⟨i, ⟨k, hk⟩⟩))}
  | 0, hk => ⟨stepLift L π hπ z _ (by rw [hz]; exact ⟨π.map (B_none_arrow L i).some⟩),
      (stepLift_spec L π hπ z _ _).2⟩
  | k + 1, hk =>
      let prev := liftArm z hz i k (by omega)
      ⟨stepLift L π hπ prev.1 _ (by
          have h1 : Nonempty (π.obj (B L (some ⟨i, ⟨k, by omega⟩⟩)) ⟶
              π.obj (B L (some ⟨i, ⟨k + 1, hk⟩⟩))) :=
            ⟨π.map (B_arm_arrow L i ⟨k, by omega⟩).some⟩
          rw [prev.2]; exact h1),
        (stepLift_spec L π hπ prev.1 _ _).2⟩

theorem liftArm_zero_arrow (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (i : Fin t)
    (hk : 0 < L i + 1) : Nonempty (z ⟶ (liftArm L π hπ z hz i 0 hk).1) :=
  (stepLift_spec L π hπ z _ (by rw [hz]; exact ⟨π.map (B_none_arrow L i).some⟩)).1

theorem liftArm_succ_arrow (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (i : Fin t)
    (k : ℕ) (hk : k + 1 < L i + 1) :
    Nonempty ((liftArm L π hπ z hz i k (by omega)).1 ⟶ (liftArm L π hπ z hz i (k + 1) hk).1) :=
  (stepLift_spec L π hπ _ _ (by
    have h1 : Nonempty (π.obj (B L (some ⟨i, ⟨k, by omega⟩⟩)) ⟶
        π.obj (B L (some ⟨i, ⟨k + 1, hk⟩⟩))) :=
      ⟨π.map (B_arm_arrow L i ⟨k, by omega⟩).some⟩
    rw [(liftArm L π hπ z hz i k (by omega)).2]; exact h1)).1

/-- The lift of the star from `z`. -/
def Lz (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) : StarV L → (starTree L).ZVert
  | none => z
  | some x => (liftArm L π hπ z hz x.1 x.2.1 x.2.2).1

theorem π_Lz (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (x : StarV L) :
    π.obj (Lz L π hπ z hz x) = π.obj (B L x) := by
  rcases x with _ | ⟨i, k⟩
  · exact hz
  · exact (liftArm L π hπ z hz i k.1 k.2).2

theorem Lz_child (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) {x y : StarV L}
    (h : starAdj x y) (hd : starDepth y = starDepth x + 1) :
    Nonempty (Lz L π hπ z hz x ⟶ Lz L π hπ z hz y) := by
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩ <;> simp only [starAdj] at h
  · obtain ⟨l, hl⟩ := l
    simp only at h
    subst h
    exact liftArm_zero_arrow L π hπ z hz j hl
  · simp [starDepth] at hd
  · obtain ⟨rfl, h⟩ := h
    simp only [starDepth] at hd
    obtain ⟨k, hk⟩ := k
    obtain ⟨l, hl⟩ := l
    simp only at hd h
    obtain rfl : l = k + 1 := by omega
    exact liftArm_succ_arrow L π hπ z hz i k hl

/-- **The deck transformation `H_z`** (`periodic-mesh-calculations.tex:146–149`):
lift the arms from `z`, then extend by translation. -/
def Hz (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (X : (starTree L).ZVert) :
    (starTree L).ZVert :=
  (τW L ^ (-jco L X)) (Lz L π hπ z hz X.v)

include hτ in
theorem π_Hz (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (X : (starTree L).ZVert) :
    π.obj (Hz L π hπ z hz X) = π.obj X := by
  conv_rhs => rw [eq_τW_zpow_B L X]
  unfold Hz
  rw [π_τW_zpow L hQ π hτ, π_τW_zpow L hQ π hτ, π_Lz]

theorem Hz_o (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) :
    Hz L π hπ z hz (o L) = z := by
  have : jco L (o L) = 0 := by simp [jco, o, B, starDepth]
  unfold Hz
  rw [this]
  simp [Lz, o, B]

theorem jco_ztau (X : (starTree L).ZVert) : jco L ((starTree L).ztau X) = jco L X - 1 := by
  have h1 := two_mul_jco L X
  have h2 := two_mul_jco L ((starTree L).ztau X)
  change 2 * jco L ((starTree L).ztau X) = (X.t - 2) - starDepth X.v at h2
  omega

theorem Hz_ztau (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (X : (starTree L).ZVert) :
    Hz L π hπ z hz ((starTree L).ztau X) = (starTree L).ztau (Hz L π hπ z hz X) := by
  unfold Hz
  have hv : ((starTree L).ztau X).v = X.v := rfl
  rw [jco_ztau, hv, ← τW_apply, ← Equiv.Perm.mul_apply, ← zpow_one_add]
  congr 2
  ring

theorem jco_child {X Y : (starTree L).ZVert} (hd : starDepth Y.v = starDepth X.v + 1)
    (ht : Y.t = X.t + 1) : jco L Y = jco L X := by
  have h1 := two_mul_jco L X; have h2 := two_mul_jco L Y; push_cast [hd] at h2; omega

theorem jco_parent {X Y : (starTree L).ZVert} (hd : starDepth X.v = starDepth Y.v + 1)
    (ht : Y.t = X.t + 1) : jco L Y = jco L X + 1 := by
  have h1 := two_mul_jco L X; have h2 := two_mul_jco L Y; push_cast [hd] at h1; omega

/-- **`H_z` preserves arrows** ("extending by translation and mates"). -/
theorem Hz_arrow (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L))
    {X Y : (starTree L).ZVert} (h : Nonempty (X ⟶ Y)) :
    Nonempty (Hz L π hπ z hz X ⟶ Hz L π hπ z hz Y) := by
  obtain ⟨⟨hadj, ht⟩⟩ := h
  have hS := (starTree L).zQuiver_isStable
  rcases starAdj_depth hadj with hd | hd
  · rw [Hz, Hz, jco_child L hd ht]
    rw [hS.nonempty_hom_zpow_iff]
    exact Lz_child L π hπ z hz hadj hd
  · rw [Hz, Hz, jco_parent L hd ht]
    have hc := Lz_child L π hπ z hz ((starGraph L).symm.symm _ _ hadj) hd
    have e : (τW L ^ (-jco L X)) (Lz L π hπ z hz X.v) =
        (τW L ^ (-(jco L X + 1))) (τW L (Lz L π hπ z hz X.v)) := by
      rw [← Equiv.Perm.mul_apply, ← zpow_add_one]; congr 2; ring
    rw [e, hS.nonempty_hom_zpow_iff, ← hS.nonempty_hom_iff]
    exact hc

include hτ in
/-- The image of `H_z` is closed under neighbours (outgoing). -/
theorem Hz_out (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) {X Y' : (starTree L).ZVert}
    (h : Nonempty (Hz L π hπ z hz X ⟶ Y')) : ∃ Y, Nonempty (X ⟶ Y) ∧ Hz L π hπ z hz Y = Y' := by
  obtain ⟨b⟩ := h
  have hb : Nonempty (π.obj X ⟶ π.obj Y') := by
    rw [← π_Hz L hQ π hπ hτ z hz X]; exact ⟨π.map b⟩
  obtain ⟨Y, hXY, hY⟩ := exists_of_star_bijective π (hπ.1 X) hb
  refine ⟨Y, hXY, eq_of_star_bijective π (hπ.1 _) (Hz_arrow L π hπ z hz hXY) ⟨b⟩ ?_⟩
  rw [π_Hz L hQ π hπ hτ, hY]

include hτ in
/-- The image of `H_z` is closed under neighbours (incoming). -/
theorem Hz_in (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) {X Y' : (starTree L).ZVert}
    (h : Nonempty (Y' ⟶ Hz L π hπ z hz X)) : ∃ Y, Nonempty (Y ⟶ X) ∧ Hz L π hπ z hz Y = Y' := by
  obtain ⟨b⟩ := h
  have hb : Nonempty (π.obj Y' ⟶ π.obj X) := by
    rw [← π_Hz L hQ π hπ hτ z hz X]; exact ⟨π.map b⟩
  obtain ⟨Y, hYX, hY⟩ := exists_of_costar_bijective π (hπ.2 X) hb
  refine ⟨Y, hYX, ?_⟩
  obtain ⟨c⟩ := Hz_arrow L π hπ z hz hYX
  have hc := (hπ.2 (Hz L π hπ z hz X)).1
  have e : π.obj (Hz L π hπ z hz Y) = π.obj Y' := by rw [π_Hz L hQ π hπ hτ, hY]
  have : π.costar _ ⟨Hz L π hπ z hz Y, c⟩ = π.costar _ ⟨Y', b⟩ := by
    simp only [Prefunctor.costar_apply]
    exact Sigma.ext e (Subsingleton.helim (congrArg (· ⟶ _) e) _ _)
  exact congrArg Sigma.fst (hc this)

include hτ in
/-- **`H_z` is surjective** ("Its image is closed under neighbours and it is
surjective"). -/
theorem Hz_surjective (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) :
    Function.Surjective (Hz L π hπ z hz) := by
  have key : ∀ Y Y', Relation.EqvGen (starTree L).ZAdj Y Y' →
      ((∃ X, Hz L π hπ z hz X = Y) ↔ (∃ X, Hz L π hπ z hz X = Y')) := by
    intro Y Y' h
    induction h with
    | rel Y Y' h =>
        constructor
        · rintro ⟨X, rfl⟩
          rcases h with h | h
          · obtain ⟨X', -, hX'⟩ := Hz_out L hQ π hπ hτ z hz h; exact ⟨X', hX'⟩
          · obtain ⟨X', -, hX'⟩ := Hz_in L hQ π hπ hτ z hz h; exact ⟨X', hX'⟩
        · rintro ⟨X, rfl⟩
          rcases h with h | h
          · obtain ⟨X', -, hX'⟩ := Hz_in L hQ π hπ hτ z hz h; exact ⟨X', hX'⟩
          · obtain ⟨X', -, hX'⟩ := Hz_out L hQ π hπ hτ z hz h; exact ⟨X', hX'⟩
    | refl => exact Iff.rfl
    | symm Y Y' _ ih => exact ih.symm
    | trans Y Y' Y'' _ _ ih1 ih2 => exact ih1.trans ih2
  intro Y
  exact (key _ _ (zconnected ht z Y)).1 ⟨o L, Hz_o L π hπ z hz⟩

include hτ in
theorem Hz_comp (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L))
    (z' : (starTree L).ZVert) (hz' : π.obj z' = π.obj (o L)) (X : (starTree L).ZVert) :
    Hz L π hπ z hz (Hz L π hπ z' hz' X) =
      Hz L π hπ (Hz L π hπ z hz z') ((π_Hz L hQ π hπ hτ z hz z').trans hz') X := by
  refine (starTree L).eq_of_over (zconnected ht) π hπ _ _
    (fun X Y h ↦ Hz_arrow L π hπ z hz (Hz_arrow L π hπ z' hz' h))
    (fun X Y h ↦ Hz_arrow L π hπ _ _ h)
    (fun X ↦ by rw [π_Hz L hQ π hπ hτ, π_Hz L hQ π hπ hτ])
    (fun X ↦ π_Hz L hQ π hπ hτ _ _ X) (X₀ := o L) ?_ X
  rw [Hz_o, Hz_o]

include hτ in
theorem Hz_eq_self_of (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L))
    {X₀ : (starTree L).ZVert} (h₀ : Hz L π hπ z hz X₀ = X₀) (X : (starTree L).ZVert) :
    Hz L π hπ z hz X = X :=
  (starTree L).eq_of_over (zconnected ht) π hπ _ id (fun X Y h ↦ Hz_arrow L π hπ z hz h)
    (fun X Y h ↦ h) (π_Hz L hQ π hπ hτ z hz) (fun X ↦ rfl) h₀ X

include hτ in
/-- **`H_z` is an automorphism**. -/
theorem Hz_bijective (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) :
    Function.Bijective (Hz L π hπ z hz) := by
  refine ⟨fun X Y hXY ↦ ?_, Hz_surjective L hQ π hπ hτ ht z hz⟩
  obtain ⟨z', hz'o⟩ := Hz_surjective L hQ π hπ hτ ht z hz (o L)
  have hz' : π.obj z' = π.obj (o L) := by rw [← π_Hz L hQ π hπ hτ z hz z', hz'o]
  -- `H_{z'} ∘ H_z` fixes `z'`, hence is the identity
  have hleft : ∀ W, Hz L π hπ z' hz' (Hz L π hπ z hz W) = W := by
    intro W
    rw [Hz_comp L hQ π hπ hτ ht z' hz' z hz]
    refine Hz_eq_self_of L hQ π hπ hτ ht _ _ (X₀ := z') ?_ W
    rw [← Hz_comp L hQ π hπ hτ ht z' hz' z hz, hz'o, Hz_o]
  rw [← hleft X, ← hleft Y, hXY]

include hτ in
theorem Hz_τW_zpow (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) (n : ℤ)
    (X : (starTree L).ZVert) :
    Hz L π hπ z hz ((τW L ^ n) X) = (τW L ^ n) (Hz L π hπ z hz X) := by
  induction n using Int.induction_on generalizing X with
  | zero => rfl
  | succ n ih =>
      rw [zpow_add_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, τW_apply, Hz_ztau]
      rfl
  | pred n ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      congr 1
      apply (τW L).injective
      have e : ∀ W, τW L ((τW L)⁻¹ W) = W := fun W ↦ by simp
      rw [e, τW_apply, ← Hz_ztau, ← τW_apply, e]

include hτ in
theorem fibre_B_arm (i : Fin t) : ∀ (k : ℕ) (hk : k < L i + 1) (Y : (starTree L).ZVert),
    π.obj Y = π.obj (B L (some ⟨i, ⟨k, hk⟩⟩)) →
    ∃ (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)),
      Hz L π hπ z hz (B L (some ⟨i, ⟨k, hk⟩⟩)) = Y := by
  intro k
  induction k with
  | zero =>
      intro hk Y hY
      have h0 : Nonempty (π.obj (o L) ⟶ π.obj Y) := by
        rw [hY]; exact ⟨π.map (B_none_arrow L i).some⟩
      obtain ⟨z, hzY, hz⟩ := exists_of_costar_bijective π (hπ.2 Y) h0
      refine ⟨z, hz, ?_⟩
      have h1 := Hz_arrow L π hπ z hz (B_none_arrow L i)
      rw [Hz_o] at h1
      exact eq_of_star_bijective π (hπ.1 z) h1 hzY (by rw [π_Hz L hQ π hπ hτ, hY])
  | succ k ih =>
      intro hk Y hY
      have h0 : Nonempty (π.obj (B L (some ⟨i, ⟨k, by omega⟩⟩)) ⟶ π.obj Y) := by
        rw [hY]; exact ⟨π.map (B_arm_arrow L i ⟨k, by omega⟩).some⟩
      obtain ⟨Y₀, hY₀Y, hY₀⟩ := exists_of_costar_bijective π (hπ.2 Y) h0
      obtain ⟨z, hz, hzY₀⟩ := ih (by omega) Y₀ hY₀
      refine ⟨z, hz, ?_⟩
      have h1 := Hz_arrow L π hπ z hz (B_arm_arrow L i ⟨k, by omega⟩)
      have e1 : B L (some ⟨i, (⟨k, by omega⟩ : Fin (L i)).castSucc⟩) =
          B L (some ⟨i, ⟨k, by omega⟩⟩) := rfl
      have e2 : B L (some ⟨i, (⟨k, by omega⟩ : Fin (L i)).succ⟩) =
          B L (some ⟨i, ⟨k + 1, hk⟩⟩) := rfl
      rw [e1, e2, hzY₀] at h1
      exact eq_of_star_bijective π (hπ.1 Y₀) h1 hY₀Y (by rw [π_Hz L hQ π hπ hτ, hY])

include hτ in
/-- **The deck group is transitive on fibres** (`periodic-mesh-calculations.tex:162–166`). -/
theorem fibre_transitive {X Y : (starTree L).ZVert} (h : π.obj X = π.obj Y) :
    ∃ (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)), Hz L π hπ z hz X = Y := by
  set j := jco L X
  have hX := eq_τW_zpow_B L X
  set Y' := (τW L ^ j) Y
  have hY' : π.obj Y' = π.obj (B L X.v) := by
    have e : π.obj X = (hQ.tauE ^ (-j)) (π.obj (B L X.v)) := by
      conv_lhs => rw [hX]
      rw [π_τW_zpow L hQ π hτ]
    rw [π_τW_zpow L hQ π hτ, ← h, e, ← Equiv.Perm.mul_apply, ← zpow_add, add_neg_cancel,
      zpow_zero, Equiv.Perm.one_apply]
  have hYY' : Y = (τW L ^ (-j)) Y' := by
    simp only [Y', ← Equiv.Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
      Equiv.Perm.one_apply]
  obtain ⟨z, hz, hzB⟩ : ∃ (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)),
      Hz L π hπ z hz (B L X.v) = Y' := by
    rcases hxv : X.v with _ | ⟨i, k⟩
    · rw [hxv] at hY'
      exact ⟨Y', hY', Hz_o L π hπ Y' hY'⟩
    · rw [hxv] at hY'
      exact fibre_B_arm L hQ π hπ hτ i k.1 k.2 Y' hY'
  refine ⟨z, hz, ?_⟩
  rw [hX, Hz_τW_zpow L hQ π hπ hτ, hzB, ← hYY']

/-- The deck transformation `H_z`, as a permutation. -/
noncomputable def deck (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) :
    Equiv.Perm (starTree L).ZVert :=
  Equiv.ofBijective _ (Hz_bijective L hQ π hπ hτ ht z hz)

theorem deck_apply (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L))
    (X : (starTree L).ZVert) : deck L hQ π hπ hτ ht z hz X = Hz L π hπ z hz X := rfl

include hτ in
theorem deck_arrow_iff (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L))
    (X Y : (starTree L).ZVert) :
    Nonempty (X ⟶ Y) ↔ Nonempty (deck L hQ π hπ hτ ht z hz X ⟶ deck L hQ π hπ hτ ht z hz Y) := by
  refine ⟨Hz_arrow L π hπ z hz, fun h ↦ ?_⟩
  obtain ⟨X', hX', hX'eq⟩ := Hz_out L hQ π hπ hτ z hz h
  rw [deck_apply] at hX'eq
  have := (Hz_bijective L hQ π hπ hτ ht z hz).1 hX'eq
  rwa [← this]

include hτ in
/-- **Height form of the deck transformations**: `H_z (v, t) = (ρ v, t + z.t)`. -/
theorem deck_height_form (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L)) :
    ∃ ρ : StarV L ≃ StarV L, (∀ a b, starAdj a b ↔ starAdj (ρ a) (ρ b)) ∧
      ∀ X, (Hz L π hπ z hz X).v = ρ X.v ∧ (Hz L π hπ z hz X).t = X.t + z.t := by
  haveI : Nonempty (StarV L) := ⟨none⟩
  obtain ⟨c₀, ρ, hρ, hF⟩ := (starTree L).height_form (deck L hQ π hπ hτ ht z hz)
    (fun X ↦ Hz_ztau L π hπ z hz X) (zconnected ht) (deck_arrow_iff L hQ π hπ hτ ht z hz)
  have hc : c₀ = z.t := by
    have := (hF (o L)).2
    rw [deck_apply, Hz_o] at this
    simp only [o, B, starDepth] at this
    omega
  refine ⟨ρ, hρ, fun X ↦ ?_⟩
  rw [← hc]
  exact hF X

include hτ in
/-- **A height-preserving deck transformation is the identity** ("a kernel
element fixes a root vertex and the deck action is free"). -/
theorem Hz_eq_id_of_t (ht : 0 < t) (hcl : t = 1 ∨ t = 3) (z : (starTree L).ZVert)
    (hz : π.obj z = π.obj (o L)) (h0 : z.t = 0) (X : (starTree L).ZVert) :
    Hz L π hπ z hz X = X := by
  obtain ⟨ρ, hρ, hF⟩ := deck_height_form L hQ π hπ hτ ht z hz
  have hpar : ∀ x, starDepth (ρ x) % 2 = starDepth x % 2 := by
    intro x
    have h1 := (Hz L π hπ z hz (B L x)).ht
    rw [(hF (B L x)).1, (hF (B L x)).2, h0, add_zero] at h1
    change ((starDepth x : ℤ) : ZMod 2) = ((starDepth (ρ x) : ℕ) : ZMod 2) at h1
    have := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 (by exact_mod_cast h1)
    omega
  obtain ⟨x, hx⟩ : ∃ x, ρ x = x := by
    rcases hcl with rfl | rfl
    · exact path_aut_fixed ρ hρ hpar
    · exact ⟨none, fixes_centre_three rfl ρ hρ⟩
  refine Hz_eq_self_of L hQ π hπ hτ ht z hz (X₀ := B L x) ?_ X
  refine OrientedTree.ZVert.ext ?_ ?_
  · rw [(hF _).1]; exact hx
  · rw [(hF _).2, h0, add_zero]

include hτ in
theorem Hz_t (ht : 0 < t) (z : (starTree L).ZVert) (hz : π.obj z = π.obj (o L))
    (X : (starTree L).ZVert) : (Hz L π hπ z hz X).t = X.t + z.t :=
  ((deck_height_form L hQ π hπ hτ ht z hz).choose_spec.2 X).2

include hτ in
theorem Hz_o_id (ht : 0 < t) (X : (starTree L).ZVert) : Hz L π hπ (o L) rfl X = X :=
  Hz_eq_self_of L hQ π hπ hτ ht (o L) rfl (X₀ := o L) (Hz_o L π hπ _ _) X

theorem Hz_congr {w w' : (starTree L).ZVert} (h : w = w') (hw : π.obj w = π.obj (o L))
    (hw' : π.obj w' = π.obj (o L)) (X : (starTree L).ZVert) :
    Hz L π hπ w hw X = Hz L π hπ w' hw' X := by
  subst h; rfl

include hτ in
/-- Powers of a deck transformation are deck transformations. -/
theorem deck_zpow (ht : 0 < t) (z₀ : (starTree L).ZVert) (hz₀ : π.obj z₀ = π.obj (o L)) :
    ∀ l : ℤ, ∃ (w : (starTree L).ZVert) (hw : π.obj w = π.obj (o L)), w.t = l * z₀.t ∧
      ∀ X, ((deck L hQ π hπ hτ ht z₀ hz₀) ^ l) X = Hz L π hπ w hw X := by
  set g := deck L hQ π hπ hτ ht z₀ hz₀
  have hgz : ∀ X, g X = Hz L π hπ z₀ hz₀ X := fun X ↦ rfl
  -- the inverse of `g` is a deck transformation
  set z₁ := g⁻¹ (o L)
  have hgz₁ : g z₁ = o L := by simp [z₁]
  have hz₁ : π.obj z₁ = π.obj (o L) := by
    have h := π_Hz L hQ π hπ hτ z₀ hz₀ z₁
    rw [← hgz, hgz₁] at h
    exact h.symm
  have hz₁t : z₁.t = -z₀.t := by
    have h := Hz_t L hQ π hπ hτ ht z₀ hz₀ z₁
    rw [← hgz, hgz₁] at h
    simp only [o, B, starDepth] at h
    omega
  have hinv : ∀ X, g⁻¹ X = Hz L π hπ z₁ hz₁ X := by
    intro X
    apply g.injective
    rw [show g (g⁻¹ X) = X by simp, hgz, Hz_comp L hQ π hπ hτ ht z₀ hz₀ z₁ hz₁,
      Hz_congr L π hπ ((hgz z₁).symm.trans hgz₁) _ rfl, Hz_o_id L hQ π hπ hτ ht]
  intro l
  induction l using Int.induction_on with
  | zero => exact ⟨o L, rfl, by simp [o, B, starDepth], fun X ↦ by
      rw [zpow_zero, Equiv.Perm.one_apply, Hz_o_id L hQ π hπ hτ ht]⟩
  | succ l ih =>
      obtain ⟨w, hw, hwt, hwX⟩ := ih
      refine ⟨Hz L π hπ w hw z₀, (π_Hz L hQ π hπ hτ w hw z₀).trans hz₀, ?_, fun X ↦ ?_⟩
      · rw [Hz_t L hQ π hπ hτ ht, hwt]; push_cast; ring
      · rw [zpow_add_one, Equiv.Perm.mul_apply, hwX, hgz, Hz_comp L hQ π hπ hτ ht w hw z₀ hz₀]
  | pred l ih =>
      obtain ⟨w, hw, hwt, hwX⟩ := ih
      refine ⟨Hz L π hπ w hw z₁, (π_Hz L hQ π hπ hτ w hw z₁).trans hz₁, ?_, fun X ↦ ?_⟩
      · rw [Hz_t L hQ π hπ hτ ht, hwt, hz₁t]; push_cast; ring
      · rw [zpow_sub_one, Equiv.Perm.mul_apply, hwX, hinv, Hz_comp L hQ π hπ hτ ht w hw z₁ hz₁]

include hπ hτ in
/-- Deck transformations with the same height shift coincide. -/
theorem eq_of_t_eq (ht : 0 < t) (hcl : t = 1 ∨ t = 3) {w w' : (starTree L).ZVert}
    (hw : π.obj w = π.obj (o L)) (hw' : π.obj w' = π.obj (o L)) (h : w.t = w'.t) : w = w' := by
  obtain ⟨v, hv⟩ := Hz_surjective L hQ π hπ hτ ht w' hw' (o L)
  have hvo : π.obj v = π.obj (o L) := by rw [← π_Hz L hQ π hπ hτ w' hw' v, hv]
  have hvt : v.t = -w'.t := by
    have := Hz_t L hQ π hπ hτ ht w' hw' v; rw [hv] at this; simp only [o, B, starDepth] at this
    omega
  set u := Hz L π hπ w hw v
  have hu : π.obj u = π.obj (o L) := (π_Hz L hQ π hπ hτ w hw v).trans hvo
  have hut : u.t = 0 := by rw [Hz_t L hQ π hπ hτ ht, hvt, h]; ring
  have huo : u = o L := by
    have := Hz_eq_id_of_t L hQ π hπ hτ ht hcl u hu hut (o L)
    rwa [Hz_o] at this
  have hagree : Hz L π hπ w hw v = Hz L π hπ w' hw' v := huo.trans hv.symm
  have := (starTree L).eq_of_over (zconnected ht) π hπ _ _ (fun X Y h ↦ Hz_arrow L π hπ w hw h)
    (fun X Y h ↦ Hz_arrow L π hπ w' hw' h) (π_Hz L hQ π hπ hτ w hw) (π_Hz L hQ π hπ hτ w' hw')
    hagree (o L)
  rwa [Hz_o, Hz_o] at this

include hτ in
/-- **Step 4: the deck group is infinite cyclic**, and the fibres of `π` are its
orbits (`periodic-mesh-calculations.tex:179–188`). -/
theorem deck_cyclic (ht : 0 < t) (hcl : t = 1 ∨ t = 3)
    (hnt : ∃ X Y : (starTree L).ZVert, X ≠ Y ∧ π.obj X = π.obj Y) :
    ∃ (z₀ : (starTree L).ZVert) (hz₀ : π.obj z₀ = π.obj (o L)), 0 < z₀.t ∧
      ∀ X Y, π.obj X = π.obj Y ↔ ∃ l : ℤ, ((deck L hQ π hπ hτ ht z₀ hz₀) ^ l) X = Y := by
  let S : AddSubgroup ℤ :=
    { carrier := {n | ∃ (w : (starTree L).ZVert) (_ : π.obj w = π.obj (o L)), w.t = n}
      zero_mem' := ⟨o L, rfl, rfl⟩
      add_mem' := by
        rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
        exact ⟨Hz L π hπ w hw w', (π_Hz L hQ π hπ hτ w hw w').trans hw',
          by rw [Hz_t L hQ π hπ hτ ht]; ring⟩
      neg_mem' := by
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨v, hv⟩ := Hz_surjective L hQ π hπ hτ ht w hw (o L)
        refine ⟨v, by rw [← π_Hz L hQ π hπ hτ w hw v, hv], ?_⟩
        have := Hz_t L hQ π hπ hτ ht w hw v
        rw [hv] at this; simp only [o, B, starDepth] at this
        omega }
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic S
  have hmem : ∀ n, n ∈ S ↔ ∃ m : ℤ, m * a = n := by
    intro n
    rw [ha, AddSubgroup.mem_closure_singleton]
    simp [smul_eq_mul]
  obtain ⟨X, Y, hXY, hπXY⟩ := hnt
  obtain ⟨w, hw, hwXY⟩ := fibre_transitive L hQ π hπ hτ hπXY
  have ha0 : a ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := (hmem w.t).1 ⟨w, hw, rfl⟩
    rw [h0, mul_zero] at hm
    exact hXY ((Hz_eq_id_of_t L hQ π hπ hτ ht hcl w hw hm.symm X).symm.trans hwXY)
  obtain ⟨z₀, hz₀, hz₀t⟩ : |a| ∈ S := by
    rw [hmem]
    rcases abs_choice a with h | h
    · exact ⟨1, by rw [h, one_mul]⟩
    · exact ⟨-1, by rw [h]; ring⟩
  refine ⟨z₀, hz₀, by rw [hz₀t]; exact abs_pos.2 ha0, fun X Y ↦ ⟨fun h ↦ ?_, fun ⟨l, hl⟩ ↦ ?_⟩⟩
  · obtain ⟨w, hw, hwXY⟩ := fibre_transitive L hQ π hπ hτ h
    obtain ⟨m, hm⟩ := (hmem w.t).1 ⟨w, hw, rfl⟩
    have hl : ∃ l : ℤ, l * z₀.t = w.t := by
      rw [hz₀t]
      rcases abs_choice a with h | h
      · exact ⟨m, by rw [h, hm]⟩
      · exact ⟨-m, by rw [h, ← hm]; ring⟩
    obtain ⟨l, hl⟩ := hl
    obtain ⟨u, hu, hut, huX⟩ := deck_zpow L hQ π hπ hτ ht z₀ hz₀ l
    refine ⟨l, ?_⟩
    rw [huX, Hz_congr L π hπ (eq_of_t_eq L hQ π hπ hτ ht hcl hu hw (hut.trans hl)) hu hw, hwXY]
  · obtain ⟨u, hu, -, huX⟩ := deck_zpow L hQ π hπ hτ ht z₀ hz₀ l
    rw [← hl, huX, π_Hz L hQ π hπ hτ]

end Lift

end StarDeck

end MultiplicativeBasisDeformations
