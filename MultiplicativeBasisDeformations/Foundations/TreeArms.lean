import MultiplicativeBasisDeformations.Foundations.TreeBFS
import MultiplicativeBasisDeformations.Foundations.DynkinConfigs
import MultiplicativeBasisDeformations.Foundations.StarModel

/-!
# Parents, children and arms in a finite tree

Proof of Proposition 4.1, Step 2 (`periodic-mesh-calculations.tex:118–140`):
"The tree is consequently a path or has one trivalent vertex. In the latter
case let `p ≤ q ≤ r` be its arm lengths."

Seen from a root `o`, each other vertex has a unique parent (`TreeBFS`); its
other neighbours are its children. This file sets up parents, children and
ancestors.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace MultiplicativeBasisDeformations

universe v

namespace RootedTree

variable {D : Type v} [Fintype D] [DecidableEq D] (G : SimpleGraph D) [DecidableRel G.Adj]
  (par : D → ZMod 2) (hpar : ∀ {u w : D}, G.Adj u w → par w = par u + 1)
  (hG : G.Connected) (hA : G.IsAcyclic) (o : D)

open Classical in
/-- The parent of a vertex, seen from the root `o`. -/
noncomputable def parentOf (v : D) : D :=
  if h : v ≠ o then Classical.choose (TreeBFS.exists_parent hG o h) else o

include hG in
theorem parentOf_spec {v : D} (h : v ≠ o) :
    G.Adj (parentOf G hG o v) v ∧ G.dist o (parentOf G hG o v) + 1 = G.dist o v := by
  unfold parentOf
  rw [dif_pos h]
  exact Classical.choose_spec (TreeBFS.exists_parent hG o h)

/-- `w` is a child of `v`. -/
def IsChild (v w : D) : Prop := G.Adj v w ∧ G.dist o w = G.dist o v + 1

include hA in
theorem eq_parentOf_of_isChild {v w : D} (h : IsChild G o v w) : v = parentOf G hG o w := by
  have hw : w ≠ o := by
    intro hw; subst hw; have := h.2; simp at this
  obtain ⟨h1, h2⟩ := parentOf_spec G hG o hw
  exact TreeBFS.parent_unique hG hA o h.1 h.2.symm h1 h2

theorem isChild_parentOf {w : D} (hw : w ≠ o) : IsChild G o (parentOf G hG o w) w :=
  ⟨(parentOf_spec G hG o hw).1, (parentOf_spec G hG o hw).2.symm⟩

open Classical in
/-- The children of `v`. -/
noncomputable def children (v : D) : Finset D := (G.neighborFinset v).filter (IsChild G o v)

include hpar hG hA in
/-- A vertex other than the root has its parent and its children as neighbours. -/
theorem degree_eq_one_add {v : D} (hv : v ≠ o) :
    G.degree v = 1 + (children G o v).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsplit : G.neighborFinset v = insert (parentOf G hG o v) (children G o v) := by
    ext w
    simp only [Finset.mem_insert, children, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · intro hw
      rcases TreeBFS.dist_adj par hpar hG o hw with h | h
      · exact Or.inr ⟨hw, ⟨hw, h⟩⟩
      · left
        have := isChild_parentOf G hG o hv
        exact (eq_parentOf_of_isChild G hG hA o ⟨hw.symm, h⟩).symm ▸ rfl
    · rintro (rfl | ⟨hw, -⟩)
      · exact (parentOf_spec G hG o hv).1.symm
      · exact hw
  rw [hsplit, Finset.card_insert_of_notMem, add_comm]
  intro hmem
  simp only [children, Finset.mem_filter] at hmem
  have h1 := hmem.2.2
  have h2 := (parentOf_spec G hG o hv).2
  omega

include hpar hG in
theorem degree_root : G.degree o = (children G o o).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp only [children, Finset.mem_filter, SimpleGraph.mem_neighborFinset, IsChild]
  constructor
  · intro hw
    refine ⟨hw, hw, ?_⟩
    rcases TreeBFS.dist_adj par hpar hG o hw with h | h
    · exact h
    · simp at h
  · exact fun h ↦ h.1

/-- The `k`-th ancestor. -/
noncomputable def anc (k : ℕ) (v : D) : D := (parentOf G hG o)^[k] v

theorem anc_succ (k : ℕ) (v : D) : anc G hG o (k + 1) v = parentOf G hG o (anc G hG o k v) :=
  Function.iterate_succ_apply' _ _ _

theorem dist_anc (v : D) : ∀ k ≤ G.dist o v, G.dist o (anc G hG o k v) = G.dist o v - k
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := dist_anc v k (by omega)
      have hne : anc G hG o k v ≠ o := by
        intro h; rw [h, SimpleGraph.dist_self] at ih; omega
      rw [anc_succ]
      have := (parentOf_spec G hG o hne).2
      omega

theorem anc_dist (v : D) : anc G hG o (G.dist o v) v = o := by
  have h := dist_anc G hG o v (G.dist o v) le_rfl
  rw [Nat.sub_self] at h
  exact ((hG.dist_eq_zero_iff).1 h).symm

include par hpar hG hA in
/-- **At most one trivalent vertex** (`periodic-mesh-calculations.tex:122–125`). -/
theorem trivalent_unique {n : D → ℚ} (hn : ∀ i, 0 < n i)
    (hMn : ∀ i, 0 < 2 * n i - ∑ j ∈ G.neighborFinset i, n j) {u w : D}
    (hu : G.degree u = 3) (hw : G.degree w = 3) : u = w := by
  classical
  by_contra huw
  set m := G.dist u w with hm
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero fun h ↦ huw ((hG.dist_eq_zero_iff).1 h)
  let p : Fin (m + 1) → D := fun k ↦ RootedTree.anc G hG u (m - k) w
  have hpd : ∀ k : Fin (m + 1), G.dist u (p k) = k := by
    intro k
    rw [RootedTree.dist_anc G hG u w (m - k) (by omega)]
    omega
  have hp0 : p 0 = u := by
    simp only [p, Fin.val_zero, Nat.sub_zero]; exact RootedTree.anc_dist G hG u w
  have hplast : p (Fin.last m) = w := by simp [p, RootedTree.anc]
  have hpadj : ∀ k : Fin m, G.Adj (p k.castSucc) (p k.succ) := by
    intro k
    have hne : p k.succ ≠ u := by
      intro h; have := hpd k.succ; rw [h, SimpleGraph.dist_self] at this; simp at this
    have e : p k.castSucc = RootedTree.parentOf G hG u (p k.succ) := by
      simp only [p, Fin.val_castSucc, Fin.val_succ]
      rw [← RootedTree.anc_succ]
      congr 1
      omega
    rw [e]
    exact (RootedTree.parentOf_spec G hG u hne).1
  -- two more leaves at `u`
  have hch_u : (children G u u).card = 3 := by rw [← degree_root G par hpar hG u, hu]
  have hp1 : p ⟨1, by omega⟩ ∈ children G u u := by
    simp only [children, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    have hadj := hpadj ⟨0, by omega⟩
    have e0 : p (⟨0, by omega⟩ : Fin m).castSucc = u := hp0
    rw [e0] at hadj
    refine ⟨hadj, hadj, ?_⟩
    rw [hpd, SimpleGraph.dist_self]
  obtain ⟨l0, l1, hl01, hl⟩ := Finset.card_eq_two.1 (by
    rw [Finset.card_erase_of_mem hp1, hch_u] : ((children G u u).erase (p ⟨1, by omega⟩)).card = 2)
  have hl0 : l0 ∈ (children G u u).erase (p ⟨1, by omega⟩) := by rw [hl]; simp
  have hl1 : l1 ∈ (children G u u).erase (p ⟨1, by omega⟩) := by rw [hl]; simp
  -- two leaves at `w`
  have hwu : w ≠ u := fun h ↦ huw h.symm
  have hch_w : (children G u w).card = 2 := by
    have := degree_eq_one_add G par hpar hG hA u hwu
    omega
  obtain ⟨l2, l3, hl23, hl'⟩ := Finset.card_eq_two.1 hch_w
  have hl2 : l2 ∈ children G u w := by rw [hl']; simp
  have hl3 : l3 ∈ children G u w := by rw [hl']; simp
  simp only [Finset.mem_erase, children, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
    IsChild] at hl0 hl1 hl2 hl3
  rw [SimpleGraph.dist_self] at hl0 hl1
  let l : Fin 4 → D := ![l0, l1, l2, l3]
  have hd0 : G.dist u l0 = 1 := by have := hl0.2.2; omega
  have hd1 : G.dist u l1 = 1 := by have := hl1.2.2; omega
  have hd2 : G.dist u l2 = m + 1 := hl2.2.2
  have hd3 : G.dist u l3 = m + 1 := hl3.2.2
  have hpl : ∀ (a : Fin (m + 1)) (j : Fin 4), p a ≠ l j := by
    intro a j h
    have hda := hpd a
    rw [h] at hda
    fin_cases j
    · change p a = l0 at h; change G.dist u l0 = a at hda
      rw [hd0] at hda
      have : a = ⟨1, by omega⟩ := Fin.ext hda.symm
      exact hl0.1 (by rw [← h, this])
    · change p a = l1 at h; change G.dist u l1 = a at hda
      rw [hd1] at hda
      have : a = ⟨1, by omega⟩ := Fin.ext hda.symm
      exact hl1.1 (by rw [← h, this])
    · change G.dist u l2 = a at hda
      rw [hd2] at hda; have := a.2; omega
    · change G.dist u l3 = a at hda
      rw [hd3] at hda; have := a.2; omega
  refine no_two_trivalent G hn hMn p l ?_ hpadj ?_
  · rintro (a | i) (b | j) hab
    · simp only [Sum.elim_inl] at hab
      have h := hpd a
      rw [hab, hpd b] at h
      exact congrArg _ (Fin.ext h.symm)
    · exact absurd hab (hpl a j)
    · exact absurd hab.symm (hpl b i)
    · simp only [Sum.elim_inr] at hab
      congr 1
      fin_cases i <;> fin_cases j <;> simp only [l] at hab ⊢ <;> simp at hab ⊢
      all_goals first
        | rfl
        | exact absurd hab hl01 | exact absurd hab.symm hl01
        | exact absurd hab hl23 | exact absurd hab.symm hl23
        | (have := congrArg (G.dist u) hab; simp only [hd0, hd1, hd2, hd3] at this; omega)
  · intro j
    fin_cases j
    · simpa [l, hp0] using hl0.2.1
    · simpa [l, hp0] using hl1.2.1
    · simpa [l, hplast] using hl2.1
    · simpa [l, hplast] using hl3.1

/-- The child of the root through which the path to `v` passes. -/
noncomputable def top (v : D) : D := anc G hG o (G.dist o v - 1) v

include hG in
theorem dist_pos {v : D} (hv : v ≠ o) : 0 < G.dist o v :=
  Nat.pos_of_ne_zero fun h ↦ hv ((hG.dist_eq_zero_iff).1 h).symm

theorem dist_top {v : D} (hv : v ≠ o) : G.dist o (top G hG o v) = 1 := by
  have := dist_pos G hG o hv
  rw [top, dist_anc G hG o v _ (by omega)]
  omega

theorem top_ne {v : D} (hv : v ≠ o) : top G hG o v ≠ o := by
  intro h; have := dist_top G hG o hv; rw [h, SimpleGraph.dist_self] at this; omega

theorem parentOf_top {v : D} (hv : v ≠ o) : parentOf G hG o (top G hG o v) = o := by
  have := dist_pos G hG o hv
  rw [top, ← anc_succ, show G.dist o v - 1 + 1 = G.dist o v by omega, anc_dist]

theorem top_mem_children {v : D} (hv : v ≠ o) : top G hG o v ∈ children G o o := by
  classical
  have h := isChild_parentOf G hG o (top_ne G hG o hv)
  rw [parentOf_top G hG o hv] at h
  simp only [children, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨h.1, h⟩

theorem top_of_dist_one {v : D} (hv : G.dist o v = 1) : top G hG o v = v := by
  simp [top, hv, anc]

theorem parentOf_ne {v : D} (hv : 2 ≤ G.dist o v) : parentOf G hG o v ≠ o := by
  have hv' : v ≠ o := by intro h; rw [h, SimpleGraph.dist_self] at hv; omega
  intro h
  have := (parentOf_spec G hG o hv').2
  rw [h, SimpleGraph.dist_self] at this
  omega

theorem top_parentOf {v : D} (hv : 2 ≤ G.dist o v) :
    top G hG o (parentOf G hG o v) = top G hG o v := by
  have hv' : v ≠ o := by intro h; rw [h, SimpleGraph.dist_self] at hv; omega
  have hd := (parentOf_spec G hG o hv').2
  unfold top
  rw [show G.dist o (parentOf G hG o v) - 1 = G.dist o v - 2 by omega, anc,
    ← Function.iterate_succ_apply, show (G.dist o v - 2).succ = G.dist o v - 1 by omega]
  rfl

include hA in
/-- **Each arm is a chain**: below each child of the root there is at most one
vertex at each distance, when non-root vertices have at most one child. -/
theorem eq_of_top_eq_of_dist_eq (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) :
    ∀ d : ℕ, ∀ v v' : D, v ≠ o → v' ≠ o → G.dist o v = d + 1 → G.dist o v' = d + 1 →
      top G hG o v = top G hG o v' → v = v' := by
  classical
  intro d
  induction d with
  | zero =>
      intro v v' _ _ hv hv' ht
      rwa [top_of_dist_one G hG o hv, top_of_dist_one G hG o hv'] at ht
  | succ d ih =>
      intro v v' hv0 hv0' hv hv' ht
      have h2 : 2 ≤ G.dist o v := by omega
      have h2' : 2 ≤ G.dist o v' := by omega
      have hp := ih _ _ (parentOf_ne G hG o h2) (parentOf_ne G hG o h2')
        (by have := (parentOf_spec G hG o hv0).2; omega)
        (by have := (parentOf_spec G hG o hv0').2; omega)
        (by rw [top_parentOf G hG o h2, top_parentOf G hG o h2', ht])
      have hc : v ∈ children G o (parentOf G hG o v) := by
        simp only [children, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        exact ⟨(isChild_parentOf G hG o hv0).1, isChild_parentOf G hG o hv0⟩
      have hc' : v' ∈ children G o (parentOf G hG o v) := by
        rw [hp]
        simp only [children, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        exact ⟨(isChild_parentOf G hG o hv0').1, isChild_parentOf G hG o hv0'⟩
      exact Finset.card_le_one.1 (hch _ (parentOf_ne G hG o h2)) _ hc _ hc'

open Classical in
/-- The arm below the child `c` of the root. -/
noncomputable def arm (c : D) : Finset D :=
  Finset.univ.filter fun v ↦ v ≠ o ∧ top G hG o v = c

theorem mem_arm {c v : D} : v ∈ arm G hG o c ↔ v ≠ o ∧ top G hG o v = c := by
  classical
  simp [arm]

theorem self_mem_arm {c : D} (hc : c ∈ children G o o) : c ∈ arm G hG o c := by
  classical
  simp only [children, Finset.mem_filter] at hc
  have hd : G.dist o c = 1 := by rw [hc.2.2, SimpleGraph.dist_self]
  have hne : c ≠ o := by intro h; rw [h, SimpleGraph.dist_self] at hd; omega
  exact (mem_arm G hG o).2 ⟨hne, top_of_dist_one G hG o hd⟩

include hA in
/-- **The distances along an arm are `1, …, |arm|`.** -/
theorem image_dist_arm (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {c : D}
    (hc : c ∈ children G o o) :
    (arm G hG o c).image (G.dist o) = Finset.Icc 1 (arm G hG o c).card := by
  classical
  set S := (arm G hG o c).image (G.dist o)
  have hinj : Set.InjOn (G.dist o) (arm G hG o c) := by
    intro v hv v' hv' h
    rw [Finset.mem_coe, mem_arm] at hv hv'
    obtain ⟨d, hd⟩ : ∃ d, G.dist o v = d + 1 := ⟨G.dist o v - 1, by
      have := dist_pos G hG o hv.1; omega⟩
    exact eq_of_top_eq_of_dist_eq G hG hA o hch d v v' hv.1 hv'.1 hd (h ▸ hd) (hv.2.trans hv'.2.symm)
  have hcard : S.card = (arm G hG o c).card := Finset.card_image_of_injOn hinj
  have hpos : ∀ d ∈ S, 1 ≤ d := by
    intro d hd
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hd
    exact dist_pos G hG o ((mem_arm G hG o).1 hv).1
  have hdown : ∀ d ∈ S, 2 ≤ d → d - 1 ∈ S := by
    intro d hd h2
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hd
    have hv' := (mem_arm G hG o).1 hv
    refine Finset.mem_image.2 ⟨parentOf G hG o v, (mem_arm G hG o).2
      ⟨parentOf_ne G hG o h2, (top_parentOf G hG o h2).trans hv'.2⟩, ?_⟩
    have := (parentOf_spec G hG o hv'.1).2
    omega
  have hne : S.Nonempty := ⟨_, Finset.mem_image_of_mem _ (self_mem_arm G hG o hc)⟩
  set M := S.max' hne
  have hsub : S ⊆ Finset.Icc 1 M := fun d hd ↦
    Finset.mem_Icc.2 ⟨hpos d hd, S.le_max' d hd⟩
  have hsup : Finset.Icc 1 M ⊆ S := by
    have key : ∀ j, j ≤ M - 1 → M - j ∈ S := by
      intro j
      induction j with
      | zero => intro _; simpa using S.max'_mem hne
      | succ j ih =>
          intro hj
          have := hdown _ (ih (by omega)) (by omega)
          rwa [show M - j - 1 = M - (j + 1) by omega] at this
    intro d hd
    rw [Finset.mem_Icc] at hd
    have := key (M - d) (by omega)
    rwa [show M - (M - d) = d by omega] at this
  have hS : S = Finset.Icc 1 M := Finset.Subset.antisymm hsub hsup
  rw [← hcard, hS, Nat.card_Icc, Nat.add_sub_cancel]

open Classical in
/-- The vertex of the arm below `c` at distance `d`. -/
noncomputable def armVert (c : D) (d : ℕ) : D :=
  if h : ∃ v ∈ arm G hG o c, G.dist o v = d then Classical.choose h else o

include hA in
theorem armVert_spec (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {c : D}
    (hc : c ∈ children G o o) {d : ℕ} (hd1 : 1 ≤ d) (hd2 : d ≤ (arm G hG o c).card) :
    armVert G hG o c d ∈ arm G hG o c ∧ G.dist o (armVert G hG o c d) = d := by
  classical
  have hex : ∃ v ∈ arm G hG o c, G.dist o v = d := by
    have : d ∈ (arm G hG o c).image (G.dist o) := by
      rw [image_dist_arm G hG hA o hch hc]; exact Finset.mem_Icc.2 ⟨hd1, hd2⟩
    simpa using this
  unfold armVert
  rw [dif_pos hex]
  exact Classical.choose_spec hex

include hA in
theorem armVert_dist (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {c v : D}
    (hc : c ∈ children G o o) (hv : v ∈ arm G hG o c) : armVert G hG o c (G.dist o v) = v := by
  classical
  have hd : G.dist o v ∈ (arm G hG o c).image (G.dist o) := Finset.mem_image_of_mem _ hv
  rw [image_dist_arm G hG hA o hch hc, Finset.mem_Icc] at hd
  obtain ⟨h1, h2⟩ := armVert_spec G hG hA o hch hc hd.1 hd.2
  have hv' := (mem_arm G hG o).1 hv
  have h1' := (mem_arm G hG o).1 h1
  obtain ⟨d, hdd⟩ : ∃ d, G.dist o v = d + 1 := ⟨G.dist o v - 1, by omega⟩
  exact eq_of_top_eq_of_dist_eq G hG hA o hch d _ _ h1'.1 hv'.1 (h2.trans hdd) hdd
    (h1'.2.trans hv'.2.symm)

/-- An enumeration of the children of the root. -/
noncomputable def enum : Fin (children G o o).card ≃ (children G o o) :=
  (children G o o).equivFin.symm

/-- The arm lengths, minus one. -/
noncomputable def armLen (i : Fin (children G o o).card) : ℕ :=
  (arm G hG o (enum G o i).1).card - 1

theorem card_arm_pos {c : D} (hc : c ∈ children G o o) : 1 ≤ (arm G hG o c).card :=
  Finset.card_pos.2 ⟨c, self_mem_arm G hG o hc⟩

theorem armLen_add_one (i : Fin (children G o o).card) :
    armLen G hG o i + 1 = (arm G hG o (enum G o i).1).card := by
  have := card_arm_pos G hG o (enum G o i).2
  unfold armLen; omega

include hA in
theorem dist_le_card_arm (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {v : D} (hv : v ≠ o) :
    G.dist o v ≤ (arm G hG o (top G hG o v)).card := by
  classical
  have hmem : v ∈ arm G hG o (top G hG o v) := (mem_arm G hG o).2 ⟨hv, rfl⟩
  have hd : G.dist o v ∈ (arm G hG o (top G hG o v)).image (G.dist o) :=
    Finset.mem_image_of_mem _ hmem
  rw [image_dist_arm G hG hA o hch (top_mem_children G hG o hv), Finset.mem_Icc] at hd
  exact hd.2

open Classical in
/-- **The isomorphism with the star model**, on vertices. -/
noncomputable def toStarV (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) (v : D) :
    StarV (armLen G hG o) :=
  if h : v = o then none else
    some ⟨(enum G o).symm ⟨top G hG o v, top_mem_children G hG o h⟩,
      ⟨G.dist o v - 1, by
        rw [armLen_add_one, Equiv.apply_symm_apply]
        show G.dist o v - 1 < (arm G hG o (top G hG o v)).card
        have := dist_le_card_arm G hG hA o hch h
        have := dist_pos G hG o h
        omega⟩⟩

/-- The inverse of `toStarV`. -/
noncomputable def fromStarV : StarV (armLen G hG o) → D
  | none => o
  | some x => armVert G hG o (enum G o x.1).1 (x.2 + 1)

theorem fromStarV_toStarV (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) (v : D) :
    fromStarV G hG o (toStarV G hG hA o hch v) = v := by
  classical
  unfold toStarV
  split_ifs with h
  · exact h.symm
  · simp only [fromStarV, Equiv.apply_symm_apply]
    have := dist_pos G hG o h
    rw [show G.dist o v - 1 + 1 = G.dist o v by omega]
    exact armVert_dist G hG hA o hch (top_mem_children G hG o h) ((mem_arm G hG o).2 ⟨h, rfl⟩)

theorem toStarV_fromStarV (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1)
    (x : StarV (armLen G hG o)) : toStarV G hG hA o hch (fromStarV G hG o x) = x := by
  classical
  rcases x with _ | ⟨i, k⟩
  · simp [fromStarV, toStarV]
  · have hc := (enum G o i).2
    have hk : k.1 + 1 ≤ (arm G hG o (enum G o i).1).card := by
      rw [← armLen_add_one]; omega
    obtain ⟨hmem, hd⟩ := armVert_spec G hG hA o hch hc (by omega) hk
    have hmem' := (mem_arm G hG o).1 hmem
    simp only [fromStarV]
    unfold toStarV
    rw [dif_neg hmem'.1]
    congr 1
    have hi : (enum G o).symm ⟨top G hG o (armVert G hG o (enum G o i).1 (k + 1)),
        top_mem_children G hG o hmem'.1⟩ = i := by
      rw [Equiv.symm_apply_eq]; exact Subtype.ext hmem'.2
    refine Sigma.ext hi ?_
    rw [Fin.heq_ext_iff (congrArg (fun j ↦ armLen G hG o j + 1) hi)]
    simp only [hd, Nat.add_sub_cancel]

include hpar in
theorem adj_toStarV_aux (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {u v : D}
    (h : G.Adj u v) (hd : G.dist o v = G.dist o u + 1) :
    starAdj (toStarV G hG hA o hch u) (toStarV G hG hA o hch v) := by
  classical
  have hv : v ≠ o := by intro e; rw [e, SimpleGraph.dist_self] at hd; omega
  have hpu : u = parentOf G hG o v := eq_parentOf_of_isChild G hG hA o ⟨h, hd⟩
  by_cases hu : u = o
  · subst hu
    unfold toStarV
    rw [dif_pos rfl, dif_neg hv]
    simp only [starAdj]
    rw [hd, SimpleGraph.dist_self]
  · have h2 : 2 ≤ G.dist o v := by have := dist_pos G hG o hu; omega
    have ht : top G hG o u = top G hG o v := by rw [hpu]; exact top_parentOf G hG o h2
    unfold toStarV
    rw [dif_neg hu, dif_neg hv]
    simp only [starAdj]
    refine ⟨by simp only [ht], Or.inl ?_⟩
    have := dist_pos G hG o hu
    omega

include hpar in
theorem adj_toStarV (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {u v : D} (h : G.Adj u v) :
    starAdj (toStarV G hG hA o hch u) (toStarV G hG hA o hch v) := by
  rcases TreeBFS.dist_adj par hpar hG o h with hd | hd
  · exact adj_toStarV_aux G par hpar hG hA o hch h hd
  · exact (starGraph (armLen G hG o)).symm.symm _ _
      (adj_toStarV_aux G par hpar hG hA o hch h.symm hd)

include hA in
theorem armVert_one (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {c : D}
    (hc : c ∈ children G o o) : armVert G hG o c 1 = c := by
  classical
  have hmem := self_mem_arm G hG o hc
  have hd : G.dist o c = 1 := by
    simp only [children, Finset.mem_filter] at hc
    rw [hc.2.2, SimpleGraph.dist_self]
  have := armVert_dist G hG hA o hch hc hmem
  rwa [hd] at this

include hA in
theorem adj_armVert_succ (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) {c : D}
    (hc : c ∈ children G o o) (k : ℕ) (hk : k + 2 ≤ (arm G hG o c).card) :
    G.Adj (armVert G hG o c (k + 1)) (armVert G hG o c (k + 2)) := by
  obtain ⟨hb, hdb⟩ := armVert_spec G hG hA o hch hc (by omega) hk
  obtain ⟨ha, hda⟩ := armVert_spec G hG hA o hch hc (d := k + 1) (by omega) (by omega)
  have hb' := (mem_arm G hG o).1 hb
  have ha' := (mem_arm G hG o).1 ha
  have h2 : 2 ≤ G.dist o (armVert G hG o c (k + 2)) := by omega
  have hp : parentOf G hG o (armVert G hG o c (k + 2)) = armVert G hG o c (k + 1) := by
    refine eq_of_top_eq_of_dist_eq G hG hA o hch k _ _ (parentOf_ne G hG o h2) ha'.1 ?_ hda ?_
    · have := (parentOf_spec G hG o hb'.1).2; omega
    · rw [top_parentOf G hG o h2, hb'.2, ha'.2]
  rw [← hp]
  exact (parentOf_spec G hG o hb'.1).1

include hA in
theorem adj_fromStarV (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1)
    {x y : StarV (armLen G hG o)} (h : starAdj x y) :
    G.Adj (fromStarV G hG o x) (fromStarV G hG o y) := by
  classical
  have hroot : ∀ (i : Fin (children G o o).card) (k : Fin (armLen G hG o i + 1)), (k : ℕ) = 0 →
      G.Adj o (fromStarV G hG o (some ⟨i, k⟩)) := by
    intro i k hk
    simp only [fromStarV, hk, zero_add]
    rw [armVert_one G hG hA o hch (enum G o i).2]
    have := (enum G o i).2
    simp only [children, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at this
    exact this.1
  have harm : ∀ (i : Fin (children G o o).card) (k l : Fin (armLen G hG o i + 1)),
      (l : ℕ) = k + 1 →
      G.Adj (fromStarV G hG o (some ⟨i, k⟩)) (fromStarV G hG o (some ⟨i, l⟩)) := by
    intro i k l hl
    simp only [fromStarV, hl]
    exact adj_armVert_succ G hG hA o hch (enum G o i).2 k (by
      rw [← armLen_add_one]; have := l.2; omega)
  rcases x with _ | ⟨i, k⟩ <;> rcases y with _ | ⟨j, l⟩ <;> simp only [starAdj] at h
  · exact hroot j l h
  · exact (hroot i k h).symm
  · obtain ⟨rfl, h | h⟩ := h
    · exact harm i k l h
    · exact (harm i l k h).symm

/-- The isomorphism with the star model, as an equivalence. -/
noncomputable def starEquiv (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) :
    D ≃ StarV (armLen G hG o) where
  toFun := toStarV G hG hA o hch
  invFun := fromStarV G hG o
  left_inv := fromStarV_toStarV G hG hA o hch
  right_inv := toStarV_fromStarV G hG hA o hch

include hpar in
theorem adj_iff_starAdj (hch : ∀ v, v ≠ o → (children G o v).card ≤ 1) (u v : D) :
    G.Adj u v ↔ starAdj (starEquiv G hG hA o hch u) (starEquiv G hG hA o hch v) := by
  refine ⟨adj_toStarV G par hpar hG hA o hch, fun h ↦ ?_⟩
  have := adj_fromStarV G hG hA o hch h
  simp only [starEquiv, Equiv.coe_fn_mk] at this
  rwa [fromStarV_toStarV, fromStarV_toStarV] at this

include par hpar hG hA in
/-- **Proposition 4.1, Step 2: the tree is Dynkin.** A finite tree carrying a
vector `n > 0` with `Mn > 0` is a star with at most one arm (a path rooted at
an end) or with three arms satisfying `∑ p_i/(p_i + 1) < 2`
(`periodic-mesh-calculations.tex:118–140`). -/
theorem classify_tree [Nonempty D] {n : D → ℚ}
    (hn : ∀ i, 0 < n i) (hMn : ∀ i, 0 < 2 * n i - ∑ j ∈ G.neighborFinset i, n j) :
    ∃ (t : ℕ) (L : Fin t → ℕ) (e : D ≃ StarV L),
      (∀ u v, G.Adj u v ↔ starAdj (e u) (e v)) ∧
      (t ≤ 1 ∨ (t = 3 ∧ ∑ i, ((L i : ℚ) + 1) / (L i + 2) < 2)) := by
  classical
  by_cases h3 : ∃ o, G.degree o = 3
  · obtain ⟨o, ho⟩ := h3
    have hch : ∀ v, v ≠ o → (children G o v).card ≤ 1 := by
      intro v hv
      have h1 := degree_le_three G hn hMn v
      have h2 : G.degree v ≠ 3 := fun h ↦ hv (trivalent_unique G par hpar hG hA hn hMn h ho)
      have := degree_eq_one_add G par hpar hG hA o hv
      omega
    have ht : (children G o o).card = 3 := by rw [← degree_root G par hpar hG o, ho]
    refine ⟨_, armLen G hG o, starEquiv G hG hA o hch, adj_iff_starAdj G par hpar hG hA o hch,
      Or.inr ⟨ht, ?_⟩⟩
    have hinj : Function.Injective (Sum.elim (fun _ : Unit ↦ o)
        (fun x : Σ i, Fin (armLen G hG o i + 1) ↦ fromStarV G hG o (some x))) := by
      intro a b hab
      have key : ∀ y : Unit ⊕ (Σ i, Fin (armLen G hG o i + 1)),
          Sum.elim (fun _ : Unit ↦ o) (fun x ↦ fromStarV G hG o (some x)) y =
            fromStarV G hG o (Sum.elim (fun _ ↦ none) some y) := by
        rintro (u | x) <;> rfl
      rw [key, key] at hab
      have := congrArg (toStarV G hG hA o hch) hab
      rw [toStarV_fromStarV, toStarV_fromStarV] at this
      rcases a with ⟨⟩ | x <;> rcases b with ⟨⟩ | y <;> simp_all
    exact arm_inequality G hn hMn (armLen G hG o) o (fun i k ↦ fromStarV G hG o (some ⟨i, k⟩))
      hinj (fun i ↦ adj_fromStarV G hG hA o hch (x := none) (y := some ⟨i, 0⟩) rfl)
      (fun i k ↦ adj_fromStarV G hG hA o hch (x := some ⟨i, k.castSucc⟩) (y := some ⟨i, k.succ⟩)
        ⟨rfl, Or.inl rfl⟩)
  · push_neg at h3
    have hdeg2 : ∀ v, G.degree v ≤ 2 := fun v ↦ by
      have := degree_le_three G hn hMn v; have := h3 v; omega
    obtain ⟨r⟩ := ‹Nonempty D›
    obtain ⟨o, -, hmax⟩ := Finset.exists_max_image Finset.univ (G.dist r) Finset.univ_nonempty
    have hdo : G.degree o ≤ 1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      by_cases hor : o = r
      · subst hor
        rw [Finset.card_le_one]
        intro a ha
        exfalso
        rw [SimpleGraph.mem_neighborFinset] at ha
        have := hmax a (Finset.mem_univ _)
        rcases TreeBFS.dist_adj par hpar hG o ha with h | h
        · rw [SimpleGraph.dist_self] at h this; omega
        · rw [SimpleGraph.dist_self] at h; omega
      · rw [Finset.card_le_one]
        intro a ha b hb
        rw [SimpleGraph.mem_neighborFinset] at ha hb
        have hpa : ∀ w, G.Adj o w → w = parentOf G hG r o := by
          intro w hw
          rcases TreeBFS.dist_adj par hpar hG r hw with h | h
          · have := hmax w (Finset.mem_univ _); omega
          · exact eq_parentOf_of_isChild G hG hA r ⟨hw.symm, h⟩
        rw [hpa a ha, hpa b hb]
    have hch : ∀ v, v ≠ o → (children G o v).card ≤ 1 := by
      intro v hv
      have := degree_eq_one_add G par hpar hG hA o hv
      have := hdeg2 v
      omega
    refine ⟨_, armLen G hG o, starEquiv G hG hA o hch, adj_iff_starAdj G par hpar hG hA o hch,
      Or.inl ?_⟩
    rw [← degree_root G par hpar hG o]
    exact hdo

end RootedTree

end MultiplicativeBasisDeformations
