import MultiplicativeBasisDeformations.Foundations.MorseCollapse
import MultiplicativeBasisDeformations.Foundations.MeshCategory

/-!
# The mesh complex `K` and its collapse

Subsection 4.1 (`subsec:mesh-walk-cover`, `scalar-normalization.tex:21–35`):
"For every nonprojective vertex `X`, adjoin an edge `t_X : τX → X` to the
underlying graph of `Γ`. For each arrow `a : Y → X` with `X` nonprojective,
attach a triangle with boundary `(σa) a t_X⁻¹`." Its fundamental groupoid is
`Morse.Pi (meshTris Q)`.

The proof of Lemma 4.2 (`lem:mesh-walk-free`, lines 96–113) eliminates edges
and triangles. Here the eliminations are an acyclic matching (`meshMatching`):

* an arrow whose mate orbit is a finite chain is eliminated with its own
  triangle, from the end of the chain ("Along a chain, the triangles
  successively express all but one quiver edge in terms of that edge and the
  edges `t_X`. Eliminate these edges and triangles from one end of the
  chain"); the potential is the remaining length of the chain;
* on the arrows with cyclic mate orbits (the periodic components) the matching
  is read off from a depth function `e` on vertices that is invariant under
  `τ` and such that each vertex has at most one cyclic incoming arrow from a
  vertex of depth at most its own: the triangle of the arrow from the parent
  eliminates `t_X`, the other triangles eliminate their arrow. This is the
  combinatorial form of "a periodic component containing arrows gives a
  mapping torus, which retracts onto its core circle"; the depth function is
  constructed from the tree model in `PeriodicDepth.lean`.

Once every triangle is eliminated, the remaining complex is a graph and the
vertex groups are free (`Morse.isFreeGroup_end`).
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations.MeshWalk

variable {V : Type} [Quiver.{0} V] (Q : TranslationQuiver V)

/-- Arrows of the quiver. -/
abbrev Arr (V : Type) [Quiver.{0} V] := Σ Y : V, Σ X : V, Y ⟶ X

/-- `σ^j a` is defined for all `j < n`. -/
def MateChain : Arr V → ℕ → Prop
  | _, 0 => True
  | ⟨Y, X, a⟩, n + 1 => ∃ h : X ∈ Q.nonprojective,
      MateChain ⟨(Q.tau ⟨X, h⟩).1, Y, Q.mate ⟨X, h⟩ Y a⟩ n

/-- An arrow whose mate orbit is a cycle: all powers of `σ` are defined. -/
def Cyclic (A : Arr V) : Prop := ∀ n, MateChain Q A n

/-- The edges of `K`: the arrows and the translation edges `t_X`. -/
abbrev Ed := Arr V ⊕ Q.nonprojective

/-- Source of an edge. -/
def src : Ed Q → V
  | Sum.inl A => A.1
  | Sum.inr x => (Q.tau x).1

/-- Target of an edge. -/
def tgt : Ed Q → V
  | Sum.inl A => A.2.1
  | Sum.inr x => x.1

/-- The triangles of `K`: one for each arrow `a : y → x` with `x` nonprojective. -/
abbrev Tri := Σ x : Q.nonprojective, Σ y : V, y ⟶ x.1

/-- The arrow of a triangle. -/
def Tri.arr {Q : TranslationQuiver V} (t : Tri Q) : Arr V := ⟨t.2.1, t.1.1, t.2.2⟩

/-- The mate arrow `σ a : τ x → y` of a triangle. -/
def Tri.mateArr {Q : TranslationQuiver V} (t : Tri Q) : Arr V :=
  ⟨(Q.tau t.1).1, t.2.1, Q.mate t.1 t.2.1 t.2.2⟩

/-- The mesh complex: triangles `(σa) a = t_X`. -/
def meshTris : Morse.Tris (src Q) (tgt Q) where
  T := Tri Q
  f t := Sum.inl t.mateArr
  g t := Sum.inl t.arr
  h t := Sum.inr t.1
  hfg _ := rfl
  hfh _ := rfl
  hgh _ := rfl

variable {Q}

theorem cyclic_mate (t : Tri Q) (h : Cyclic Q t.arr) : Cyclic Q t.mateArr := by
  intro n
  obtain ⟨hx, hc⟩ := h (n + 1)
  exact hc

theorem cyclic_of_mate (t : Tri Q) (h : Cyclic Q t.mateArr) : Cyclic Q t.arr := by
  rintro (_ | n)
  · trivial
  · exact ⟨t.1.2, h n⟩

open Classical in
/-- The remaining length of a finite mate chain. -/
def len (A : Arr V) : ℕ := if h : ∃ n, ¬ MateChain Q A n then Nat.find h else 0

theorem len_mate (t : Tri Q) (h : ¬ Cyclic Q t.arr) :
    len (Q := Q) t.mateArr + 1 = len (Q := Q) t.arr := by
  classical
  have h' : ¬ Cyclic Q t.mateArr := fun hc ↦ h (cyclic_of_mate t hc)
  unfold Cyclic at h h'
  push Not at h h'
  have key : ∀ n, MateChain Q t.arr (n + 1) ↔ MateChain Q t.mateArr n :=
    fun n ↦ ⟨fun ⟨_, hc⟩ ↦ hc, fun hc ↦ ⟨t.1.2, hc⟩⟩
  unfold len
  rw [dif_pos h, dif_pos h']
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec h
    cases hN : Nat.find h with
    | zero => rw [hN] at hspec; exact hspec trivial
    | succ m =>
        rw [hN] at hspec hlt
        rw [key] at hspec
        exact Nat.find_min h' (by omega) hspec
  · apply Nat.find_min' h
    rw [key]
    exact Nat.find_spec h'

theorem arr_injective {t t' : Tri Q} (h : t'.arr = t.arr) : t' = t := by
  rcases t with ⟨⟨x, hx⟩, y, a⟩
  rcases t' with ⟨⟨x', hx'⟩, y', a'⟩
  simp only [Tri.arr, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h⟩ := (Sigma.mk.inj_iff).1 (eq_of_heq h)
  cases eq_of_heq h
  rfl

theorem arr_fst {t : Tri Q} {A : Arr V} (h : t.arr = A) : t.2.1 = A.1 := by
  rw [← h]; rfl

theorem arr_snd {t : Tri Q} {A : Arr V} (h : t.arr = A) : t.1.1 = A.2.1 := by
  rw [← h]; rfl

/-- A depth function on the vertices, adapted to the cyclic arrows. -/
structure Depth (Q : TranslationQuiver V) where
  /-- the depth -/
  e : V → ℕ
  /-- invariance under `τ` along cyclic arrows -/
  tau_eq : ∀ t : Tri Q, Cyclic Q t.arr → e (Q.tau t.1).1 = e t.1.1
  /-- at most one cyclic arrow into a vertex comes from depth at most its own -/
  uniq : ∀ t t' : Tri Q, t.1 = t'.1 → Cyclic Q t.arr → Cyclic Q t'.arr →
    e t.2.1 ≤ e t.1.1 → e t'.2.1 ≤ e t'.1.1 → t = t'

variable (D : Depth Q)

/-- The condition for a triangle to eliminate its translation edge. -/
def Up (t : Tri Q) : Prop := Cyclic Q t.arr ∧ D.e t.2.1 ≤ D.e t.1.1

theorem edge_zero (t : Tri Q) : (meshTris Q).edge t 0 = Sum.inl t.mateArr := rfl
theorem edge_one (t : Tri Q) : (meshTris Q).edge t 1 = Sum.inl t.arr := rfl
theorem edge_two (t : Tri Q) : (meshTris Q).edge t 2 = Sum.inr t.1 := rfl

open Classical in
theorem matched_inr {t : Tri Q} {x : Q.nonprojective}
    (h : (meshTris Q).edge t (if Up D t then 2 else 1) = Sum.inr x) : t.1 = x ∧ Up D t := by
  split_ifs at h with hu
  · exact ⟨Sum.inr_injective h, hu⟩
  · rw [edge_one] at h; exact absurd h Sum.inl_ne_inr

open Classical in
theorem matched_inl {t : Tri Q} {A : Arr V}
    (h : (meshTris Q).edge t (if Up D t then 2 else 1) = Sum.inl A) : t.arr = A ∧ ¬ Up D t := by
  split_ifs at h with hu
  · rw [edge_two] at h; exact absurd h Sum.inr_ne_inl
  · exact ⟨Sum.inl_injective h, hu⟩

variable [Fintype V]

/-- A bound above all the periodic potentials. -/
def B : ℕ := ∑ v, (2 * D.e v + 2)

theorem lt_B (v : V) : 2 * D.e v + 1 < B D := by
  have : 2 * D.e v + 2 ≤ B D :=
    Finset.single_le_sum (f := fun v ↦ 2 * D.e v + 2) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ v)
  omega

open Classical in
/-- The potential of a triangle. -/
def pot (t : Tri Q) : ℕ :=
  if Cyclic Q t.arr then (if D.e t.2.1 ≤ D.e t.1.1 then 2 * D.e t.1.1 else 2 * D.e t.1.1 + 1)
    else B D + len (Q := Q) t.arr

theorem pot_up {t : Tri Q} (hu : Up D t) : pot D t = 2 * D.e t.1.1 := by
  simp [pot, hu.1, hu.2]

theorem pot_down {t : Tri Q} (hc : Cyclic Q t.arr) (hd : D.e t.1.1 < D.e t.2.1) :
    pot D t = 2 * D.e t.1.1 + 1 := by
  simp [pot, hc, not_le.2 hd]

theorem pot_chain {t : Tri Q} (hc : ¬ Cyclic Q t.arr) : pot D t = B D + len (Q := Q) t.arr := by
  simp [pot, hc]

theorem pot_ge {t : Tri Q} : 2 * D.e t.1.1 ≤ pot D t := by
  have := lt_B D t.1.1
  unfold pot
  split_ifs <;> omega

open Classical in
/-- **The matching of the mesh complex.** -/
def meshMatching : Morse.Matching (meshTris Q) where
  m t := if Up D t then 2 else 1
  inj := by
    intro t t' h
    simp only at h
    by_cases hu : Up D t
    · have h1 : (meshTris Q).edge t (if Up D t then 2 else 1) = Sum.inr t.1 := by
        rw [if_pos hu]; rfl
      obtain ⟨he, hu'⟩ := matched_inr D (h.symm.trans h1)
      exact D.uniq t t' he.symm hu.1 hu'.1 hu.2 hu'.2
    · have h1 : (meshTris Q).edge t (if Up D t then 2 else 1) = Sum.inl t.arr := by
        rw [if_neg hu]; rfl
      obtain ⟨he, -⟩ := matched_inl D (h.symm.trans h1)
      exact (arr_injective he).symm
  pot := pot D
  dec := by
    intro (t : Tri Q) i hi (t' : Tri Q) ht'
    change i ≠ (if Up D t then 2 else 1) at hi
    change (meshTris Q).edge t' (if Up D t' then 2 else 1) = (meshTris Q).edge t i at ht'
    change pot D t' < pot D t
    fin_cases i
    · -- the mate arrow
      change _ = Sum.inl t.mateArr at ht'
      obtain ⟨ha, hu⟩ := matched_inl D ht'
      have h1 := arr_fst ha
      have h2 := arr_snd ha
      simp only [Tri.mateArr] at h1 h2
      by_cases hc : Cyclic Q t.arr
      · have hc' : Cyclic Q t'.arr := ha ▸ cyclic_mate t hc
        have hlt : D.e t'.1.1 < D.e t'.2.1 := by
          by_contra hle
          exact hu ⟨hc', not_lt.1 hle⟩
        have hτ := D.tau_eq t hc
        rw [h1, h2, hτ] at hlt
        have hup : Up D t := ⟨hc, hlt.le⟩
        rw [pot_down D hc' (by rw [h1, h2, hτ]; exact hlt), pot_up D hup, h2]
        omega
      · have hc' : ¬ Cyclic Q t'.arr := fun h' ↦ hc (cyclic_of_mate t (ha ▸ h'))
        have hl := len_mate t hc
        rw [pot_chain D hc', pot_chain D hc, ha]
        omega
    · -- the arrow itself: then `t` eliminates `t_x`
      have hu : Up D t := by
        by_contra hu
        apply hi
        simp [hu]
      change _ = Sum.inl t.arr at ht'
      obtain ⟨ha, hu'⟩ := matched_inl D ht'
      exact absurd (arr_injective ha ▸ hu) hu'
    · -- the translation edge
      have hu : ¬ Up D t := by
        intro hu
        apply hi
        simp [hu]
      change _ = Sum.inr t.1 at ht'
      obtain ⟨hx, hu'⟩ := matched_inr D ht'
      rw [pot_up D hu', hx]
      by_cases hc : Cyclic Q t.arr
      · have hd : D.e t.1.1 < D.e t.2.1 := not_le.1 fun h ↦ hu ⟨hc, h⟩
        rw [pot_down D hc hd]
        omega
      · rw [pot_chain D hc]
        have := lt_B D t.1.1
        omega

variable (Q) in
/-- The fundamental groupoid `Π(K)` of the mesh complex: walks modulo cancellation
and the triangle relations. -/
abbrev PiK := Morse.Pi (meshTris Q)

variable (Q) in
/-- A vertex of `Γ` as an object of `Π(K)`. -/
abbrev obK (X : V) : PiK Q := (Morse.Qf (S := meshTris Q)).obj (Morse.ob (src Q) (tgt Q) X)

include D in
/-- **The vertex groups of `K` are free**, given a depth function on the
periodic part. -/
theorem isFreeGroup_end_of_depth (X : V) : IsFreeGroup (End (obK Q X)) :=
  Morse.isFreeGroup_end (meshMatching D) X

end MultiplicativeBasisDeformations.MeshWalk
