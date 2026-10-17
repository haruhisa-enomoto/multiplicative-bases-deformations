import MultiplicativeBasisDeformations.Foundations.MeshDerivativeRows

/-!
# Periodic localization of the mesh derivative

Proposition 5.1 (`prop:periodic-localization`, `mesh-deformations.tex`).

A correction column has at most two entries (`column_eq`). On a row `(x, w)`
with `w = p a` and `a : y → x`, the column `(σ a, p)` connects the row to its
*rotation* `(y, (σ σ a) p)` when `y` is nonprojective, and has the row as its
only entry when `y` is projective. Rotating moves every vertex of the path one
step to the right and brings in the translate of the vertex before the last
one; after `d` rotations a row is translated by `τ`. A row with a vertex that
is not `τ`-periodic therefore reaches a one-entry column after finitely many
rotations, and elimination from that end puts it in the image of `D_m`
(`row_mem_imageD_of_not_periodic`).

The counting is organized by the potential `d·δ(v_i) + (d - 1 - i)`, minimized
over the positions `i < d` of the path, where `δ(v)` is the number of times `τ`
can be applied to `v`. One rotation lowers it by exactly one.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] (Q : TranslationQuiver V)

/-- `τ^j v` is defined for all `j < n`. -/
def TauChain : V → ℕ → Prop
  | _, 0 => True
  | v, n + 1 => ∃ h : v ∈ Q.nonprojective, TauChain (Q.tau ⟨v, h⟩).1 n

/-- A vertex on which every power of `τ` is defined. On a finite quiver these
are the vertices on the cycles of `τ` (`isTauPeriodic_iff`). -/
def IsTauPeriodic (v : V) : Prop := ∀ n, Q.TauChain v n

variable {Q}

theorem tauChain_succ_iff (v : V) (n : ℕ) :
    Q.TauChain v (n + 1) ↔ ∃ h : v ∈ Q.nonprojective, Q.TauChain (Q.tau ⟨v, h⟩).1 n := Iff.rfl

theorem TauChain.mono : ∀ {v : V} {n n' : ℕ}, n' ≤ n → Q.TauChain v n → Q.TauChain v n'
  | _, _, 0, _, _ => trivial
  | _, 0, _ + 1, h, _ => absurd h (by omega)
  | _, _ + 1, _ + 1, h, ⟨hv, hc⟩ => ⟨hv, TauChain.mono (by omega) hc⟩

end TranslationQuiver

namespace ScalarMeshCategory

open TranslationQuiver

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q) [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]
  [DecidablePred (· ∈ Q.nonprojective)]

theorem single_mem_familiesDeg {m : ℕ} {u v : V} (a : u ⟶ v) (p : Quiver.Path u v)
    (hp : p.length = m) :
    Pi.single (⟨u, v, a⟩ : Σ u v : V, u ⟶ v) (pathMor c p) ∈ familiesDeg c m := by
  intro b
  by_cases hb : b = ⟨u, v, a⟩
  · subst hb
    rw [Pi.single_eq_same, ← hp]
    exact pathMor_mem_degreePart c p
  · rw [Pi.single_eq_of_ne hb]
    exact zero_mem _

/-- One step of the rotation: a row `(x, p a)` is in the image of `D_m` if `y`
is projective, and otherwise exactly when its rotation `(y, (σ σ a) p)` is. -/
theorem row_mem_imageD_of_rotation {m : ℕ} (x : Q.nonprojective) {y : V} (a : y ⟶ x.1)
    (p : Quiver.Path (Q.tau x).1 y) (hp : p.length = m)
    (hrot : ∀ hy : y ∈ Q.nonprojective,
      row c ⟨y, hy⟩ ((Q.mate ⟨y, hy⟩ (Q.tau x).1 (Q.mate x y a)).toPath.comp p) ∈ imageD c m) :
    row c x (p.cons a) ∈ imageD c m := by
  have hcol : meshDerivative c (Pi.single (⟨(Q.tau x).1, y, Q.mate x y a⟩ : Σ u v : V, u ⟶ v)
      (pathMor c p)) ∈ imageD c m :=
    ⟨_, single_mem_familiesDeg c _ p hp, rfl⟩
  rw [column_eq] at hcol
  have hrest : (if hy : y ∈ Q.nonprojective then
      ((c ⟨y, hy⟩ (Q.tau x).1 (Q.mate x y a) : kˣ) : k) •
        row c ⟨y, hy⟩ ((Q.mate ⟨y, hy⟩ (Q.tau x).1 (Q.mate x y a)).toPath.comp p)
      else 0) ∈ imageD c m := by
    split_ifs with hy
    · exact Submodule.smul_mem _ _ (hrot hy)
    · exact zero_mem _
  have h := sub_mem hcol hrest
  rw [add_sub_cancel_right] at h
  have := Submodule.smul_mem _ (((c x y a : kˣ)⁻¹ : kˣ) : k) h
  rwa [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at this

/-- The vertices of the rotated path, without its endpoint. -/
theorem vertices_rotate {x' y z : V} (b : x' ⟶ y) (p : Quiver.Path y z) {z' : V}
    (p' : Quiver.Path x' z') (a' : z' ⟶ z) (h : b.toPath.comp p = p'.cons a') :
    p'.vertices = x' :: p.vertices.dropLast := by
  have h1 := congrArg Quiver.Path.vertices h
  rw [Quiver.Path.vertices_comp, Quiver.Path.vertices_cons, Quiver.Path.vertices_toPath] at h1
  have h2 := congrArg List.dropLast h1
  rw [List.concat_eq_append, List.dropLast_concat] at h2
  rw [← h2]
  simp [List.dropLast_cons_of_ne_nil p.vertices_ne_nil]

omit [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]
  [DecidablePred (· ∈ Q.nonprojective)] in
theorem exists_eq_cons {a b : V} (q : Quiver.Path a b) (hq : 0 < q.length) :
    ∃ (z : V) (q' : Quiver.Path a z) (e : z ⟶ b), q = q'.cons e := by
  cases q with
  | nil => simp at hq
  | cons q' e => exact ⟨_, q', e, rfl⟩

omit [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]
  [DecidablePred (· ∈ Q.nonprojective)] in
theorem vertices_getElem_length {a b : V} (q : Quiver.Path a b)
    (h : q.length < q.vertices.length) : q.vertices[q.length] = b := by
  have e : q.vertices.length - 1 = q.length := by simp
  have := List.getLast_eq_getElem (l := q.vertices) q.vertices_ne_nil
  rw [Quiver.Path.vertices_getLast] at this
  simp only [e] at this
  exact this.symm

omit [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]
  [DecidablePred (· ∈ Q.nonprojective)] in
theorem not_tauChain_tau {v : V} (hv : v ∈ Q.nonprojective) {n : ℕ}
    (h : ¬ Q.TauChain v (n + 1)) : ¬ Q.TauChain (Q.tau ⟨v, hv⟩).1 n :=
  fun h' ↦ h ⟨hv, h'⟩

/-- **Elimination along rotations**, by induction on the potential. -/
theorem row_mem_imageD_of_potential (m : ℕ) : ∀ N : ℕ, ∀ (x : Q.nonprojective) {y : V}
    (a : y ⟶ x.1) (p : Quiver.Path (Q.tau x).1 y), p.length = m →
    (∃ (i : ℕ) (hi : i < p.vertices.length) (n : ℕ),
      ¬ Q.TauChain p.vertices[i] (n + 1) ∧ (m + 1) * n + (m - i) ≤ N) →
    row c x (p.cons a) ∈ imageD c m := by
  intro N
  induction N with
  | zero =>
      rintro x y a p hp ⟨i, hi, n, hn, hle⟩
      apply row_mem_imageD_of_rotation c x a p hp
      intro hy
      exfalso
      have hlen : p.vertices.length = m + 1 := by simp [hp]
      have h0 : (m + 1) * n = 0 := by omega
      have hn0 : n = 0 := by simpa using h0
      have him : i = m := by omega
      subst hn0 him
      have e : p.vertices[i] = y := by
        have := vertices_getElem_length p (by omega)
        simp only [hp] at this
        exact this
      rw [e] at hn
      exact hn ⟨hy, trivial⟩
  | succ N ih =>
      rintro x y a p hp ⟨i, hi, n, hn, hle⟩
      apply row_mem_imageD_of_rotation c x a p hp
      intro hy
      have hlen : p.vertices.length = m + 1 := by simp [hp]
      obtain ⟨z', p', a', hw⟩ := exists_eq_cons
        ((Q.mate ⟨y, hy⟩ (Q.tau x).1 (Q.mate x y a)).toPath.comp p) (by simp)
      have hp' : p'.length = m := by
        have := congrArg Quiver.Path.length hw
        simp [hp] at this
        omega
      have hv := vertices_rotate _ p p' a' hw
      rw [hw]
      apply ih ⟨y, hy⟩ a' p' hp'
      by_cases him : i < m
      · refine ⟨i + 1, by simp [hp']; omega, n, ?_, ?_⟩
        · have e : p'.vertices[i + 1]'(by simp [hp']; omega) = p.vertices[i] := by
            simp only [hv, List.getElem_cons_succ, List.getElem_dropLast]
          rw [e]; exact hn
        · generalize (m + 1) * n = K at *
          omega
      · have him' : i = m := by omega
        subst him'
        have e : p.vertices[i] = y := by
          have := vertices_getElem_length p (by omega)
          simp only [hp] at this
          exact this
        rw [e] at hn
        obtain _ | n' := n
        · exact absurd ⟨hy, trivial⟩ hn
        refine ⟨0, by simp, n', ?_, ?_⟩
        · have e0 : p'.vertices[0]'(by simp) = (Q.tau ⟨y, hy⟩).1 := by simp [hv]
          rw [e0]
          exact not_tauChain_tau hy hn
        · have : (i + 1) * (n' + 1) = (i + 1) * n' + (i + 1) := by ring
          rw [this] at hle
          generalize (i + 1) * n' = K at *
          omega

/-- **Proposition 5.1, the nonperiodic rows** (`prop:periodic-localization`).
A row of length `m + 1` through a vertex that is not `τ`-periodic lies in the
image of `D_m`. -/
theorem row_mem_imageD_of_not_periodic {m : ℕ} (x : Q.nonprojective)
    (w : Quiver.Path (Q.tau x).1 x.1) (hw : w.length = m + 1) {v : V} (hv : v ∈ w.vertices)
    (hper : ¬ Q.IsTauPeriodic v) : row c x w ∈ imageD c m := by
  obtain ⟨y, p, a, rfl⟩ := exists_eq_cons w (by omega)
  have hp : p.length = m := by simpa using hw
  have hlen : p.vertices.length = m + 1 := by simp [hp]
  obtain ⟨n0, hn0⟩ : ∃ n, ¬ Q.TauChain v n := by
    by_contra h
    push_neg at h
    exact hper h
  rw [Quiver.Path.vertices_cons, List.concat_eq_append, List.mem_append,
    List.mem_singleton] at hv
  rcases hv with hv | rfl
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    exact row_mem_imageD_of_potential c m _ x a p hp
      ⟨i, hi, n0, fun h ↦ hn0 (h.mono (by omega)), le_rfl⟩
  · obtain _ | n1 := n0
    · exact absurd trivial hn0
    refine row_mem_imageD_of_potential c m _ x a p hp ⟨0, by omega, n1, ?_, le_rfl⟩
    have e0 : p.vertices[0]'(by omega) = (Q.tau x).1 := by simp
    rw [e0]
    intro h
    exact not_tauChain_tau x.2 hn0 (h.mono (by omega))

end ScalarMeshCategory

end MultiplicativeBasisDeformations
