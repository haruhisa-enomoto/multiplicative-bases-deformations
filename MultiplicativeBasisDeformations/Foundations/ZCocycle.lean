import MultiplicativeBasisDeformations.Foundations.MorseCollapse

/-!
# Integer cocycles from an acyclic matching

For Proposition 7.6. An integer one-cocycle on a 2-complex (`f_t + g_t = h_t` on every
triangle) is determined by arbitrary values on the unmatched edges of an acyclic matching:
each matched edge is solved from its triangle, by recursion on the potential (`zval`,
`zval_tri`). This is the abelian form of the collapse of Lemma 4.2 ("each matched edge is
expressed through the remaining ones").

`zval_agree`: on a set of edges closed under the matching triangles, a cocycle agreeing
with the prescribed values on the unmatched edges of the set agrees with `zval`.
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations.Morse

variable {V : Type} {Ed : Type} {src tgt : Ed → V} {S : Tris src tgt} (M : Matching S)
  {G : Type*} [AddCommGroup G]

/-- The value of edge `i` of a triangle solved from the values `v` of the other two. -/
def triZ (v : Fin 3 → G) : Fin 3 → G
  | 0 => v 2 - v 1
  | 1 => v 2 - v 0
  | 2 => v 0 + v 1

open Classical in
/-- **The cocycle with prescribed values `f` on the unmatched edges.** -/
def zval (f : Ed → G) : Ed → G :=
  (measure (μ M)).wf.fix fun e rec ↦
    if h : Matched M e then
      triZ (fun j ↦ if hj : j = M.m (Classical.choose h) then 0 else
        rec (S.edge (Classical.choose h) j) (μ_lt_of_other M h j hj)) (M.m (Classical.choose h))
    else f e

open Classical in
theorem zval_eq (f : Ed → G) (e : Ed) :
    zval M f e = if h : Matched M e then
      triZ (fun j ↦ if j = M.m (Classical.choose h) then 0 else
        zval M f (S.edge (Classical.choose h) j)) (M.m (Classical.choose h))
    else f e := by
  rw [zval, WellFounded.fix_eq]
  split_ifs with h
  · congr 1
  · rfl

theorem zval_unmatched (f : Ed → G) {e : Ed} (h : ¬ Matched M e) : zval M f e = f e := by
  rw [zval_eq, dif_neg h]

theorem zval_matched (f : Ed → G) (t : S.T) :
    zval M f (S.edge t (M.m t)) =
      triZ (fun j ↦ if j = M.m t then 0 else zval M f (S.edge t j)) (M.m t) := by
  classical
  have h : Matched M (S.edge t (M.m t)) := ⟨t, rfl⟩
  have hc : Classical.choose h = t := M.inj (Classical.choose_spec h)
  rw [zval_eq, dif_pos h]
  generalize Classical.choose h = t' at hc ⊢
  subst hc
  rfl

theorem triZ_rel (v : Fin 3 → G) (i : Fin 3) (w : Fin 3 → G)
    (hw : w = fun j ↦ if j = i then triZ (fun j ↦ if j = i then 0 else v j) i else v j) :
    w 0 + w 1 = w 2 := by
  subst hw
  fin_cases i <;> simp [triZ]

/-- **The triangle relations hold.** -/
theorem zval_tri (f : Ed → G) (t : S.T) :
    zval M f (S.f t) + zval M f (S.g t) = zval M f (S.h t) := by
  have key : ∀ j, zval M f (S.edge t j) = if j = M.m t then
      triZ (fun j ↦ if j = M.m t then 0 else zval M f (S.edge t j)) (M.m t)
      else zval M f (S.edge t j) := by
    intro j
    split_ifs with hj
    · subst hj; exact zval_matched M f t
    · rfl
  have := triZ_rel (fun j ↦ zval M f (S.edge t j)) (M.m t) (fun j ↦ zval M f (S.edge t j))
    (funext key)
  simpa [Tris.edge] using this

/-- **Agreement on a closed set of edges.** -/
theorem zval_agree (f : Ed → G) (E : Set Ed) (g : Ed → G)
    (hE : ∀ t, S.edge t (M.m t) ∈ E → ∀ j, S.edge t j ∈ E)
    (hg : ∀ t, (∀ j, S.edge t j ∈ E) → g (S.f t) + g (S.g t) = g (S.h t))
    (hf : ∀ e ∈ E, ¬ Matched M e → f e = g e) : ∀ e ∈ E, zval M f e = g e := by
  intro e
  induction e using (measure (μ M)).wf.induction with
  | _ e ih =>
    intro he
    by_cases h : Matched M e
    · obtain ⟨t, rfl⟩ := h
      have hall := hE t he
      have hlt : ∀ j, j ≠ M.m t → μ M (S.edge t j) < μ M (S.edge t (M.m t)) := by
        intro j hj
        have h' : Matched M (S.edge t (M.m t)) := ⟨t, rfl⟩
        have hc : Classical.choose h' = t := M.inj (Classical.choose_spec h')
        have := μ_lt_of_other M h' j (by rw [hc]; exact hj)
        rwa [hc] at this
      rw [zval_matched]
      have hrel := hg t hall
      have hv : ∀ j, j ≠ M.m t → zval M f (S.edge t j) = g (S.edge t j) :=
        fun j hj ↦ ih _ (hlt j hj) (hall j)
      have hrel' : g (S.edge t 0) + g (S.edge t 1) = g (S.edge t 2) := hrel
      generalize hm : M.m t = m at hv ⊢
      fin_cases m <;> simp [triZ] at hv ⊢
      · rw [hv 2 (by decide), hv 1 (by decide), ← hrel']; abel
      · rw [hv 2 (by decide), hv 0 (by decide), ← hrel']; abel
      · rw [hv 0 (by decide), hv 1 (by decide), ← hrel']
    · rw [zval_unmatched M f h]; exact hf e he h

end MultiplicativeBasisDeformations.Morse
