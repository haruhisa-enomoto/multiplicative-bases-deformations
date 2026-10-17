import MultiplicativeBasisDeformations.Foundations.PeriodicDepth

/-!
# Unit mesh coefficients

Lemma 4.4 (`lem:unit-mesh-coefficients`, `scalar-normalization.tex:150–176`):
"Regard its coefficients as a multiplicative cellular two-cochain on `K`,
assigning `c_{X,a}` to the triangle with boundary `(σa) a t_X⁻¹`. […] Rescale the
path arrow `a` by `φ(a)` and divide the whole mesh relation at `X` by `φ(t_X)`.
These operations change its coefficient to `c_{X,a}(dφ)(X,a)` […] There are no
3-cells, and Lemma 4.2 makes `K` homotopy equivalent to a graph. Thus its
cellular `H²(K;k^*)` is zero, so every two-cochain is a coboundary."

Here `H²(K; G) = 0` for an abelian group `G` is proved from the acyclic matching
of Lemma 4.2 (`Morse.exists_cochain`): the matched edge of each triangle is
solved for, in increasing order of the potential. For the mesh complex this
gives the rescaling (`exists_unit_rescaling`).
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace Morse

variable {V : Type} {Ed : Type} {src tgt : Ed → V} {S : Tris src tgt}

/-- The cocycle equation `c_t φ(f) φ(g) = φ(h)` of a triangle. -/
def CochainEq {G : Type*} [CommGroup G] (c : S.T → G) (φ : Ed → G) (t : S.T) : Prop :=
  c t * φ (S.edge t 0) * φ (S.edge t 1) = φ (S.edge t 2)

/-- The value forced on the matched edge of `t` by its equation. -/
def solve {G : Type*} [CommGroup G] (M : Matching S) (c : S.T → G) (φ : Ed → G) (t : S.T) : G :=
  if M.m t = 0 then (c t * φ (S.edge t 1))⁻¹ * φ (S.edge t 2)
  else if M.m t = 1 then (c t * φ (S.edge t 0))⁻¹ * φ (S.edge t 2)
  else c t * φ (S.edge t 0) * φ (S.edge t 1)

/-- **`H²` of a complex with a complete acyclic matching vanishes**: every
two-cochain is a coboundary. -/
theorem exists_cochain {G : Type*} [CommGroup G] (M : Matching S) (hN : ∃ N, ∀ t, M.pot t < N)
    (c : S.T → G) : ∃ φ : Ed → G, ∀ t, CochainEq c φ t := by
  classical
  have key : ∀ N, ∃ φ : Ed → G, ∀ t, M.pot t < N → CochainEq c φ t := by
    intro N
    induction N with
    | zero => exact ⟨fun _ ↦ 1, fun t ht ↦ absurd ht (Nat.not_lt_zero _)⟩
    | succ N ih =>
        obtain ⟨φ, hφ⟩ := ih
        let φ' : Ed → G := fun e ↦
          if h : ∃ t, M.pot t = N ∧ S.edge t (M.m t) = e then solve M c φ (Classical.choose h)
          else φ e
        -- other edges of a triangle of potential `≤ N` are unchanged
        have hother : ∀ t, M.pot t ≤ N → ∀ i, i ≠ M.m t → φ' (S.edge t i) = φ (S.edge t i) := by
          intro t ht i hi
          refine dif_neg ?_
          rintro ⟨t₂, ht₂, he⟩
          have := M.dec t i hi t₂ he
          omega
        have hmatched_lt : ∀ t, M.pot t < N → φ' (S.edge t (M.m t)) = φ (S.edge t (M.m t)) := by
          intro t ht
          refine dif_neg ?_
          rintro ⟨t₂, ht₂, he⟩
          have := M.inj he
          subst this
          omega
        have hmatched_eq : ∀ t, M.pot t = N → φ' (S.edge t (M.m t)) = solve M c φ t := by
          intro t ht
          have h : ∃ t', M.pot t' = N ∧ S.edge t' (M.m t') = S.edge t (M.m t) := ⟨t, ht, rfl⟩
          change (if h : _ then _ else _) = _
          rw [dif_pos h, M.inj (Classical.choose_spec h).2]
        refine ⟨φ', fun t ht ↦ ?_⟩
        have hall : ∀ i, i ≠ M.m t → φ' (S.edge t i) = φ (S.edge t i) := hother t (by omega)
        rcases Nat.lt_or_ge (M.pot t) N with hlt | hge
        · have h0 : ∀ i, φ' (S.edge t i) = φ (S.edge t i) := fun i ↦ by
            by_cases hi : i = M.m t
            · subst hi; exact hmatched_lt t hlt
            · exact hall i hi
          unfold CochainEq
          rw [h0, h0, h0]
          exact hφ t hlt
        · have heq : M.pot t = N := by omega
          have hs := hmatched_eq t heq
          unfold CochainEq
          have hm : M.m t = 0 ∨ M.m t = 1 ∨ M.m t = 2 := by omega
          rcases hm with hm | hm | hm
          · unfold solve at hs
            rw [hm, if_pos rfl] at hs
            rw [hm] at hall
            rw [hs, hall 1 (by decide), hall 2 (by decide), mul_right_comm,
              ← mul_assoc, mul_inv_cancel, one_mul]
          · unfold solve at hs
            rw [hm, if_neg (by decide), if_pos rfl] at hs
            rw [hm] at hall
            rw [hs, hall 0 (by decide), hall 2 (by decide), mul_inv_cancel_left]
          · unfold solve at hs
            rw [hm, if_neg (by decide), if_neg (by decide)] at hs
            rw [hm] at hall
            rw [hs, hall 0 (by decide), hall 1 (by decide)]
  obtain ⟨N, hN⟩ := hN
  obtain ⟨φ, hφ⟩ := key N
  exact ⟨φ, fun t ↦ hφ t (hN t)⟩

end Morse

namespace MeshWalk

open TranslationQuiver

variable {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V}
  [Fintype V] [DecidableEq V] [∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] {k : Type*} [Field k] (c : MeshCoefficients k Q)
  (hfin : ∀ x y : V, FiniteDimensional k
    (ScalarMeshCategory.obj c x ⟶ ScalarMeshCategory.obj c y))

include hfin in
/-- **Lemma 4.4**: every coefficient system `c'` on `Q` becomes `1` after
rescaling each arrow `a` by `φ(a)` and each whole mesh relation at `x` by
`ψ(x)⁻¹`: `c'_{x,a} φ(σa) φ(a) = ψ(x)`. (The acyclic matching of `K` comes from a
reference system `c` with finite-dimensional mesh category, e.g. that of `Γ_A`.) -/
theorem exists_unit_rescaling (c' : MeshCoefficients k Q) :
    ∃ (φ : Arr V → kˣ) (ψ : Q.nonprojective → kˣ), ∀ (x : Q.nonprojective) (y : V)
      (a : y ⟶ x.1), c' x y a * φ ⟨(Q.tau x).1, y, Q.mate x y a⟩ * φ ⟨y, x.1, a⟩ = ψ x := by
  classical
  let M := meshMatching (meshDepth c hfin)
  have hN : ∃ N, ∀ t, M.pot t < N := by
    haveI : Finite (meshTris Q).T := inferInstanceAs (Finite (Tri Q))
    obtain ⟨N, hN⟩ := (Set.finite_range M.pot).bddAbove
    exact ⟨N + 1, fun t ↦ Nat.lt_succ_of_le (hN ⟨t, rfl⟩)⟩
  obtain ⟨φ, hφ⟩ := Morse.exists_cochain M hN (G := kˣ) fun t ↦ c' t.1 t.2.1 t.2.2
  exact ⟨fun A ↦ φ (Sum.inl A), fun x ↦ φ (Sum.inr x), fun x y a ↦ hφ ⟨x, y, a⟩⟩

end MeshWalk

end MultiplicativeBasisDeformations
