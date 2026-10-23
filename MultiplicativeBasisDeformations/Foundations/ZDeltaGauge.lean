module

public import MultiplicativeBasisDeformations.Foundations.MeshGauge
public import MultiplicativeBasisDeformations.Foundations.TreeRepetition

/-!
# Rescaling the meshes of `ℤΔ` to the signed coefficients

Proof of Proposition 4.1, Step 2 (`periodic-mesh-calculations.tex`):
"We first rescale the meshes on `ℤΔ` to the coefficients `±1` ... On a tree
edge `u → v`, write the repetition arrows as `a_j : u_j → v_j` and
`b_j : v_j → u_{j+1}`. The two coefficients at its endpoints prescribe nonzero
products ... Their ratio determines `μ_{a,j}` recursively in both directions
from `μ_{a,0}`, and then determines every `μ_b`. There is no periodic equation
on the integer line, and different tree edges have disjoint arrow variables."

In height coordinates the arrows over an edge `{x, y}` form a line indexed by
the height `h` of their source, and the mesh at height `h + 2` prescribes the
product of the scalars of the arrows of heights `h` and `h + 1`
(`exists_line_solution`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

variable {k : Type u} [CommRing k]

/-- **No periodic equation on the integer line**: any prescribed products of
consecutive terms are realized. -/
theorem exists_line_solution (r : ℤ → kˣ) : ∃ m : ℤ → kˣ, ∀ s, m s * m (s + 1) = r s := by
  let mpos : ℕ → kˣ := fun n ↦ Nat.rec 1 (fun n mn ↦ r n * mn⁻¹) n
  let mneg : ℕ → kˣ := fun n ↦ Nat.rec 1 (fun n mn ↦ r (-(n + 1 : ℕ)) * mn⁻¹) n
  refine ⟨fun s ↦ if 0 ≤ s then mpos s.toNat else mneg (-s).toNat, fun s ↦ ?_⟩
  beta_reduce
  rcases lt_trichotomy s (-1) with hs | hs | hs
  · -- both negative
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = -((n : ℤ) + 1 + 1) := ⟨(-s - 2).toNat, by omega⟩
    rw [if_neg (by omega), if_neg (by omega)]
    have e1 : (-(-((n : ℤ) + 1 + 1))).toNat = n + 1 + 1 := by omega
    have e2 : (-(-((n : ℤ) + 1 + 1) + 1)).toNat = n + 1 := by omega
    rw [e1, e2]
    change r (-((n + 1 : ℕ) + 1 : ℕ)) * (mneg (n + 1))⁻¹ * mneg (n + 1) = _
    rw [inv_mul_cancel_right]
    congr 1
  · subst hs
    rw [if_neg (by omega), if_pos (by omega)]
    change r (-((0 : ℕ) + 1 : ℕ)) * (1 : kˣ)⁻¹ * 1 = r (-1)
    simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n := ⟨s.toNat, by omega⟩
    rw [if_pos (by omega), if_pos (by omega)]
    have e1 : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [Int.toNat_natCast, e1]
    change mpos n * (r n * (mpos n)⁻¹) = r n
    rw [mul_comm, inv_mul_cancel_right]

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D)

theorem par_ne_of_adj {x y : D} (h : T.G.Adj x y) : T.par y ≠ T.par x := by
  rw [T.par_adj h]
  intro h'
  have : (1 : ZMod 2) = 0 := by
    have := congrArg (· - T.par x) h'
    simpa using this
  exact absurd this (by decide)

theorem zmod2_eq_or : ∀ a b : ZMod 2, a = b ∨ a = b + 1 := by decide

theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

open Classical in
/-- The ratio prescribed by the mesh at height `s + 2` on the edge `{x, y}`. -/
def edgeRatio [DecidableRel T.orient] (c : MeshCoefficients k T.zQuiver) (x y : D) (s : ℤ) : kˣ :=
  if hadj : T.G.Adj x y then
    if hs : (s : ZMod 2) = T.par x then
      T.sgn k x y * (c ⟨⟨x, s + 2, by push_cast; rw [hs, zmod2_two, add_zero]⟩, trivial⟩
        ⟨y, s + 1, by push_cast; rw [hs, T.par_adj hadj]⟩ ⟨⟨hadj.symm, show s + 2 = s + 1 + 1 by omega⟩⟩)⁻¹
    else
      have hs' : (s : ZMod 2) = T.par y := by
        rcases zmod2_eq_or (s : ZMod 2) (T.par x) with h | h
        · exact absurd h hs
        · rw [h, T.par_adj hadj]
      T.sgn k y x * (c ⟨⟨y, s + 2, by push_cast; rw [hs', zmod2_two, add_zero]⟩, trivial⟩
        ⟨x, s + 1, by
          push_cast; rw [hs']
          have := T.par_adj hadj
          rw [this, add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]⟩
        ⟨⟨hadj, show s + 2 = s + 1 + 1 by omega⟩⟩)⁻¹
  else 1

/-- **The meshes of `ℤΔ` can be rescaled to the signed preprojective
coefficients**, by rescaling arrows alone. -/
theorem exists_gauge [DecidableRel T.orient] (c : MeshCoefficients k T.zQuiver) :
    ∃ μ : ∀ {X Y : T.ZVert}, (X ⟶ Y) → kˣ, ∀ (X : T.zQuiver.nonprojective) (Y : T.ZVert)
      (a : Y ⟶ X.1), T.zSigned k X Y a = 1 * c X Y a * μ (T.zQuiver.mate X Y a) * μ a := by
  classical
  choose m hm using fun p : D × D ↦ exists_line_solution (T.edgeRatio c p.1 p.2)
  let M : D → D → ℤ → kˣ := fun w w' h ↦ if T.par w = 0 then m (w, w') h else m (w', w) h
  refine ⟨fun {X Y} _ ↦ M X.v Y.v X.t, fun X Y a ↦ ?_⟩
  obtain ⟨⟨x, t, ht⟩, hX⟩ := X
  obtain ⟨y, ty, hty⟩ := Y
  obtain ⟨hadj, hY⟩ := a.down
  change T.G.Adj y x at hadj
  change t = ty + 1 at hY
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by ring⟩
  obtain rfl : ty = s + 1 := by omega
  have hsx : (s : ZMod 2) = T.par x := by
    have := ht; push_cast at this; rwa [zmod2_two, add_zero] at this
  change T.sgn k x y = 1 * c _ _ a * M x y (s + 2 - 2) * M y x (s + 1)
  rw [show s + 2 - 2 = s by ring]
  have hpar := T.par_ne_of_adj hadj
  by_cases hx0 : T.par x = 0
  · have hy0 : ¬ T.par y = 0 := fun h ↦ hpar (hx0.trans h.symm)
    simp only [M, if_pos hx0, if_neg hy0]
    rw [mul_assoc, hm (x, y) s]
    simp only [edgeRatio, dif_pos hadj.symm, dif_pos hsx]
    rw [one_mul, mul_left_comm]
    exact (by simp : ∀ u : kˣ, T.sgn k x y = T.sgn k x y * (u * u⁻¹)) _
  · have hy0 : T.par y = 0 := by
      rcases zmod2_eq_or (T.par y) 0 with h | h
      · exact h
      · exfalso
        rcases zmod2_eq_or (T.par x) 0 with h' | h'
        · exact hx0 h'
        · exact hpar (h'.trans h.symm)
    have hsy : ¬ (s : ZMod 2) = T.par y := fun h ↦ hpar (hsx.symm.trans h)
    simp only [M, if_neg hx0, if_pos hy0]
    rw [mul_assoc, hm (y, x) s]
    simp only [edgeRatio, dif_pos hadj, dif_neg hsy]
    rw [one_mul, mul_left_comm]
    exact (by simp : ∀ u : kˣ, T.sgn k x y = T.sgn k x y * (u * u⁻¹)) _

end OrientedTree

end MultiplicativeBasisDeformations
