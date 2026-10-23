module

public import MultiplicativeBasisDeformations.Foundations.MeshWeights
public import MultiplicativeBasisDeformations.Foundations.BasisExt
public import MultiplicativeBasisDeformations.Foundations.WeightHH

/-!
# Proposition 7.5: the residual characters are part of an integer basis

`weights-and-parameters.tex` (`prop:primitive-parameter-characters`): "In the
weight lattice `L = W(P)`, the residual characters `χ_i` form part of an integer basis."

Here `χ_i = w(p_i) − ν_{v_i}` for a mesh weight `W_u` with values in `W(P)` restricting to
the identity (Lemma 7.4 with `h = id`). Given integer mesh weights `W_j` with
`W_j(p_i) − ν_{v_i} = δ_ij` (`residual_dual`), the integer ray weights `h_j = res W_j`
satisfy `h_j(χ_i) = δ_ij`: the mesh weights `h_j ∘ W_u` and `W_j` have the same restriction,
so by Lemma 7.4 they differ by object values vanishing at the projectives, which do not
change the weight of a row relative to its mesh (`rowWt_eq_of_res`). As `W(P)` is free of
finite rank, the `χ_i` are part of a basis (`exists_basis_of_dual`).

Deviation: the source identifies `χ_i` with the deck class `±θ_{g_i}` and uses a lemma on the
periodic core; we use the dual mesh weights instead.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u

namespace MeshWalk

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

section Ops

variable {V : Type} [Quiver.{0} V] {Q : TranslationQuiver V}

/-- The image of a mesh weight under a homomorphism. -/
def MeshWt.map {M N : Type} [AddCommGroup M] [AddCommGroup N] (h : M →+ N) (W : MeshWt Q M) :
    MeshWt Q N where
  w a := h (W.w a)
  ν x := h (W.ν x)
  mesh x a := by rw [← map_add, W.mesh]

/-- The difference of two mesh weights. -/
def MeshWt.sub {M : Type} [AddCommGroup M] (W W' : MeshWt Q M) : MeshWt Q M where
  w a := W.w a - W'.w a
  ν x := W.ν x - W'.ν x
  mesh x a := by rw [← W.mesh x a, ← W'.mesh x a]; abel

theorem MeshWt.pw_map {M N : Type} [AddCommGroup M] [AddCommGroup N] (h : M →+ N) (W : MeshWt Q M)
    {y x : V} (p : Quiver.Path y x) : (W.map h).pw p = h (W.pw p) := by
  induction p with
  | nil => simp [MeshWt.pw]
  | cons p a ih => rw [MeshWt.pw, MeshWt.pw, ih, map_add]; rfl

theorem MeshWt.pw_sub {M : Type} [AddCommGroup M] (W W' : MeshWt Q M) {y x : V}
    (p : Quiver.Path y x) : (W.sub W').pw p = W.pw p - W'.pw p := by
  induction p with
  | nil => simp [MeshWt.pw]
  | cons p a ih => rw [MeshWt.pw, MeshWt.pw, MeshWt.pw, ih]; change _ + (W.w a - W'.w a) = _; abel

end Ops

variable {k : Type u} [Field k] [IsAlgClosed k] [Infinite k] {V : Type} [Quiver.{0} V]
  [Fintype V] [DecidableEq V] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  {c : MeshCoefficients k Q} {v₀ : V}
  [hone : ∀ x y : V, Subsingleton (x ⟶ y)] [∀ x y : V, Fintype (x ⟶ y)]
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

theorem MeshWt.rv_map {M N : Type} [AddCommGroup M] [AddCommGroup N] (h : M →+ N) (W : MeshWt Q M)
    (t : Piece Q c v₀ D) : (W.map h).rv (c := c) (D := D) t = h (W.rv (c := c) (D := D) t) := by
  by_cases ht : NZ Q c v₀ D t
  · obtain ⟨x, y, g⟩ := t
    obtain ⟨p, hp⟩ := exists_path_of_nz ht
    rw [MeshWt.rv_path _ ht hp, MeshWt.rv_path _ ht hp, MeshWt.pw_map]
  · simp [MeshWt.rv, if_neg ht]

theorem MeshWt.rv_sub {M : Type} [AddCommGroup M] (W W' : MeshWt Q M) (t : Piece Q c v₀ D) :
    (W.sub W').rv (c := c) (D := D) t = W.rv (c := c) (D := D) t - W'.rv (c := c) (D := D) t := by
  by_cases ht : NZ Q c v₀ D t
  · obtain ⟨x, y, g⟩ := t
    obtain ⟨p, hp⟩ := exists_path_of_nz ht
    rw [MeshWt.rv_path _ ht hp, MeshWt.rv_path _ ht hp, MeshWt.rv_path _ ht hp, MeshWt.pw_sub]
  · simp [MeshWt.rv, if_neg ht]

theorem WP_hom_ext {M : Type} [AddCommGroup M] {f g : WP Q c v₀ D →+ M}
    (h : ∀ t, f (cls Q c v₀ D t) = g (cls Q c v₀ D t)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply Finsupp.addHom_ext'
  intro t
  apply AddMonoidHom.ext_int
  exact h t

theorem MeshWt.res_map {M N : Type} [AddCommGroup M] [AddCommGroup N] (h : M →+ N) (W : MeshWt Q M) :
    (W.map h).res (v₀ := v₀) c D = h.comp (W.res c D) :=
  WP_hom_ext fun t ↦ by
    rw [MeshWt.res_cls, AddMonoidHom.comp_apply, MeshWt.res_cls, MeshWt.rv_map]

theorem MeshWt.res_sub {M : Type} [AddCommGroup M] (W W' : MeshWt Q M) :
    (W.sub W').res (v₀ := v₀) c D = W.res c D - W'.res c D :=
  WP_hom_ext fun t ↦ by
    rw [MeshWt.res_cls, AddMonoidHom.sub_apply, MeshWt.res_cls, MeshWt.res_cls, MeshWt.rv_sub]

section Prop76

variable (x₀ : D.PV) (hK : ∀ X : V, ∃ g, aconn Q v₀ (x₀.1, 1) (X, g))
  (hmid : ∀ x : Q.nonprojective, Nonempty (Σ y : V, y ⟶ x.1))

include hK hmid in
/-- **Mesh weights with the same restriction give the same row weights.** -/
theorem rowWt_eq_of_res {M : Type} [AddCommGroup M] (W W' : MeshWt Q M)
    (hres : W.res (v₀ := v₀) c D = W'.res c D) (R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) :
    rowWt W R = rowWt W' R := by
  have h0 : (W.sub W').res (v₀ := v₀) c D = 0 := by rw [MeshWt.res_sub, hres, sub_self]
  obtain ⟨ζ, -, hζw, hζν⟩ := (res_eq_zero_iff (hK := hK) hmid (W.sub W')).1 h0
  have h1 := (W.sub W').pw_of_diff hζw R.2
  rw [MeshWt.pw_sub] at h1
  have h2 := hζν R.1
  change W.ν R.1 - W'.ν R.1 = _ at h2
  unfold rowWt
  rw [← sub_eq_zero]
  rw [show W.pw R.2 - W.ν R.1 - (W'.pw R.2 - W'.ν R.1) =
    (W.pw R.2 - W'.pw R.2) - (W.ν R.1 - W'.ν R.1) by abel, h1, h2, sub_self]

theorem rowWt_map {M N : Type} [AddCommGroup M] [AddCommGroup N] (h : M →+ N) (W : MeshWt Q M)
    (R : Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1) :
    rowWt (W.map h) R = h (rowWt W R) := by
  unfold rowWt
  rw [MeshWt.pw_map, map_sub]; rfl

include hK hmid in
/-- **Proposition 7.5** (`prop:primitive-parameter-characters`): the residual characters
are part of an integer basis of `W(P)`. -/
theorem chars_part_of_basis [Module.Free ℤ (WP Q c v₀ D)] [Module.Finite ℤ (WP Q c v₀ D)]
    (Wu : MeshWt Q (WP Q c v₀ D)) (hWu : Wu.res c D = AddMonoidHom.id _) {n : ℕ}
    (R : Fin n → Σ x : Q.nonprojective, Quiver.Path (Q.tau x).1 x.1)
    (hdual : ∀ i, ∃ W : MeshWt Q ℤ, ∀ j, rowWt W (R j) = if j = i then 1 else 0) :
    ∃ (ι : Type) (b : Module.Basis ι ℤ (WP Q c v₀ D)) (j : Fin n → ι), Function.Injective j ∧
      ∀ i, b (j i) = rowWt Wu (R i) := by
  choose W hW using hdual
  refine exists_basis_of_dual (fun i ↦ rowWt Wu (R i)) (fun i ↦ ((W i).res c D).toIntLinearMap)
    fun i j ↦ ?_
  change (W i).res c D (rowWt Wu (R j)) = _
  rw [← rowWt_map, rowWt_eq_of_res x₀ hK hmid _ (W i) (by rw [MeshWt.res_map, hWu]; rfl), hW i j]
  simp only [eq_comm]

end Prop76

end MeshWalk

end MultiplicativeBasisDeformations
