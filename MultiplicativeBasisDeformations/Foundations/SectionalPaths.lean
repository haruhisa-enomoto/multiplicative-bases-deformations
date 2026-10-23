module

public import MultiplicativeBasisDeformations.Foundations.MeshGrading
public import MultiplicativeBasisDeformations.Foundations.HomIdeal

/-!
# Sectional paths

Proof of Proposition 4.1, Step 1 (`periodic-mesh-calculations.tex`):
"A path is sectional if it contains no consecutive pair `(σa)a`. A sectional
path cannot occur as a monomial term in a contextual mesh relation. Its
coefficient therefore defines a linear functional annihilating the mesh ideal,
and the path is nonzero in the mesh category. Since the mesh category is
finite-dimensional, there is an integer `N` such that all paths of length at
least `N` vanish. Hence every sectional path has length less than `N`."

A path is recorded by its list of arrows (`arrowList`), and it is sectional when
no two consecutive arrows form a mesh pair `(σ a, a)`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u v w

namespace Quiver.Path

variable {V : Type v} [Quiver.{w} V]

/-- The arrows of a path, in order. -/
def arrowList {x : V} : ∀ {y : V}, Quiver.Path x y → List (Σ u v : V, u ⟶ v)
  | _, Quiver.Path.nil => []
  | _, Quiver.Path.cons p a => arrowList p ++ [⟨_, _, a⟩]

@[simp] theorem arrowList_nil (x : V) : arrowList (Quiver.Path.nil : Quiver.Path x x) = [] := rfl

@[simp] theorem arrowList_cons {x y z : V} (p : Quiver.Path x y) (a : y ⟶ z) :
    arrowList (p.cons a) = arrowList p ++ [⟨_, _, a⟩] := rfl

@[simp] theorem arrowList_comp {x y z : V} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    arrowList (p.comp q) = arrowList p ++ arrowList q := by
  induction q with
  | nil => simp
  | cons q a ih => simp [Quiver.Path.comp_cons, ih]

@[simp] theorem arrowList_toPath {x y : V} (a : x ⟶ y) :
    arrowList a.toPath = [⟨x, y, a⟩] := rfl

end Quiver.Path

namespace MultiplicativeBasisDeformations

variable {V : Type v} [Quiver.{w} V]

namespace TranslationQuiver

variable (Q : TranslationQuiver V)

/-- Two consecutive arrows `b, a` form a mesh pair if `b = σ a`. -/
def IsMeshPair (b a : Σ u v : V, u ⟶ v) : Prop :=
  ∃ (x : Q.nonprojective) (y : V) (a' : y ⟶ x.1),
    a = ⟨y, x.1, a'⟩ ∧ b = ⟨(Q.tau x).1, y, Q.mate x y a'⟩

/-- A path is sectional if no two consecutive arrows form a mesh pair. -/
def IsSectional {x y : V} (p : Quiver.Path x y) : Prop :=
  p.arrowList.IsChain fun b a ↦ ¬ Q.IsMeshPair b a

end TranslationQuiver

namespace ScalarMeshCategory

open TranslationQuiver CategoricalIdeal

variable {k : Type u} [Field k] {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q)

theorem not_isSectional_of_mesh {s t : V} (x : Q.nonprojective) {y : V} (a : y ⟶ x.1)
    (q : Quiver.Path s (Q.tau x).1) (q' : Quiver.Path x.1 t) :
    ¬ Q.IsSectional ((q.comp ((Q.mate x y a).toPath.comp a.toPath)).comp q') := by
  intro h
  unfold IsSectional at h
  simp only [Quiver.Path.arrowList_comp, Quiver.Path.arrowList_toPath] at h
  have hinf : [(⟨(Q.tau x).1, y, Q.mate x y a⟩ : Σ u v : V, u ⟶ v), ⟨y, x.1, a⟩] <:+:
      q.arrowList ++ ([⟨(Q.tau x).1, y, Q.mate x y a⟩] ++ [⟨y, x.1, a⟩]) ++ q'.arrowList :=
    ⟨q.arrowList, q'.arrowList, by simp⟩
  have := List.isChain_pair.1 (h.infix hinf)
  exact this ⟨x, y, a, rfl, rfl⟩

/-- **A sectional path does not occur in the mesh ideal**: its coefficient
vanishes on the whole ideal. -/
theorem coeff_eq_zero_of_mem_ideal {x y : V} (p : Quiver.Path x y) (hp : Q.IsSectional p)
    {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hf : f ∈ HomIdeal.generatedHomSubmodule k (meshRelations c) _ _) :
    LinearPaths.toFinsupp f p = 0 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨A, B, r, hr, u, w', rfl⟩ := hg
      obtain ⟨A', rfl⟩ : ∃ A' : V, LinearPaths.obj (k := k) A' = A := ⟨A, rfl⟩
      obtain ⟨B', rfl⟩ : ∃ B' : V, LinearPaths.obj (k := k) B' = B := ⟨B, rfl⟩
      obtain ⟨z, hX, hY, rfl⟩ := hr
      change A' = (Q.tau z).1 at hX
      change B' = z.1 at hY
      subst hX hY
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      induction u using LinearPaths.induction_on with
      | h0 => simp
      | hadd u₁ u₂ h₁ h₂ =>
          rw [Preadditive.add_comp, LinearPaths.toFinsupp_add, Finsupp.add_apply, h₁, h₂,
            add_zero]
      | hsingle q t =>
          induction w' using LinearPaths.induction_on with
          | h0 => simp
          | hadd w₁ w₂ h₁ h₂ =>
              rw [Preadditive.comp_add, Preadditive.comp_add, LinearPaths.toFinsupp_add,
                Finsupp.add_apply, h₁, h₂, add_zero]
          | hsingle q' t' =>
              rw [Linear.smul_comp, Linear.comp_smul, Linear.comp_smul,
                LinearPaths.toFinsupp_smul, LinearPaths.toFinsupp_smul, Finsupp.smul_apply,
                Finsupp.smul_apply]
              simp only [meshRelation, Preadditive.sum_comp, Preadditive.comp_sum,
                Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path]
              rw [show ∀ g : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y,
                LinearPaths.toFinsupp g = (LinearPaths.finsuppEquiv x y) g from fun _ ↦ rfl,
                map_sum]
              simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
                Finsupp.smul_apply]
              rw [Finset.sum_eq_zero]
              · simp
              intro a _
              change _ • (Finsupp.single _ 1 : Quiver.Path x y →₀ k) p = 0
              classical
              rw [Finsupp.single_apply, if_neg]
              · simp
              intro h
              apply not_isSectional_of_mesh z a.2 q q'
              rw [Quiver.Path.comp_assoc, h]
              exact hp
  | zero => simp
  | add f g _ _ hf hg => rw [LinearPaths.toFinsupp_add, Finsupp.add_apply, hf, hg, add_zero]
  | smul t f _ hf => rw [LinearPaths.toFinsupp_smul, Finsupp.smul_apply, hf, smul_zero]

/-- A sectional path is nonzero in the mesh category. -/
theorem pathMor_ne_zero_of_isSectional {x y : V} (p : Quiver.Path x y) (hp : Q.IsSectional p) :
    pathMor c p ≠ 0 := by
  classical
  intro h
  rw [pathMor, RelationCategory.functor_map_eq_zero_iff] at h
  have := coeff_eq_zero_of_mem_ideal c p hp h
  rw [LinearPaths.toFinsupp_path, Finsupp.single_eq_same] at this
  exact one_ne_zero this

/-- **Sectional paths are short** in a finite-dimensional scalar mesh category. -/
theorem exists_length_lt_of_isSectional [Finite V]
    (hfin : ∀ x y : V, FiniteDimensional k (obj c x ⟶ obj c y)) :
    ∃ N : ℕ, ∀ (x y : V) (p : Quiver.Path x y), Q.IsSectional p → p.length < N := by
  obtain ⟨N, hN⟩ := exists_pathMor_eq_zero c hfin
  refine ⟨N, fun x y p hp ↦ ?_⟩
  by_contra h
  exact pathMor_ne_zero_of_isSectional c p hp (hN x y p (by omega))

end ScalarMeshCategory

end MultiplicativeBasisDeformations
