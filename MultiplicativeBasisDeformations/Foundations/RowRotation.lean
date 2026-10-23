module

public import MultiplicativeBasisDeformations.Foundations.PeriodicLocalization
public import MultiplicativeBasisDeformations.Foundations.StableTranslation

/-!
# Rotation of rows with signed coefficients

Proof of Lemma A.2 (`lem:twisted-trace-surjection`,
`periodic-mesh-calculations.tex`): "In the signed meshes an arrow
correction identifies a row path `wa` with `(τa)w`, with coefficient one. Indeed,
the correction column gives `c[wa] + c'[(τa)w] = 0`, where `c, c'` are the two
mesh coefficients of the corresponding tree edge, and these are opposite."

Here the cokernel of `D_m` is the quotient `MeshFamily c ⧸ imageD c m`, and the
coefficients are *opposite on mates*: `c_{y, σ a} = - c_{x, a}` for `a : y → x`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

namespace ScalarMeshCategory

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q) [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]
  [DecidablePred (· ∈ Q.nonprojective)]

/-- The cokernel of `D_m`. -/
abbrev Coker (m : ℕ) := MeshFamily c ⧸ imageD c m

/-- The class of a row in the cokernel. -/
def rowClass (m : ℕ) (x : Q.nonprojective) (w : Quiver.Path (Q.tau x).1 x.1) : Coker c m :=
  Submodule.Quotient.mk (row c x w)

/-- Coefficients opposite on mates. -/
def OppositeOnMates (hQ : Q.IsStable) : Prop :=
  ∀ (x : Q.nonprojective) (y : V) (a : y ⟶ x.1),
    c ⟨y, hQ.mem_nonprojective y⟩ (Q.tau x).1 (Q.mate x y a) = -c x y a

/-- **Rotation**: with coefficients opposite on mates, a row `(x, q a)` has the
class of its rotation `(y, (σσ a) q)`. -/
theorem rowClass_rotate (hQ : Q.IsStable) (hc : OppositeOnMates c hQ) {m : ℕ}
    (x : Q.nonprojective) {y : V} (a : y ⟶ x.1) (q : Quiver.Path (Q.tau x).1 y)
    (hq : q.length = m) :
    rowClass c m x (q.cons a) =
      rowClass c m ⟨y, hQ.mem_nonprojective y⟩
        ((Q.mate ⟨y, hQ.mem_nonprojective y⟩ (Q.tau x).1 (Q.mate x y a)).toPath.comp q) := by
  have hcol : meshDerivative c (Pi.single (⟨(Q.tau x).1, y, Q.mate x y a⟩ : Σ u v : V, u ⟶ v)
      (pathMor c q)) ∈ imageD c m :=
    ⟨_, single_mem_familiesDeg c _ q hq, rfl⟩
  rw [column_eq, dif_pos (hQ.mem_nonprojective y), hc] at hcol
  unfold rowClass
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  have h := Submodule.smul_mem _ (((c x y a)⁻¹ : kˣ) : k) hcol
  rw [smul_add, smul_smul, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul,
    Units.val_neg, mul_neg, ← Units.val_mul, inv_mul_cancel, Units.val_one, neg_one_smul,
    ← sub_eq_add_neg] at h
  exact h

variable (hQ : Q.IsStable)

/-- The class of an arbitrary path in the cokernel: the row class of `w` if it
runs from `τ y` to `y`, and zero otherwise. Its endpoints are free, so it is
insensitive to casts. -/
def rowQ (m : ℕ) {u y : V} (w : Quiver.Path u y) : Coker c m :=
  if h : u = hQ.tauE y then rowClass c m ⟨y, hQ.mem_nonprojective y⟩ (w.cast h rfl) else 0

theorem rowQ_cast (m : ℕ) {u y u' y' : V} (hu : u = u') (hy : y = y') (w : Quiver.Path u y) :
    rowQ c hQ m (w.cast hu hy) = rowQ c hQ m w := by
  subst hu hy; rfl

theorem rowQ_eq (m : ℕ) {y : V} (w : Quiver.Path (hQ.tauE y) y) :
    rowQ c hQ m w = rowClass c m ⟨y, hQ.mem_nonprojective y⟩ w := by
  rw [rowQ, dif_pos rfl]; rfl

/-- **Rotation of rows**, with free endpoints: for `a : y → x` and
`b : τ y → τ x`, the row `b q` at `y` and the row `q a` at `x` have the same
class (coefficients opposite on mates). -/
theorem rowQ_rotate [∀ x y : V, Subsingleton (x ⟶ y)] (hc : OppositeOnMates c hQ) {m : ℕ} {x y : V} (a : y ⟶ x)
    (b : hQ.tauE y ⟶ hQ.tauE x) (q : Quiver.Path (hQ.tauE x) y) (hq : q.length = m) :
    rowQ c hQ m (b.toPath.comp q) = rowQ c hQ m (q.cons a) := by
  rw [rowQ_eq, rowQ_eq, rowClass_rotate c hQ hc ⟨x, hQ.mem_nonprojective x⟩ a q hq]
  rw [Subsingleton.elim b]

/-- The row class of a path as a linear function of its image in `C(Q, c)`. -/
theorem rowQ_eq_mk (m : ℕ) {y : V} (w : Quiver.Path (hQ.tauE y) y) :
    rowQ c hQ m w = Submodule.Quotient.mk
      (Pi.single (⟨y, hQ.mem_nonprojective y⟩ : Q.nonprojective) (pathMor c w)) := by
  rw [rowQ_eq]; rfl

end ScalarMeshCategory

end MultiplicativeBasisDeformations
