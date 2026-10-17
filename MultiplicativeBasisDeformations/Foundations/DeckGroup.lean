import MultiplicativeBasisDeformations.Foundations.ZTransport
import MultiplicativeBasisDeformations.Foundations.StarTree

/-!
# Deck transformations of `ℤΔ → Q`

Proof of Proposition 4.1, Steps 3 and 4 (`periodic-mesh-calculations.tex`).

* A map over `π` preserving arrows is determined by its value at one vertex
  ("by unique lifting of undirected walks") — `eq_of_over`.
* A translation-commuting automorphism of `ℤΔ` has the form
  `(v, t) ↦ (ρ v, t + c₀)` in height coordinates: "Every quiver arrow increases
  the height by one ... the difference `H(Fx) - H(x)` is therefore constant along
  arrows and hence constant on the connected quiver. Its action on translation
  orbits is a tree automorphism `ρ`" — `height_form`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Function

namespace MultiplicativeBasisDeformations

universe u v w

namespace OrientedTree

variable {D : Type v} (T : OrientedTree D)

/-- Two vertices of `ℤΔ` joined by an arrow in either direction. -/
def ZAdj (X Y : T.ZVert) : Prop := Nonempty (X ⟶ Y) ∨ Nonempty (Y ⟶ X)

/-- `ℤΔ` is connected. -/
def ZConnected : Prop := ∀ X Y : T.ZVert, Relation.EqvGen T.ZAdj X Y

variable {V : Type u} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)]

/-- **Maps over a covering are determined by one value.** -/
theorem eq_of_over (hW : T.ZConnected) (π : T.ZVert ⥤q V) (hπ : π.IsCovering)
    (F G : T.ZVert → T.ZVert) (hF : ∀ X Y, Nonempty (X ⟶ Y) → Nonempty (F X ⟶ F Y))
    (hG : ∀ X Y, Nonempty (X ⟶ Y) → Nonempty (G X ⟶ G Y))
    (hπF : ∀ X, π.obj (F X) = π.obj X) (hπG : ∀ X, π.obj (G X) = π.obj X)
    {X₀ : T.ZVert} (h₀ : F X₀ = G X₀) (X : T.ZVert) : F X = G X := by
  have step : ∀ X Y, Nonempty (X ⟶ Y) → (F X = G X ↔ F Y = G Y) := by
    intro X Y hXY
    · constructor
      · intro h
        have h1 := hF X Y hXY
        have h2 := hG X Y hXY
        rw [h] at h1
        exact eq_of_star_bijective π (hπ.1 _) h1 h2 ((hπF Y).trans (hπG Y).symm)
      · intro h
        have h1 := hF X Y hXY
        have h2 := hG X Y hXY
        rw [h] at h1
        obtain ⟨a⟩ := h1
        obtain ⟨b⟩ := h2
        have hc := (hπ.2 (G Y)).1
        have : π.costar (G Y) ⟨F X, a⟩ = π.costar (G Y) ⟨G X, b⟩ := by
          simp only [Prefunctor.costar_apply]
          have e : π.obj (F X) = π.obj (G X) := (hπF X).trans (hπG X).symm
          exact Sigma.ext e (Subsingleton.helim (congrArg (· ⟶ π.obj (G Y)) e) _ _)
        exact congrArg Sigma.fst (hc this)
  have key : ∀ X Y, Relation.EqvGen T.ZAdj X Y → (F X = G X ↔ F Y = G Y) := by
    intro X Y h
    induction h with
    | rel X Y h =>
        rcases h with h | h
        · exact step X Y h
        · exact (step Y X h).symm
    | refl => exact Iff.rfl
    | symm X Y _ ih => exact ih.symm
    | trans X Y Z _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key X₀ X (hW X₀ X)).1 h₀

/-- A vertex of `ℤΔ` over `a`, at a height of the right parity. -/
def baseZ (a : D) : T.ZVert := ⟨a, (T.par a).val, by simp⟩

/-- Moving up by `2n` in height. -/
def upZ (X : T.ZVert) (n : ℕ) : T.ZVert := ⟨X.v, X.t + 2 * n, by
  push_cast; rw [X.ht, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]⟩

theorem ztau_upZ (X : T.ZVert) (n : ℕ) : T.ztau (T.upZ X (n + 1)) = T.upZ X n := by
  ext <;> simp [ztau, upZ] <;> ring

theorem eq_upZ_or {X Y : T.ZVert} (h : X.v = Y.v) :
    (∃ n : ℕ, Y = T.upZ X n) ∨ ∃ n : ℕ, X = T.upZ Y n := by
  have hp : ((Y.t - X.t : ℤ) : ZMod 2) = 0 := by push_cast; rw [X.ht, Y.ht, h, sub_self]
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 hp
  rcases le_or_gt 0 m with hm0 | hm0
  · left
    refine ⟨m.toNat, ?_⟩
    ext
    · exact h.symm
    · simp only [upZ]; omega
  · right
    refine ⟨(-m).toNat, ?_⟩
    ext
    · exact h
    · simp only [upZ]; omega

variable (F : T.ZVert ≃ T.ZVert) (hτ : ∀ X, F (T.ztau X) = T.ztau (F X))

include hτ in
theorem v_upZ (X : T.ZVert) (n : ℕ) : (F (T.upZ X n)).v = (F X).v := by
  induction n with
  | zero => congr 1; ext <;> simp [upZ]
  | succ n ih =>
      rw [← ih, ← T.ztau_upZ X n, hτ]
      rfl

include hτ in
theorem v_eq_of_v_eq {X Y : T.ZVert} (h : X.v = Y.v) : (F X).v = (F Y).v := by
  rcases T.eq_upZ_or h with ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact (v_upZ T F hτ X n).symm
  · exact v_upZ T F hτ Y n

/-- A vertex over `b` just above a vertex over an adjacent `a`. -/
def aboveZ (X : T.ZVert) (b : D) (h : T.G.Adj X.v b) : T.ZVert :=
  ⟨b, X.t + 1, by push_cast; rw [X.ht, T.par_adj h]⟩

theorem nonempty_hom_aboveZ (X : T.ZVert) (b : D) (h : T.G.Adj X.v b) :
    Nonempty (X ⟶ T.aboveZ X b h) := ⟨⟨h, rfl⟩⟩

include hτ in
/-- **Step 4: height coordinates of a translation-commuting automorphism**
(`periodic-mesh-calculations.tex`). -/
theorem height_form [Nonempty D] (hW : T.ZConnected)
    (hF : ∀ X Y, Nonempty (X ⟶ Y) ↔ Nonempty (F X ⟶ F Y)) :
    ∃ (c₀ : ℤ) (ρ : D ≃ D), (∀ a b, T.G.Adj a b ↔ T.G.Adj (ρ a) (ρ b)) ∧
      ∀ X, (F X).v = ρ X.v ∧ (F X).t = X.t + c₀ := by
  -- the height shift is constant
  have hstep : ∀ X Y, T.ZAdj X Y → (F X).t - X.t = (F Y).t - Y.t := by
    intro X Y h
    rcases h with h | h
    · obtain ⟨a⟩ := h
      obtain ⟨b⟩ := (hF X Y).1 ⟨a⟩
      have := a.down.2; have := b.down.2; omega
    · obtain ⟨a⟩ := h
      obtain ⟨b⟩ := (hF Y X).1 ⟨a⟩
      have := a.down.2; have := b.down.2; omega
  have hconst : ∀ X Y, (F X).t - X.t = (F Y).t - Y.t := by
    intro X Y
    induction hW X Y with
    | rel X Y h => exact hstep X Y h
    | refl => rfl
    | symm X Y _ ih => exact ih.symm
    | trans X Y Z _ _ ih1 ih2 => exact ih1.trans ih2
  obtain ⟨a₀⟩ := ‹Nonempty D›
  -- the inverse also commutes with translation
  have hτ' : ∀ X, F.symm (T.ztau X) = T.ztau (F.symm X) := by
    intro X
    apply F.injective
    rw [Equiv.apply_symm_apply, hτ, Equiv.apply_symm_apply]
  let ρf : D → D := fun a ↦ (F (T.baseZ a)).v
  let ρg : D → D := fun a ↦ (F.symm (T.baseZ a)).v
  have hρf : ∀ X, (F X).v = ρf X.v := fun X ↦ v_eq_of_v_eq T F hτ (by rfl)
  have hρg : ∀ X, (F.symm X).v = ρg X.v := fun X ↦ v_eq_of_v_eq T F.symm hτ' (by rfl)
  let ρ : D ≃ D :=
    { toFun := ρf
      invFun := ρg
      left_inv := fun a ↦ by
        have := hρg (F (T.baseZ a))
        rw [Equiv.symm_apply_apply] at this
        exact this.symm
      right_inv := fun a ↦ by
        have := hρf (F.symm (T.baseZ a))
        rw [Equiv.apply_symm_apply] at this
        exact this.symm }
  refine ⟨(F (T.baseZ a₀)).t - (T.baseZ a₀).t, ρ, fun a b ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩,
    fun X ↦ ⟨hρf X, by have := hconst X (T.baseZ a₀); omega⟩⟩
  · obtain ⟨c⟩ := (hF _ _).1 (T.nonempty_hom_aboveZ (T.baseZ a) b h)
    have := c.down.1
    rwa [hρf, hρf] at this
  · have h' : T.G.Adj (T.baseZ (ρ a)).v (ρ b) := h
    obtain ⟨c⟩ := (hF (F.symm (T.baseZ (ρ a))) (F.symm (T.aboveZ (T.baseZ (ρ a)) (ρ b) h'))).2 (by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact T.nonempty_hom_aboveZ (T.baseZ (ρ a)) (ρ b) h')
    have := c.down.1
    rw [hρg, hρg] at this
    change T.G.Adj (ρg (ρf a)) (ρg (ρf b)) at this
    have e1 : ρg (ρf a) = a := ρ.left_inv a
    have e2 : ρg (ρf b) = b := ρ.left_inv b
    rwa [e1, e2] at this

end OrientedTree

end MultiplicativeBasisDeformations
