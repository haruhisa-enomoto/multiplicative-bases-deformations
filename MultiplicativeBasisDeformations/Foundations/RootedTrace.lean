module

public import MultiplicativeBasisDeformations.Foundations.RootedGauge
public import MultiplicativeBasisDeformations.Foundations.ResidualSpaces

/-!
# Lemma A.2 for an arbitrary tree

`lem:twisted-trace-surjection` (`periodic-mesh-calculations.tex`): "Let
`Q = Q(Δ, s, ρ) = ℤΔ/⟨τ^s ρ⟩` be a rooted periodic model with signed mesh coefficients, and put
`Π = Π(Δ)`. (1) The cokernel class of a correction in a row of degree `d ≥ 3` is zero unless `d` is
even and `s ∣ (d/2 − 1)`. (2) In an allowed degree, put `l = (1 − d/2)/s` and `θ = ρ^l`. There is a
surjection `T_θ(Π)_d → coker D_{d−1}`."

Here `Δ` is any finite tree (`OrientedTree`), and the covering `π : ℤΔ → Q` has fibres the orbits of
the deck generator `g (v, t) = (ρ v, t + c₀)` in height coordinates (so `c₀ = 2s`). (1) is
`row_lift`: a row of length `m + 1` lifts to a path from `τ X` to `g^n X` with `n c₀ = m − 1`.
(2) is `twistedTraceSurjection`: the twisted trace space `T_σ(Π)_{m+1}` is the quotient of
`⊕_x kΔ̄(x, σ x)` by the ideal of `Π(Δ)`, the rotations `uv − v σ(u)` and the other degrees
(`TwTrace`); lifting paths gives a linear map onto the degree-`(m+1)` cokernel of `D_m`
(`twMap`). The star case is `StarTrace.rowClass_mem_span` with `DegreeDeck.row_lift`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace OrientedTree

open ScalarMeshCategory

variable {D : Type*} (T : OrientedTree D)
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : T.ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]

/-! ### (1) The degree of a row -/

omit [Field k] in
theorem length_cast' {W : Type*} [Quiver W] {a b a' b' : W} (p : Quiver.Path a b) (ha : a = a')
    (hb : b = b') : (p.cast ha hb).length = p.length := by
  subst ha hb; rfl

section Degree

variable (ρ : D ≃ D) (hρ : ∀ a b, T.G.Adj (ρ a) (ρ b) ↔ T.G.Adj a b) (c0 : ℕ)
  (hρp : ∀ v, T.par (ρ v) = T.par v + ((c0 : ℤ) : ZMod 2))

include hρ in
theorem adj_pow (n : ℕ) : ∀ a b, T.G.Adj ((ρ ^ n) a) ((ρ ^ n) b) ↔ T.G.Adj a b := by
  induction n with
  | zero => intro a b; rfl
  | succ n ih => intro a b; rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hρ, ih]

include hρp in
theorem par_pow (n : ℕ) (v : D) :
    T.par ((ρ ^ n) v) = T.par v + (((n * c0 : ℕ) : ℤ) : ZMod 2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hρp, ih]; push_cast; ring

/-- The deck generator on vertices. -/
abbrev gV : T.ZVert → T.ZVert := (T.zAct ρ hρ (c0 : ℤ) hρp).obj

/-- The deck transformation `g^n` in height form. -/
abbrev gPow (n : ℕ) : T.ZVert ⥤q T.ZVert :=
  T.zAct (ρ ^ n) (T.adj_pow ρ hρ n) ((n * c0 : ℕ) : ℤ) (T.par_pow ρ c0 hρp n)

theorem gV_iter (n : ℕ) (X : T.ZVert) :
    ((T.gV ρ hρ c0 hρp)^[n] X).v = (ρ ^ n) X.v ∧ ((T.gV ρ hρ c0 hρp)^[n] X).t = X.t + n * c0 := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      obtain ⟨h1, h2⟩ := ih X
      refine ⟨?_, ?_⟩
      · change ρ ((T.gV ρ hρ c0 hρp)^[n] X).v = ρ ((ρ ^ n) X.v); rw [h1]
      · change ((T.gV ρ hρ c0 hρp)^[n] X).t + c0 = _; rw [h2]; push_cast; ring

theorem gPow_obj (n : ℕ) (Z : T.ZVert) :
    (T.gPow ρ hρ c0 hρp n).obj Z = (T.gV ρ hρ c0 hρp)^[n] Z := by
  apply ZVert.ext
  · exact (T.gV_iter ρ hρ c0 hρp n Z).1.symm
  · rw [(T.gV_iter ρ hρ c0 hρp n Z).2]; change Z.t + ((n * c0 : ℕ) : ℤ) = _; push_cast; ring

variable (hdeck : ∀ Z, π.obj ((T.zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)

include hdeck in
theorem gPow_deck (n : ℕ) (Z : T.ZVert) : π.obj ((T.gPow ρ hρ c0 hρp n).obj Z) = π.obj Z := by
  rw [gPow_obj]
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hdeck, ih]

variable (hfib : ∀ X Y : T.ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (T.gV ρ hρ c0 hρp)^[n] X ∨ X = (T.gV ρ hρ c0 hρp)^[n] Y)

include hfib in
theorem gPow_fib (hc0 : 0 < c0) (n : ℕ) (X E : T.ZVert) (h1 : π.obj E = π.obj X)
    (h2 : E.t = X.t + ((n * c0 : ℕ) : ℤ)) : E = (T.gPow ρ hρ c0 hρp n).obj X := by
  rw [gPow_obj]
  have hgt : ∀ (n : ℕ) (Z : T.ZVert), ((T.gV ρ hρ c0 hρp)^[n] Z).t = Z.t + n * c0 :=
    fun n Z ↦ (T.gV_iter ρ hρ c0 hρp n Z).2
  obtain ⟨n', hn' | hn'⟩ := hfib X E h1.symm
  · have := hgt n' X
    rw [← hn', h2] at this
    have : n' = n := by
      have h3 : (n' : ℤ) * c0 = n * c0 := by push_cast at this; omega
      exact_mod_cast mul_right_cancel₀ (by positivity) h3
    subst this; exact hn'
  · have := hgt n' E
    rw [← hn', h2] at this
    push_cast at this
    have hn0 : n = 0 := by
      by_contra hne; have : (0 : ℤ) < n * c0 := by positivity
      have : (0 : ℤ) ≤ n' * c0 := by positivity
      omega
    have hn'0 : n' = 0 := by
      by_contra hne; have : (0 : ℤ) < n' * c0 := by positivity
      have : (0 : ℤ) ≤ n * c0 := by positivity
      omega
    subst hn0 hn'0
    exact hn'.symm

variable [Fintype D] [DecidableEq D] (hπ : π.IsCovering)
  (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y)) (hsurj : ∀ x : V, ∃ X, π.obj X = x)

include hπ hτ hsurj hfib in
/-- **Lemma A.2(1)**: a row of length `m + 1 ≥ 2` lifts to a path from `τ X` to `g^n X` with
`n c₀ = m − 1`; in particular rows, hence nonzero cokernel classes, occur only in these
degrees. -/
theorem row_lift (hc0 : 0 < c0) {m : ℕ} (hm : 1 ≤ m) (x : Q.nonprojective) (p : Quiver.Path (Q.tau x).1 x.1)
    (hp : p.length = m + 1) :
    ∃ (n : ℕ) (X : T.ZVert) (P : Quiver.Path (T.ztau X) ((T.gPow ρ hρ c0 hρp n).obj X)),
      ((n * c0 : ℕ) : ℤ) = m - 1 ∧ P.length = m + 1 ∧
      rowClass c m x p = T.rowZ hQ π c m P := by
  obtain ⟨X, hX⟩ := hsurj x.1
  have e1 : π.obj (T.ztau X) = (Q.tau x).1 := by rw [hτ, hX]; rfl
  obtain ⟨E, hE, P, hP⟩ := RelSystem.exists_lift π hπ (T.ztau X) (p.cast e1.symm rfl)
  have hPlen : P.length = m + 1 := by
    rw [← LinearPaths.length_mapPath π P, hP, length_cast', length_cast', hp]
  have hEt : E.t = X.t + (m - 1 : ℤ) := by
    have := T.t_path P
    rw [hPlen] at this; simp only [ztau] at this; push_cast at this; omega
  have hgt : ∀ (n : ℕ) (Z : T.ZVert), ((T.gV ρ hρ c0 hρp)^[n] Z).t = Z.t + n * c0 :=
    fun n Z ↦ (T.gV_iter ρ hρ c0 hρp n Z).2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((n * c0 : ℕ) : ℤ) = m - 1 := by
    obtain ⟨n, hn | hn⟩ := hfib X E (hE.trans hX.symm).symm
    · exact ⟨n, by have := hgt n X; rw [← hn] at this; push_cast; omega⟩
    · have h1 := hgt n E; rw [← hn] at h1
      have h2 : (0 : ℤ) ≤ n * c0 := by positivity
      exact ⟨0, by push_cast; omega⟩
  have hEX : E = (T.gPow ρ hρ c0 hρp n).obj X :=
    T.gPow_fib π ρ hρ c0 hρp hfib hc0 n X E (hE.trans hX.symm) (by rw [hEt, hn])
  subst hEX
  refine ⟨n, X, P, hn, hPlen, ?_⟩
  rw [OrientedTree.rowZ, hP, rowQ_cast, rowQ_cast]
  exact (rowQ_eq c hQ m p).symm

end Degree

/-! ### (2) The twisted trace surjection -/

section Trace

variable [Fintype D] [DecidableEq D] [DecidableRel T.orient]
  (σ : D ≃ D) (hσ : ∀ a b, T.G.Adj (σ a) (σ b) ↔ T.G.Adj a b)

/-- `⊕_x kΔ̄(x, σ x)`. -/
abbrev TwPaths := ∀ x : D,
  (LinearPaths.obj (k := k) (T.toDbl x) ⟶ LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x)))

/-- The component at `x`. -/
def tsingle (x : D) (g : LinearPaths.obj (k := k) (T.toDbl x) ⟶
    LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x))) : T.TwPaths (k := k) σ hσ :=
  Pi.single (M := fun x ↦ LinearPaths.obj (k := k) (T.toDbl x) ⟶
    LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x))) x g

theorem tsingle_apply_same (x : D) (g : LinearPaths.obj (k := k) (T.toDbl x) ⟶
    LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x))) : T.tsingle σ hσ x g x = g :=
  Pi.single_eq_same _ _

theorem tsingle_apply_ne {x x' : D} (h : x' ≠ x) (g : LinearPaths.obj (k := k) (T.toDbl x) ⟶
    LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x))) : T.tsingle σ hσ x g x' = 0 :=
  Pi.single_eq_of_ne h _

/-- The relations of the twisted trace space in degree `d`: the ideal of `Π(Δ)`, the twisted
rotations `uv − v σ(u)`, and the other degrees. -/
def twRel (d : ℕ) : Submodule k (T.TwPaths (k := k) σ hσ) :=
  Submodule.span k
    ({f : T.TwPaths (k := k) σ hσ | ∃ (x : D) (g : LinearPaths.obj (k := k) (T.toDbl x) ⟶
          LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x))),
        g ∈ (T.preproj k).ideal _ _ ∧ f = T.tsingle σ hσ x g} ∪
      {f : T.TwPaths (k := k) σ hσ | ∃ (x z : D) (U : Quiver.Path (T.toDbl x) (T.toDbl z))
          (W : Quiver.Path (T.toDbl z) ((T.dAct σ hσ).obj (T.toDbl x))),
        f = T.tsingle σ hσ x (LinearPaths.path (k := k) (U.comp W)) -
          T.tsingle σ hσ z (LinearPaths.path (k := k) (W.comp ((T.dAct σ hσ).mapPath U)))} ∪
      {f : T.TwPaths (k := k) σ hσ | ∃ (x : D) (e : ℕ) (g : LinearPaths.obj (k := k) (T.toDbl x) ⟶
          LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x))),
        e ≠ d ∧ g ∈ LinearPaths.degreePart (k := k) e _ _ ∧ f = T.tsingle σ hσ x g})

/-- **The twisted trace space** `T_σ(Π)_d` of `eq:twisted-trace-space`. -/
abbrev TwTrace (d : ℕ) := T.TwPaths (k := k) σ hσ ⧸ T.twRel (k := k) σ hσ d

/-- A base point of height of the parity of `x`. -/
def X0 (x : D) : T.ZVert := ⟨x, ((T.par x).val : ℤ), by rw [Int.cast_natCast, ZMod.natCast_zmod_val]⟩

/-- Lifting the degree-`(m+1)` components from the base points. -/
def twMapF (m : ℕ) : T.TwPaths (k := k) σ hσ →ₗ[k] Coker c m :=
  ∑ x : D, (T.phiL hQ π c m (T.X0 x) ((T.dAct σ hσ).obj (T.toDbl x))) ∘ₗ
    (LinearPaths.proj (k := k) (m + 1) _ _) ∘ₗ LinearMap.proj x

theorem twMapF_single (m : ℕ) (x : D) (g : LinearPaths.obj (k := k) (T.toDbl x) ⟶
    LinearPaths.obj ((T.dAct σ hσ).obj (T.toDbl x))) :
    T.twMapF hQ π c σ hσ m (T.tsingle σ hσ x g) =
      T.phiL hQ π c m (T.X0 x) _ (LinearPaths.proj (k := k) (m + 1) _ _ g) := by
  unfold twMapF
  rw [LinearMap.sum_apply, Finset.sum_eq_single x]
  · show T.phiL hQ π c m (T.X0 x) _ (LinearPaths.proj (k := k) (m + 1) _ _
      (T.tsingle σ hσ x g x)) = _
    rw [tsingle_apply_same]
  · intro x' _ hx'
    show T.phiL hQ π c m (T.X0 x') _ (LinearPaths.proj (k := k) (m + 1) _ _
      (T.tsingle σ hσ x g x')) = 0
    rw [tsingle_apply_ne T σ hσ hx', map_zero, map_zero]
  · simp

theorem proj_mem_ideal (e : ℕ) {a b : T.Dbl} {g : LinearPaths.obj (k := k) a ⟶ LinearPaths.obj b}
    (hg : g ∈ (T.preproj k).ideal _ _) :
    LinearPaths.proj (k := k) e a b g ∈ (T.preproj k).ideal _ _ := by
  refine (T.preproj k).ideal_induction
    (P := fun g ↦ LinearPaths.proj (k := k) e a b g ∈ (T.preproj k).ideal _ _)
    (by simp) (fun f g hf hg ↦ by rw [map_add]; exact add_mem hf hg)
    (fun t f hf ↦ by rw [map_smul]; exact Submodule.smul_mem _ t hf) (fun i p p' ↦ ?_) hg
  have hdeg : LinearPaths.path (k := k) p ≫ (T.preproj k).rel i ≫ LinearPaths.path p' ∈
      LinearPaths.degreePart (k := k) (p.length + (2 + p'.length)) _ _ :=
    LinearPaths.comp_mem_degreePart (LinearPaths.path_mem_degreePart (k := k) p)
      (LinearPaths.comp_mem_degreePart (T.preprojRel_mem_degreePart (k := k) i)
        (LinearPaths.path_mem_degreePart (k := k) p'))
  rw [LinearPaths.proj_of_mem hdeg]
  split_ifs
  · exact (T.preproj k).comp_rel_comp_mem i _ _
  · exact zero_mem _

variable [Fintype V] [DecidablePred (· ∈ Q.periodic)] [Fintype Q.nonprojective]

/-- The degree-`(m+1)` cokernel of `D_m`, inside `Coker c m`. -/
abbrev cokerDeg' (m : ℕ) : Submodule k (Coker c m) := (famDeg c (m + 1)).map (imageD c m).mkQ

theorem rowQ_mem (m : ℕ) {u y : V} (w : Quiver.Path u y) (hw : w.length = m + 1) :
    rowQ c hQ m w ∈ cokerDeg' c m := by
  unfold rowQ
  split_ifs with h
  · refine ⟨row c _ (w.cast h rfl), ?_, rfl⟩
    have := row_mem_famDeg c (m := m) ⟨y, hQ.mem_nonprojective y⟩ (w.cast h rfl)
      (by rw [length_cast']; exact hw) 1
    rwa [one_smul] at this
  · exact zero_mem _

theorem phiL_mem (m : ℕ) (X : T.ZVert) (b : T.Dbl)
    {g : LinearPaths.obj (k := k) (T.toDbl X.v) ⟶ LinearPaths.obj b}
    (hg : g ∈ LinearPaths.degreePart (k := k) (m + 1) _ _) :
    T.phiL hQ π c m X b g ∈ cokerDeg' c m := by
  induction hg using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, hp, rfl⟩ := hf
      unfold phiL
      rw [LinearPaths.extend_path, phiD, rowZ]
      exact rowQ_mem hQ c m _ (by rw [LinearPaths.length_mapPath, length_liftZ, hp])
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
  | smul t f _ hf => rw [map_smul]; exact Submodule.smul_mem _ t hf

variable (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))
  (hsig : T.pullCoeff hQ π c = T.zSigned k) (hc : OppositeOnMates c hQ) (s : ℤ)
  (hσp : ∀ v, T.par (σ v) = T.par v + s)
  (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z)

include hπ hτ hsig hc hdeck in
/-- The relations of `T_σ(Π)_{m+1}` have zero row classes: the ideal of `Π(Δ)` lifts term by term,
twisted rotation is `phiD_rotate_path`, and the height does not matter (`phiD_height`). -/
theorem twRel_le_ker {m : ℕ} (hs : (m : ℤ) + 1 = 2 + s) :
    T.twRel (k := k) σ hσ (m + 1) ≤ LinearMap.ker (T.twMapF hQ π c σ hσ m) := by
  unfold twRel
  rw [Submodule.span_le]
  rintro f ((⟨x, g, hg, rfl⟩ | ⟨x, z, U, W, rfl⟩) | ⟨x, e, g, he, hg, rfl⟩)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, twMapF_single]
    exact T.phiL_eq_zero_of_mem hQ π c hπ hτ hsig m _ (T.proj_mem_ideal (m + 1) hg)
  · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, twMapF_single, twMapF_single,
      LinearPaths.proj_path, LinearPaths.proj_path, sub_eq_zero]
    have hlen : (W.comp ((T.dAct σ hσ).mapPath U)).length = (U.comp W).length := by
      rw [Quiver.Path.length_comp, Quiver.Path.length_comp, LinearPaths.length_mapPath, add_comm]
    rw [hlen]
    split_ifs with h
    · unfold phiL
      rw [LinearPaths.extend_path, LinearPaths.extend_path,
        T.phiD_rotate_path hQ π c hτ σ hσ s hσp hc hdeck hs (T.X0 x) U W
          (by rw [← Quiver.Path.length_comp, h])]
      exact T.phiD_height hQ π c hτ σ hσ s hσp hc hdeck hs (T.liftEnd (T.X0 x) U) _
        (by rw [hlen, h]) _ _
    · rfl
  · have hg' : g ∈ LinearPaths.degreePart (k := k) e (T.toDbl (T.X0 x).v) _ := hg
    rw [SetLike.mem_coe, LinearMap.mem_ker, twMapF_single, LinearPaths.proj_of_mem hg',
      if_neg he, map_zero]

/-- **The twisted trace map** `T_σ(Π)_{m+1} → coker D_m`. -/
def twMap {m : ℕ} (hs : (m : ℤ) + 1 = 2 + s) : T.TwTrace (k := k) σ hσ (m + 1) →ₗ[k] Coker c m :=
  (T.twRel σ hσ (m + 1)).liftQ (T.twMapF hQ π c σ hσ m)
    (T.twRel_le_ker hQ π c σ hσ hπ hτ hsig hc s hσp hdeck hs)

include hπ hτ hsig hc hdeck in
/-- **Lemma A.2(2)** (`lem:twisted-trace-surjection`), for an arbitrary finite tree `Δ`: for the
twist `σ` with height shift `s` (`m + 1 = 2 + s`, so the degree is `d = m + 1`), when the lifts of
rows from `τ X` end at `σ`-translates (`hfib`), the twisted trace map is a surjection
`T_σ(Π)_d → coker D_{d−1}`: its range is the degree-`d` cokernel. -/
theorem twistedTraceSurjection (hsurj : ∀ x : V, ∃ X, π.obj X = x)
    (hfib : ∀ X E : T.ZVert, π.obj E = π.obj X → E.t = X.t + s →
      E = (T.zAct σ hσ s hσp).obj X)
    {m : ℕ} (hs : (m : ℤ) + 1 = 2 + s) :
    LinearMap.range (T.twMap hQ π c σ hσ hπ hτ hsig hc s hσp hdeck hs) = cokerDeg' c m := by
  rw [twMap, Submodule.range_liftQ]
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    unfold twMapF
    rw [LinearMap.sum_apply]
    exact sum_mem fun x _ ↦ T.phiL_mem hQ π c m _ _ (LinearPaths.proj_mem _)
  · refine (Submodule.map_mono (famDeg_le_rows c m)).trans ?_
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, w, hw, rfl⟩, rfl⟩
    obtain ⟨X, hX⟩ := hsurj x.1
    have e1 : π.obj (T.ztau X) = (Q.tau x).1 := by rw [hτ, hX]; rfl
    obtain ⟨E, hE, P, hP⟩ := RelSystem.exists_lift π hπ (T.ztau X) (w.cast e1.symm rfl)
    have hPlen : P.length = m + 1 := by
      rw [← LinearPaths.length_mapPath π P, hP, length_cast', length_cast', hw]
    have hEt : E.t = X.t + s := by
      have := T.t_path P
      rw [hPlen] at this
      simp only [ztau] at this
      push_cast at this
      omega
    have hEX : E = (T.zAct σ hσ s hσp).obj X := hfib X E (hE.trans hX.symm) hEt
    have r1 : rowClass c m x w = T.rowZ hQ π c m P := by
      rw [OrientedTree.rowZ, hP, rowQ_cast, rowQ_cast]
      exact (rowQ_eq c hQ m w).symm
    set p' : Quiver.Path (T.toDbl X.v) ((T.dAct σ hσ).obj (T.toDbl X.v)) :=
      (T.forget.mapPath P).cast rfl (congrArg OrientedTree.ZVert.v hEX)
    have hp' : p'.length = m + 1 := by
      rw [length_cast', LinearPaths.length_mapPath, hPlen]
    have r2 : T.rowZ hQ π c m P = T.phiD hQ π c m X p' := by
      apply T.rowZ_eq_of_pathStar
      apply T.pathStar_eq_of_forget
      refine Sigma.ext (by have := congrArg OrientedTree.ZVert.v hEX; exact this) ?_
      rw [forget_mapPath_liftZ]
      dsimp only
      exact (Quiver.Path.cast_heq _ _ _).symm
    have r3 : T.phiD hQ π c m X p' = T.phiD hQ π c m (T.X0 X.v) p' :=
      T.phiD_height hQ π c hτ σ hσ s hσp hc hdeck hs X p' hp' _ _
    refine ⟨T.tsingle σ hσ X.v (LinearPaths.path p'), ?_⟩
    rw [twMapF_single, LinearPaths.proj_path, if_pos hp']
    unfold phiL
    rw [LinearPaths.extend_path, ← r3, ← r2, ← r1]
    rfl

end Trace

/-! ### The allowed degrees -/

section Deck

variable [Fintype D] [DecidableEq D] [DecidableRel T.orient] [Fintype V]
  [DecidablePred (· ∈ Q.periodic)] [Fintype Q.nonprojective]
  (ρ : D ≃ D) (hρ : ∀ a b, T.G.Adj (ρ a) (ρ b) ↔ T.G.Adj a b) (c0 : ℕ) (hc0 : 0 < c0)
  (hρp : ∀ v, T.par (ρ v) = T.par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj ((T.zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
  (hfib : ∀ X Y : T.ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (T.gV ρ hρ c0 hρp)^[n] X ∨ X = (T.gV ρ hρ c0 hρp)^[n] Y)
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))
  (hsurj : ∀ x : V, ∃ X, π.obj X = x) (hsig : T.pullCoeff hQ π c = T.zSigned k)
  (hc : OppositeOnMates c hQ)

include hc0 hfib hsurj in
/-- **Lemma A.2(2) in an allowed degree**: if `n c₀ = m − 1`, the twisted trace map for the twist
`θ = ρ^n` is onto the degree-`(m+1)` cokernel. -/
theorem twistedTraceSurjection_deck {m n : ℕ} (hn : ((n * c0 : ℕ) : ℤ) = m - 1) :
    LinearMap.range (T.twMap hQ π c (ρ ^ n) (T.adj_pow ρ hρ n) hπ hτ hsig hc ((n * c0 : ℕ) : ℤ)
      (T.par_pow ρ c0 hρp n) (T.gPow_deck π ρ hρ c0 hρp hdeck n) (by omega)) =
      cokerDeg' c m :=
  T.twistedTraceSurjection hQ π c (ρ ^ n) (T.adj_pow ρ hρ n) hπ hτ hsig hc _ _ _ hsurj
    (fun X E h1 h2 ↦ T.gPow_fib π ρ hρ c0 hρp hfib hc0 n X E h1 h2) _

end Deck

end OrientedTree

end MultiplicativeBasisDeformations
