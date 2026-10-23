module

public import MultiplicativeBasisDeformations.Foundations.OddGaugeQ
public import MultiplicativeBasisDeformations.Foundations.StarCase

/-!
# The odd quotients of even `A` (Appendix A)

`periodic-mesh-calculations.tex`, "The odd quotients of even A": with all
mesh coefficients one, "a correction to an arrow gives a relation between a row
path and its one-arrow rotation, with opposite classes"; rows are reduced by the
sum of their levels to words in the middle arrows `ε`, and "going around the
cycle gives `w_j = -w_j`".
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace ScalarMeshCategory

variable {k : Type u} [Field k] {V : Type v'} [Quiver.{w} V]
  {Q : TranslationQuiver V} [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
  (c : MeshCoefficients k Q) [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)]
  [DecidablePred (· ∈ Q.nonprojective)] (hQ : Q.IsStable)

/-- **Rotation with all coefficients one**: a row and its one-arrow rotation have
opposite classes. -/
theorem rowClass_rotate_one (hc : ∀ x y a, c x y a = 1) {m : ℕ}
    (x : Q.nonprojective) {y : V} (a : y ⟶ x.1) (q : Quiver.Path (Q.tau x).1 y)
    (hq : q.length = m) :
    rowClass c m x (q.cons a) =
      -rowClass c m ⟨y, hQ.mem_nonprojective y⟩
        ((Q.mate ⟨y, hQ.mem_nonprojective y⟩ (Q.tau x).1 (Q.mate x y a)).toPath.comp q) := by
  have hcol : meshDerivative c (Pi.single (⟨(Q.tau x).1, y, Q.mate x y a⟩ : Σ u v : V, u ⟶ v)
      (pathMor c q)) ∈ imageD c m :=
    ⟨_, single_mem_familiesDeg c _ q hq, rfl⟩
  rw [column_eq, dif_pos (hQ.mem_nonprojective y), hc, hc, Units.val_one, one_smul,
    one_smul] at hcol
  unfold rowClass
  rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero]
  exact hcol

theorem rowQ_rotate_one [∀ x y : V, Subsingleton (x ⟶ y)] (hc : ∀ x y a, c x y a = 1) {m : ℕ}
    {x y : V} (a : y ⟶ x) (b : hQ.tauE y ⟶ hQ.tauE x) (q : Quiver.Path (hQ.tauE x) y)
    (hq : q.length = m) : rowQ c hQ m (b.toPath.comp q) = -rowQ c hQ m (q.cons a) := by
  rw [rowQ_eq, rowQ_eq, rowClass_rotate_one c hQ hc ⟨x, hQ.mem_nonprojective x⟩ a q hq, neg_neg]
  rw [Subsingleton.elim b]

end ScalarMeshCategory

namespace OrientedTree

open ScalarMeshCategory

variable {D : Type*} (T : OrientedTree D) [Fintype D] [DecidableEq D]
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : T.ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]

/-- All coefficients one on `Q`, from all coefficients one upstairs. -/
theorem one_of_pull (hπ : π.IsCovering) (hsurj : ∀ x : V, ∃ X, π.obj X = x)
    (hone : T.pullCoeff hQ π c = fun _ _ _ ↦ 1) : ∀ x y a, c x y a = 1 := by
  intro x y a
  obtain ⟨X, hX⟩ := hsurj x.1
  obtain ⟨⟨Y, A⟩, hYA⟩ := (hπ.costar_bijective X).2 ⟨y, Quiver.Hom.cast rfl hX.symm a⟩
  have hY : π.obj Y = y := congrArg Sigma.fst hYA
  have e1 : c x y a = T.pullCoeff hQ π c ⟨X, trivial⟩ Y A :=
    StarGauge.c_congr c (Subtype.ext hX.symm) hY.symm _ _
  rw [e1, hone]

omit [Fintype D] [DecidableEq D] in
/-- Rotation of a lifted row, all coefficients one. -/
theorem rowZ_rotate_one (hc : ∀ x y a, c x y a = 1) {m : ℕ} {Z Y₁ E E' : T.ZVert} (a₁ : Z ⟶ Y₁)
    (B : Quiver.Path Y₁ E) (a₂ : E ⟶ E') (hZ : π.obj Z = hQ.tauE (π.obj E))
    (hY : π.obj Y₁ = hQ.tauE (π.obj E')) (hB : B.length = m) :
    T.rowZ hQ π c m (a₁.toPath.comp B) = -T.rowZ hQ π c m (B.cons a₂) := by
  rw [rowZ, rowZ, Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath, Prefunctor.mapPath_cons]
  have key : ∀ {u w₁ y x : V} (hu : u = hQ.tauE y) (hw : w₁ = hQ.tauE x) (b : u ⟶ w₁) (a : y ⟶ x)
      (q : Quiver.Path w₁ y), q.length = m →
      rowQ c hQ m (b.toPath.comp q) = -rowQ c hQ m (q.cons a) := by
    intro u w₁ y x hu hw b a q hq
    subst hu hw
    exact rowQ_rotate_one c hQ hc a b q hq
  exact key hZ hY _ _ _ (by rw [LinearPaths.length_mapPath, hB])

/-- Inverse translation as an automorphism of the quiver `ℤΔ`. -/
def tauInvQ : T.ZVert ⥤q T.ZVert where
  obj := T.ztauInv
  map a := ⟨⟨a.down.1, by simp only [ztauInv, a.down.2]; ring⟩⟩

section Rot

variable (σ : D ≃ D) (hσ : ∀ a b, T.G.Adj (σ a) (σ b) ↔ T.G.Adj a b) (s : ℤ)
  (hσp : ∀ v, T.par (σ v) = T.par v + s)
  (hdeck : ∀ Z, π.obj ((T.zAct σ hσ s hσp).obj Z) = π.obj Z)
  (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))

/-- The deck image of the inverse translate: the end of a row path from `Z`. -/
abbrev rowEnd (Z : T.ZVert) : T.ZVert := (T.zAct σ hσ s hσp).obj (T.ztauInv Z)

/-- The translate of an initial segment, appended at the end in a rotation. -/
def shiftPath {Z Y : T.ZVert} (U : Quiver.Path Z Y) :
    Quiver.Path (T.rowEnd σ hσ s hσp Z) (T.rowEnd σ hσ s hσp Y) :=
  (T.zAct σ hσ s hσp).mapPath ((T.tauInvQ).mapPath U)

include hdeck hτ in
theorem row_cond (Z : T.ZVert) : π.obj Z = hQ.tauE (π.obj (T.rowEnd σ hσ s hσp Z)) := by
  rw [rowEnd, hdeck, ← hτ]
  exact congrArg π.obj (by ext <;> simp [ztau, ztauInv])

include hdeck hτ in
/-- **Rotation of an initial segment** of a lifted row, all coefficients one:
`[U W] = (-1)^{|U|} [W U']`. -/
theorem rowZ_rotate_path (hc : ∀ x y a, c x y a = 1) {m : ℕ} {Z : T.ZVert} :
    ∀ {Y : T.ZVert} (U : Quiver.Path Z Y) (W : Quiver.Path Y (T.rowEnd σ hσ s hσp Z)),
      U.length + W.length = m + 1 →
      T.rowZ hQ π c m (U.comp W) =
        (-1) ^ U.length • T.rowZ hQ π c m (W.comp (T.shiftPath σ hσ s hσp U)) := by
  intro Y U
  induction U with
  | nil =>
      intro W _
      simp [shiftPath]
  | @cons Y₀ Y U' e ih =>
      intro W hW
      rw [Quiver.Path.length_cons] at hW
      have h1 : (U'.cons e).comp W = U'.comp (e.toPath.comp W) := by
        rw [← Quiver.Path.comp_assoc]; rfl
      rw [h1, ih _ (by rw [Quiver.Path.length_comp, Quiver.Path.length_toPath]; omega),
        Quiver.Path.comp_assoc]
      -- rotate the arrow `e`
      let e' : T.rowEnd σ hσ s hσp Y₀ ⟶ T.rowEnd σ hσ s hσp Y :=
        (T.zAct σ hσ s hσp).map ((T.tauInvQ).map e)
      rw [T.rowZ_rotate_one hQ π c hc e (W.comp (T.shiftPath σ hσ s hσp U')) e'
        (T.row_cond hQ π σ hσ s hσp hdeck hτ Y₀) (T.row_cond hQ π σ hσ s hσp hdeck hτ Y)
        (by rw [Quiver.Path.length_comp]
            simp only [shiftPath, LinearPaths.length_mapPath]; omega)]
      rw [Quiver.Path.length_cons, pow_succ, mul_comm, mul_smul, neg_one_smul, smul_neg]
      rw [show W.comp (T.shiftPath σ hσ s hσp (U'.cons e)) =
        (W.comp (T.shiftPath σ hσ s hσp U')).cons e' from rfl]

end Rot

variable [DecidableRel T.orient]

include hQ in
theorem sigma_eq_of_fst {X : T.ZVert} (e e' : Σ Y : T.ZVert, Y ⟶ X) (h : e.1 = e'.1) : e = e' := by
  obtain ⟨Y, a⟩ := e
  obtain ⟨Y', a'⟩ := e'
  simp only at h
  subst h
  rw [Subsingleton.elim a a']

/-- **A mesh with two terms** (all coefficients one): replacing one two-arrow
path through the mesh by the other changes the sign of the class. -/
theorem rowZ_two_term (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))
    (hone : T.pullCoeff hQ π c = fun _ _ _ ↦ 1) {m : ℕ} {X Y₁ Y₂ : T.ZVert} (hne : Y₁ ≠ Y₂)
    (a₁ : Y₁ ⟶ X) (a₂ : Y₂ ⟶ X) (hall : ∀ e : Σ Y : T.ZVert, Y ⟶ X, e.1 = Y₁ ∨ e.1 = Y₂)
    (b₁ : T.ztau X ⟶ Y₁) (b₂ : T.ztau X ⟶ Y₂) {Z E : T.ZVert} (A : Quiver.Path Z (T.ztau X))
    (B : Quiver.Path X E) :
    T.rowZ hQ π c m (A.comp ((b₁.toPath.comp a₁.toPath).comp B)) +
      T.rowZ hQ π c m (A.comp ((b₂.toPath.comp a₂.toPath).comp B)) = 0 := by
  classical
  have hmem := (RelSystem.mesh (T.pullCoeff hQ π c)).comp_rel_comp_mem
    (⟨X, trivial⟩ : T.zQuiver.nonprojective) (LinearPaths.path A) (LinearPaths.path B)
  have h0 := T.rowZL_eq_zero_of_mem hQ π c hπ hτ m hmem
  rw [RelSystem.mesh_rel] at h0
  unfold meshRelation at h0
  rw [Preadditive.sum_comp, Preadditive.comp_sum, map_sum,
    Fintype.sum_eq_add (⟨Y₁, a₁⟩ : Σ Y : T.ZVert, Y ⟶ X) ⟨Y₂, a₂⟩] at h0
  · rw [← h0]
    simp only [hone, Units.val_one, one_smul, Linear.smul_comp, Linear.comp_smul,
      LinearPaths.path_comp_path]
    congr 1
    · rw [rowZL, LinearPaths.extend_path,
        Subsingleton.elim b₁ (T.zQuiver.mate ⟨X, trivial⟩ Y₁ a₁), Quiver.Path.comp_assoc]
    · rw [rowZL, LinearPaths.extend_path,
        Subsingleton.elim b₂ (T.zQuiver.mate ⟨X, trivial⟩ Y₂ a₂), Quiver.Path.comp_assoc]
  · intro h; exact hne (congrArg Sigma.fst h)
  · rintro e ⟨h1, h2⟩
    rcases hall e with h | h
    · exact absurd (T.sigma_eq_of_fst hQ e _ h) h1
    · exact absurd (T.sigma_eq_of_fst hQ e _ h) h2

/-- **Peak replacement**: at a vertex with exactly two in-neighbours, a row
beginning `Z₀ → W → Z₂` has the opposite class of the row beginning
`Z₀ → W' → Z₂`. -/
theorem rowZ_peak (hπ : π.IsCovering) (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))
    (hone : T.pullCoeff hQ π c = fun _ _ _ ↦ 1) {m : ℕ} {Z₀ W W' Z₂ E : T.ZVert}
    (hZ : Z₀ = T.ztau Z₂) (b₁ : Z₀ ⟶ W) (b₂ : W ⟶ Z₂) (c₁ : Z₀ ⟶ W') (c₂ : W' ⟶ Z₂)
    (hne : W ≠ W') (hall : ∀ e : Σ Y : T.ZVert, Y ⟶ Z₂, e.1 = W ∨ e.1 = W')
    (B : Quiver.Path Z₂ E) :
    T.rowZ hQ π c m (b₁.toPath.comp (b₂.toPath.comp B)) =
      -T.rowZ hQ π c m (c₁.toPath.comp (c₂.toPath.comp B)) := by
  subst hZ
  have := T.rowZ_two_term hQ π c hπ hτ hone (m := m) hne b₂ c₂ hall b₁ c₁ Quiver.Path.nil B
  simp only [Quiver.Path.nil_comp, Quiver.Path.comp_assoc] at this
  exact eq_neg_of_add_eq_zero_left this

end OrientedTree

namespace EvenA

open OrientedTree

variable {L : Fin 1 → ℕ} (h : ℕ) (hh : 1 ≤ h) (hL : L 0 = 2 * h - 2)

/-- The level of a depth: the distance to the middle edge, plus one. -/
def lev (d : ℕ) : ℕ := if h ≤ d then d + 1 - h else h - d

/-- The level of a vertex of `ℤΔ`. -/
abbrev levZ (X : (starTree L).ZVert) : ℕ := lev h (starDepth X.v)

theorem lev_pos (d : ℕ) : 1 ≤ lev h d ∨ (d < h ∧ h = 0) := by
  unfold lev; split_ifs <;> omega

include hh in
theorem lev_ge_one (d : ℕ) : 1 ≤ lev h d := by
  unfold lev; split_ifs <;> omega

/-- Levels of adjacent depths differ by one, except across the middle edge. -/
theorem lev_adj (d : ℕ) :
    (lev h (d + 1) = lev h d + 1 ∨ lev h d = lev h (d + 1) + 1) ∨ (d + 1 = h) := by
  unfold lev; split_ifs <;> omega

theorem lev_rev (d : ℕ) (hd : d < 2 * h) : lev h (2 * h - 1 - d) = lev h d := by
  unfold lev; split_ifs <;> omega

/-- Across an edge at a vertex of level at least two, levels differ by one. -/
theorem lev_adj' (a b : ℕ) (hab : b = a + 1 ∨ a = b + 1) (hb : 2 ≤ lev h b) :
    lev h a = lev h b + 1 ∨ lev h a + 1 = lev h b := by
  unfold lev at *; split_ifs at * <;> omega

/-- A vertex of level at least two has a unique neighbour of smaller level. -/
theorem inward_unique (d d₁ d₂ : ℕ) (h2 : 2 ≤ lev h d)
    (h1 : d₁ = d + 1 ∨ d = d₁ + 1) (h1' : lev h d₁ < lev h d)
    (h2' : d₂ = d + 1 ∨ d = d₂ + 1) (h2'' : lev h d₂ < lev h d) : d₁ = d₂ := by
  unfold lev at *; split_ifs at * <;> omega

/-- The sum of the levels of a row, the last vertex omitted. -/
def lamC {Z E : (starTree L).ZVert} (P : Quiver.Path Z E) : ℕ :=
  ((P.vertices.dropLast).map (levZ h)).sum

theorem dropLast_vertices_comp {W : Type*} [Quiver W] {a b c : W} (p : Quiver.Path a b)
    (q : Quiver.Path b c) :
    (p.comp q).vertices.dropLast = p.vertices.dropLast ++ q.vertices.dropLast := by
  rw [Quiver.Path.vertices_comp, List.dropLast_append_of_ne_nil (Quiver.Path.vertices_ne_nil q)]

theorem lamC_comp {Z Y E : (starTree L).ZVert} (p : Quiver.Path Z Y) (q : Quiver.Path Y E) :
    lamC h (p.comp q) = lamC h p + lamC h q := by
  unfold lamC
  rw [dropLast_vertices_comp, List.map_append, List.sum_append]

variable (σ : StarV L ≃ StarV L) (hσ : ∀ a b, (starTree L).G.Adj (σ a) (σ b) ↔ (starTree L).G.Adj a b)
  (s : ℤ) (hσp : ∀ v, (starTree L).par (σ v) = (starTree L).par v + s)
  (hσlev : ∀ v, lev h (starDepth (σ v)) = lev h (starDepth v))

include hσlev in
theorem lamC_shift {Z Y : (starTree L).ZVert} (U : Quiver.Path Z Y) :
    lamC h ((starTree L).shiftPath σ hσ s hσp U) = lamC h U := by
  unfold lamC shiftPath
  rw [LinearPaths.vertices_mapPath, LinearPaths.vertices_mapPath, ← List.map_dropLast,
    ← List.map_dropLast, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  simp only [Function.comp_apply, levZ]
  exact hσlev v.v

include hσlev in
/-- Rotation preserves the level sum. -/
theorem lamC_rot {Z Y : (starTree L).ZVert} (U : Quiver.Path Z Y)
    (W : Quiver.Path Y ((starTree L).rowEnd σ hσ s hσp Z)) :
    lamC h (W.comp ((starTree L).shiftPath σ hσ s hσp U)) = lamC h (U.comp W) := by
  rw [lamC_comp, lamC_comp, lamC_shift h σ hσ s hσp hσlev, add_comm]

include hσlev in
theorem levZ_shift_mem {Z Y : (starTree L).ZVert} (U : Quiver.Path Z Y) {v : (starTree L).ZVert}
    (hv : v ∈ ((starTree L).shiftPath σ hσ s hσp U).vertices) :
    ∃ v' ∈ U.vertices, levZ h v = levZ h v' := by
  unfold shiftPath at hv
  rw [LinearPaths.vertices_mapPath, LinearPaths.vertices_mapPath, List.map_map,
    List.mem_map] at hv
  obtain ⟨v', hv', rfl⟩ := hv
  exact ⟨v', hv', hσlev v'.v⟩

theorem exists_arrow_to {W : Type*} [Quiver W] {a b : W} (P : Quiver.Path a b) {v : W}
    (hv : v ∈ P.vertices) (hne : v ≠ a) :
    ∃ (c : W) (U : Quiver.Path a c) (e : c ⟶ v) (X : Quiver.Path v b), P = U.comp (e.toPath.comp X) := by
  induction P with
  | nil => simp at hv; exact absurd hv hne
  | @cons b' b P' e ih =>
      rw [Quiver.Path.mem_vertices_cons] at hv
      rcases hv with hv | rfl
      · obtain ⟨c, U, e', X, rfl⟩ := ih hv
        exact ⟨c, U, e', X.cons e, by simp [Quiver.Path.comp_cons]⟩
      · exact ⟨b', P', e, Quiver.Path.nil, rfl⟩

theorem lamC_cons_front {Z Y E : (starTree L).ZVert} (e : Z ⟶ Y) (X : Quiver.Path Y E) :
    lamC h (e.toPath.comp X) = levZ h Z + lamC h X := by
  rw [lamC_comp]
  simp [lamC]

theorem adj_depth {a b : StarV L} : (starTree L).G.Adj a b ↔
    (starDepth b = starDepth a + 1 ∨ starDepth a = starDepth b + 1) := ReRoot.adj_one a b

include hh hL in
/-- **The other in-neighbour**: at a vertex `Z₂` with an outward in-neighbour `W`,
there is exactly one further in-neighbour `W'`, of smaller level than `W`. -/
theorem other_in (Z₂ W : (starTree L).ZVert) (b : W ⟶ Z₂) (hout : levZ h W = levZ h Z₂ + 1) :
    ∃ (W' : (starTree L).ZVert) (c₂ : W' ⟶ Z₂) (c₁ : (starTree L).ztau Z₂ ⟶ W'),
      W ≠ W' ∧ levZ h W' < levZ h W ∧ ∀ e : Σ Y : (starTree L).ZVert, Y ⟶ Z₂, e.1 = W ∨ e.1 = W' := by
  obtain ⟨hadj, ht⟩ := b.down
  have hadj' := adj_depth.1 hadj
  set u := starDepth Z₂.v
  set w := starDepth W.v
  have hu := depth_le Z₂.v
  have hw := depth_le W.v
  rw [hL] at hu hw
  -- the other depth
  have hw' : ∃ w' : ℕ, (w' = u + 1 ∨ u = w' + 1) ∧ w' ≠ w ∧ w' ≤ 2 * h - 1 ∧ lev h w' < lev h w := by
    have hout' : lev h w = lev h u + 1 := hout
    simp only [lev] at hout'
    rcases hadj' with h1 | h1
    · refine ⟨u + 1, Or.inl rfl, by omega, by split_ifs at hout' <;> omega, ?_⟩
      simp only [lev]; split_ifs at hout' ⊢ <;> omega
    · refine ⟨u - 1, Or.inr (by split_ifs at hout' <;> omega), by omega, by omega, ?_⟩
      simp only [lev]; split_ifs at hout' ⊢ <;> omega
  obtain ⟨w', hadjw', hne, hw'le, hlev⟩ := hw'
  have hpar : ((Z₂.t - 1 : ℤ) : ZMod 2) = (starTree L).par (OddGauge.vd L w') := by
    have h1 : (starTree L).par (OddGauge.vd L w') = ((w' : ℕ) : ZMod 2) := by
      change ((starDepth _ : ℕ) : ZMod 2) = _
      rw [OddGauge.depth_vd w' (by omega)]
    rw [h1]
    have h2 : ((Z₂.t : ℤ) : ZMod 2) = ((u : ℕ) : ZMod 2) := Z₂.ht
    push_cast; rw [h2]
    have key : ∀ x : ZMod 2, x - 1 = x + 1 := by decide
    rcases hadjw' with h3 | h3
    · rw [h3]; push_cast; exact key _
    · rw [h3]; push_cast; ring
  let W' : (starTree L).ZVert := ⟨OddGauge.vd L w', Z₂.t - 1, hpar⟩
  have hdW' : starDepth W'.v = w' := OddGauge.depth_vd w' (by omega)
  have c₂ : W' ⟶ Z₂ := ⟨⟨adj_depth.2 (by rw [hdW']; omega), by simp [W']⟩⟩
  have c₁ : (starTree L).ztau Z₂ ⟶ W' :=
    ⟨⟨adj_depth.2 (by rw [hdW']; change w' = starDepth Z₂.v + 1 ∨ starDepth Z₂.v = w' + 1; omega),
      by simp only [W', ztau]; ring⟩⟩
  refine ⟨W', c₂, c₁, fun h' ↦ hne (by rw [← hdW', ← h']), by
    unfold levZ; rw [hdW']; exact hlev, fun e ↦ ?_⟩
  obtain ⟨Y, a⟩ := e
  obtain ⟨hYa, hYt⟩ := a.down
  have hYd := adj_depth.1 hYa
  have hYt' : Y.t = Z₂.t - 1 := by omega
  by_cases hY : starDepth Y.v = w
  · left
    apply ZVert.ext
    · exact depth_injective hY
    · rw [hYt']; omega
  · right
    apply ZVert.ext
    · apply depth_injective; rw [hdW']; change starDepth Y.v = w'; omega
    · rw [hYt']

section Reduce

variable {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  (hπ : π.IsCovering) (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))
  (hone : (starTree L).pullCoeff hQ π c = fun _ _ _ ↦ 1) (hc : ∀ x y a, c x y a = 1)
  (hdeck : ∀ Z, π.obj (((starTree L).zAct σ hσ s hσp).obj Z) = π.obj Z)

include hh hL hπ hτ hone hc hdeck hσlev in
/-- **Reduction by the sum of levels** (`periodic-mesh-calculations.tex`):
if every row whose vertices all have level one (a word in the middle arrows) has
zero class, every row of length `m + 1` has zero class. -/
theorem reduce (m : ℕ) (hm : 1 ≤ m) (hs : (m : ℤ) + 1 = 2 + s)
    (hε : ∀ (Z : (starTree L).ZVert) (P : Quiver.Path Z ((starTree L).rowEnd σ hσ s hσp Z)),
      P.length = m + 1 → (∀ v ∈ P.vertices, levZ h v = 1) → (starTree L).rowZ hQ π c m P = 0) :
    ∀ (n : ℕ) (Z : (starTree L).ZVert) (P : Quiver.Path Z ((starTree L).rowEnd σ hσ s hσp Z)),
      P.length = m + 1 → lamC h P ≤ n → (starTree L).rowZ hQ π c m P = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Z P hP hn
  by_cases hall : ∀ v ∈ P.vertices, levZ h v = 1
  · exact hε Z P hP hall
  push_neg at hall
  obtain ⟨v1, hv1, hv1'⟩ := hall
  classical
  obtain ⟨v, hv, hmax⟩ := P.vertices.toFinset.exists_max_image (levZ h) ⟨v1, by simpa⟩
  rw [List.mem_toFinset] at hv
  have hmax' : ∀ x ∈ P.vertices, levZ h x ≤ levZ h v := fun x hx ↦ hmax x (by simpa)
  have hM : 2 ≤ levZ h v := by
    have := lev_ge_one h hh (starDepth v1.v); have := hmax' v1 hv1; unfold levZ at *; omega
  -- a vertex of maximal level other than the start
  have hend_lev : levZ h ((starTree L).rowEnd σ hσ s hσp Z) = levZ h Z := hσlev Z.v
  obtain ⟨v₀, hv₀, hne, hlev₀⟩ : ∃ v₀ ∈ P.vertices, v₀ ≠ Z ∧ levZ h v₀ = levZ h v := by
    by_cases hvZ : v = Z
    · refine ⟨_, Quiver.Path.end_mem_vertices P, fun h' ↦ ?_, by rw [hend_lev, hvZ]⟩
      have := congrArg ZVert.t h'
      simp only [rowEnd, zAct, ztauInv] at this
      omega
    · exact ⟨v, hv, hvZ, rfl⟩
  obtain ⟨c', U, e, X, hPeq⟩ := exists_arrow_to P hv₀ hne
  subst hPeq
  -- rotate the initial segment `U`
  have hrot := (starTree L).rowZ_rotate_path hQ π c σ hσ s hσp hdeck hτ hc U (e.toPath.comp X)
    (by rw [← Quiver.Path.length_comp]; exact hP)
  rw [Quiver.Path.comp_assoc] at hrot
  set S := (starTree L).shiftPath σ hσ s hσp U
  have hlen : (X.comp S).length = m := by
    have := hP
    rw [Quiver.Path.length_comp, Quiver.Path.length_comp, Quiver.Path.length_toPath] at this
    rw [Quiver.Path.length_comp]
    simp only [S, shiftPath, LinearPaths.length_mapPath]; omega
  obtain ⟨Z₂, b₂, B, hBlen, hXB⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ (X.comp S)
    (n := m - 1) (by omega)
  rw [hXB] at hrot
  -- levels around the peak
  have hlc : levZ h c' ≤ levZ h v := hmax' c' (Quiver.Path.mem_of_mem_left U _
    (Quiver.Path.end_mem_vertices U))
  have hlZ₂ : levZ h Z₂ ≤ levZ h v := by
    have hmem : Z₂ ∈ (X.comp S).vertices := by
      rw [hXB, Quiver.Path.vertices_comp]
      exact List.mem_append_right _ (StarTrace.start_mem_vertices B)
    rw [Quiver.Path.vertices_comp] at hmem
    rcases List.mem_append.1 hmem with hm' | hm'
    · exact hmax' Z₂ (Quiver.Path.mem_of_mem_right U _ (Quiver.Path.mem_of_mem_right e.toPath X
        (List.mem_of_mem_dropLast hm')))
    · obtain ⟨v', hv', hl⟩ := levZ_shift_mem h σ hσ s hσp hσlev U hm'
      rw [hl]; exact hmax' v' (Quiver.Path.mem_of_mem_left U _ hv')
  have hadj1 := adj_depth.1 e.down.1
  have hadj2 := adj_depth.1 b₂.down.1
  unfold levZ at hlc hlZ₂ hlev₀ hM
  have hv₀2 : 2 ≤ lev h (starDepth v₀.v) := by omega
  have hc1 : lev h (starDepth c'.v) + 1 = lev h (starDepth v₀.v) := by
    rcases lev_adj' h (starDepth c'.v) (starDepth v₀.v) hadj1 hv₀2 with h2 | h2 <;> omega
  have hc2 : lev h (starDepth Z₂.v) + 1 = lev h (starDepth v₀.v) := by
    rcases lev_adj' h (starDepth Z₂.v) (starDepth v₀.v) hadj2.symm hv₀2 with h2 | h2 <;> omega
  have hdep : starDepth c'.v = starDepth Z₂.v :=
    inward_unique h (starDepth v₀.v) _ _ (by omega)
      (by rcases hadj1 with h1 | h1 <;> omega) (by omega)
      (by rcases hadj2 with h1 | h1 <;> omega) (by omega)
  have hZ : c' = (starTree L).ztau Z₂ := by
    apply ZVert.ext
    · exact depth_injective hdep
    · have := e.down.2; have := b₂.down.2; simp only [ztau]; omega
  -- replace the peak
  obtain ⟨W', c₂, c₁, hneW, hltW, hallW⟩ := other_in h hh hL Z₂ v₀ b₂ (by unfold levZ; omega)
  have hpeak := (starTree L).rowZ_peak hQ π c hπ hτ hone (m := m) hZ e b₂
    (Quiver.Hom.cast hZ.symm rfl c₁) c₂ hneW hallW B
  set P'' := (Quiver.Hom.cast hZ.symm rfl c₁).toPath.comp (c₂.toPath.comp B)
  have hP'' : P''.length = m + 1 := by
    simp only [P'', Quiver.Path.length_comp, Quiver.Path.length_toPath, hBlen]; omega
  have hlam : lamC h P'' < n := by
    have e1 : lamC h (e.toPath.comp (b₂.toPath.comp B)) = lamC h (U.comp (e.toPath.comp X)) := by
      rw [← hXB, ← Quiver.Path.comp_assoc]
      exact lamC_rot h σ hσ s hσp hσlev U (e.toPath.comp X)
    simp only [P'', lamC_cons_front, levZ] at e1 ⊢
    unfold levZ at hltW
    omega
  rw [hrot, hpeak, ih _ hlam c' P'' hP'' le_rfl, neg_zero, smul_zero]

end Reduce

/-! ### Words in the middle arrows -/

theorem lev_one_iff (d : ℕ) : lev h d = 1 ↔ (d + 1 = h ∨ d = h) := by
  unfold lev; split_ifs <;> omega

include hh in
/-- **Middle paths are determined by their start and length.** -/
theorem dbl_mid_unique {a : (starTree L).Dbl} {b b' : (starTree L).Dbl} (p : Quiver.Path a b)
    (q : Quiver.Path a b') (hl : p.length = q.length)
    (hp : ∀ v ∈ p.vertices, lev h (starDepth (L := L) v) = 1)
    (hq : ∀ v ∈ q.vertices, lev h (starDepth (L := L) v) = 1) :
    (⟨b, p⟩ : Quiver.PathStar a) = ⟨b', q⟩ := by
  induction p generalizing b' with
  | nil =>
      cases q with
      | nil => rfl
      | cons q e => simp at hl
  | @cons c bb p e ih =>
      cases q with
      | nil => simp at hl
      | @cons c' _ q e' =>
          simp only [Quiver.Path.length_cons, Nat.add_right_cancel_iff] at hl
          have h1 := ih q hl (fun v hv ↦ hp v (by rw [Quiver.Path.mem_vertices_cons]; exact Or.inl hv))
            (fun v hv ↦ hq v (by rw [Quiver.Path.mem_vertices_cons]; exact Or.inl hv))
          obtain ⟨rfl, hpq⟩ := Sigma.mk.inj_iff.1 h1
          obtain rfl := eq_of_heq hpq
          -- the next middle vertex is forced
          have hb := hp bb (Quiver.Path.end_mem_vertices _)
          have hb' := hq b' (Quiver.Path.end_mem_vertices _)
          have hcm : c ∈ (p.cons e).vertices := by
            rw [Quiver.Path.mem_vertices_cons]; exact Or.inl (Quiver.Path.end_mem_vertices p)
          have hc := hp c hcm
          have ha := adj_depth.1 e.down
          have ha' := adj_depth.1 e'.down
          rw [lev_one_iff] at hb hb' hc
          have : bb = b' := depth_injective (show starDepth (L := L) bb = starDepth (L := L) b' by omega)
          subst this
          rw [Subsingleton.elim e e']

include hh in
/-- Two middle depths of the same parity coincide. -/
theorem mid_eq_of_par {a b : ℕ} (ha : lev h a = 1) (hb : lev h b = 1)
    (hab : ((a : ℕ) : ZMod 2) = ((b : ℕ) : ZMod 2)) : a = b := by
  rw [lev_one_iff] at ha hb
  have key : ∀ x : ZMod 2, x ≠ x + 1 := by decide
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · omega
  · exfalso
    have : b = a + 1 := by omega
    rw [this] at hab; push_cast at hab
    exact key _ hab
  · exfalso
    have : a = b + 1 := by omega
    rw [this] at hab; push_cast at hab
    exact key _ hab.symm
  · omega

section Eps

variable {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [Field k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)
  [DecidableEq V] [∀ x y : V, DecidableEq (x ⟶ y)] [DecidablePred (· ∈ Q.nonprojective)]
  (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y)) (hc : ∀ x y a, c x y a = 1)
  (hdeck : ∀ Z, π.obj (((starTree L).zAct σ hσ s hσp).obj Z) = π.obj Z)

include hτ hc hdeck hσlev in
/-- Rotating a middle row `j` times. -/
theorem eps_rotate (m : ℕ) (j : ℕ) : ∀ (Z : (starTree L).ZVert)
    (P : Quiver.Path Z ((starTree L).rowEnd σ hσ s hσp Z)), P.length = m + 1 →
    (∀ v ∈ P.vertices, levZ h v = 1) →
    ∃ (Z' : (starTree L).ZVert) (P' : Quiver.Path Z' ((starTree L).rowEnd σ hσ s hσp Z')),
      Z'.t = Z.t + j ∧ P'.length = m + 1 ∧ (∀ v ∈ P'.vertices, levZ h v = 1) ∧
      (starTree L).rowZ hQ π c m P = (-1 : ℤ) ^ j • (starTree L).rowZ hQ π c m P' := by
  induction j with
  | zero => intro Z P hP hlev; exact ⟨Z, P, by simp, hP, hlev, by simp⟩
  | succ j ih =>
      intro Z P hP hlev
      obtain ⟨Z', P', ht, hP', hlev', hrow⟩ := ih Z P hP hlev
      obtain ⟨Y₁, a₁, B, hB, hPB⟩ := Quiver.Path.eq_toPath_comp_of_length_eq_succ P' (n := m) hP'
      have hrot := (starTree L).rowZ_rotate_path hQ π c σ hσ s hσp hdeck hτ hc (m := m) a₁.toPath B
        (by rw [Quiver.Path.length_toPath, hB]; omega)
      refine ⟨Y₁, B.comp ((starTree L).shiftPath σ hσ s hσp a₁.toPath), ?_, ?_, ?_, ?_⟩
      · have := a₁.down.2; push_cast; omega
      · rw [Quiver.Path.length_comp, hB]
        simp only [shiftPath, LinearPaths.length_mapPath, Quiver.Path.length_toPath]
      · intro v hv
        rw [Quiver.Path.vertices_comp] at hv
        rcases List.mem_append.1 hv with hv | hv
        · have hv2 : v ∈ (a₁.toPath.comp B).vertices :=
            Quiver.Path.mem_of_mem_right a₁.toPath B (List.mem_of_mem_dropLast hv)
          rw [← hPB] at hv2
          exact hlev' v hv2
        · obtain ⟨v', hv', hl⟩ := levZ_shift_mem h σ hσ s hσp hσlev _ hv
          have hv2 : v' ∈ (a₁.toPath.comp B).vertices := Quiver.Path.mem_of_mem_left a₁.toPath B hv'
          rw [← hPB] at hv2
          rw [hl]; exact hlev' v' hv2
      · rw [hrow, hPB, hrot, Quiver.Path.length_toPath, pow_one, smul_smul, pow_succ]

include hh hτ hc hdeck hσlev in
/-- **Middle words vanish** (`periodic-mesh-calculations.tex`): rotating
a word in the middle arrows `c₀` times gives its image under the deck generator
with the sign `(-1)^{c₀} = -1`, so twice its class is zero. -/
theorem eps_zero (ρ : StarV L ≃ StarV L)
    (hρ : ∀ a b, (starTree L).G.Adj (ρ a) (ρ b) ↔ (starTree L).G.Adj a b) (c0 : ℕ)
    (hρp : ∀ v, (starTree L).par (ρ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
    (hdeckg : ∀ Z, π.obj (((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z) = π.obj Z)
    (hodd : Odd c0) (hρlev : ∀ v, lev h (starDepth (ρ v)) = lev h (starDepth v))
    (h2 : (2 : k) ≠ 0) (m : ℕ) (Z : (starTree L).ZVert)
    (P : Quiver.Path Z ((starTree L).rowEnd σ hσ s hσp Z)) (hP : P.length = m + 1)
    (hlev : ∀ v ∈ P.vertices, levZ h v = 1) : (starTree L).rowZ hQ π c m P = 0 := by
  obtain ⟨Z', P', ht, hP', hlev', hrow⟩ := eps_rotate h σ hσ s hσp hσlev hQ π c hτ hc hdeck m c0
    Z P hP hlev
  -- `Z'` is the image of `Z` under the deck generator
  have hZ' : Z' = ((starTree L).zAct ρ hρ (c0 : ℤ) hρp).obj Z := by
    apply ZVert.ext
    · have hZ1 : levZ h Z = 1 := hlev Z (StarTrace.start_mem_vertices P)
      have hZ'1 : levZ h Z' = 1 := hlev' Z' (StarTrace.start_mem_vertices P')
      have hρ1 : lev h (starDepth (ρ Z.v)) = 1 := by rw [hρlev]; exact hZ1
      apply depth_injective
      change starDepth Z'.v = starDepth (ρ Z.v)
      refine mid_eq_of_par h hh hZ'1 hρ1 ?_
      have hp1 : ((Z'.t : ℤ) : ZMod 2) = ((starDepth Z'.v : ℕ) : ZMod 2) := Z'.ht
      have hp2 : ((starDepth (ρ Z.v) : ℕ) : ZMod 2) =
          ((starDepth Z.v : ℕ) : ZMod 2) + ((c0 : ℤ) : ZMod 2) := hρp Z.v
      have hp3 : ((Z.t : ℤ) : ZMod 2) = ((starDepth Z.v : ℕ) : ZMod 2) := Z.ht
      rw [← hp1, hp2, ← hp3, ht]; push_cast; ring
    · exact ht
  subst hZ'
  set gP := ((starTree L).zAct ρ hρ (c0 : ℤ) hρp).mapPath P
  have hsame : (starTree L).rowZ hQ π c m P' = (starTree L).rowZ hQ π c m gP := by
    apply (starTree L).rowZ_eq_of_pathStar
    apply (starTree L).pathStar_eq_of_forget
    apply dbl_mid_unique h hh
    · rw [LinearPaths.length_mapPath, LinearPaths.length_mapPath, LinearPaths.length_mapPath, hP',
        hP]
    · intro v hv
      rw [LinearPaths.vertices_mapPath, List.mem_map] at hv
      obtain ⟨v', hv', rfl⟩ := hv
      exact hlev' v' hv'
    · intro v hv
      rw [LinearPaths.vertices_mapPath, LinearPaths.vertices_mapPath, List.map_map,
        List.mem_map] at hv
      obtain ⟨v', hv', rfl⟩ := hv
      change lev h (starDepth (ρ v'.v)) = 1
      rw [hρlev]; exact hlev v' hv'
  have hg : (starTree L).rowZ hQ π c m gP = (starTree L).rowZ hQ π c m P :=
    (starTree L).rowZ_zAct hQ π c ρ hρ (c0 : ℤ) hρp hdeckg P
  rw [hsame, hg, hodd.neg_one_pow, neg_one_smul] at hrow
  have h0 : (starTree L).rowZ hQ π c m P + (starTree L).rowZ hQ π c m P = 0 := by
    nth_rewrite 1 [hrow]; exact neg_add_cancel _
  exact TraceAlg.two_cancel h2 _ h0

end Eps

end EvenA

end MultiplicativeBasisDeformations
