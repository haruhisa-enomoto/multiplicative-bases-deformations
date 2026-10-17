import MultiplicativeBasisDeformations.Foundations.StarGauge
import MultiplicativeBasisDeformations.Foundations.TwistedTrace

/-!
# Lemma A.1(1): signed coefficients on a periodic star model

`lem:periodic-scalar-gauges` (1) (`periodic-mesh-calculations.tex:257–300`).
Let `π : ℤΔ → Q` be a covering of a star model commuting with translation, whose
fibres are the orbits of `g (v, t) = (σ v, t + c₀)`, with `σ` fixing the centre.
Every coefficient system `c` on `Q` becomes the signed preprojective one after
rescaling arrows and entire mesh relations: the scales of `StarGauge` are
`g`-invariant, so they descend to `Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v' w

namespace StarGauge

open StarCorner OrbitReps OrientedTree

variable {t : ℕ} {L : Fin t → ℕ}

/-- The endpoint of an edge further from the centre. -/
def child (w w' : StarV L) : StarV L := if starDepth w < starDepth w' then w' else w

theorem child_comm {w w' : StarV L} (h : starAdj w w') : child w w' = child w' w := by
  rcases starAdj_depth h with h' | h' <;> simp [child, h'] <;> omega

theorem pa_succ (i : Fin t) (j : ℕ) (h : j + 1 ≤ L i) : pa i (j + 1) h = ch i j (by omega) := by
  simp [pa, ch]

/-- The two ways an edge of the star is seen from its endpoints. -/
theorem adj_cases {w w' : StarV L} (h : starAdj w' w) :
    (∃ (i : Fin t) (j : ℕ) (hj : j ≤ L i), w = ch i j hj ∧ w' = pa i j hj) ∨
      (∃ (i : Fin t) (j : ℕ) (hj : j ≤ L i), w = pa i j hj ∧ w' = ch i j hj) := by
  rcases w with _ | ⟨i, ⟨j, hj⟩⟩ <;> rcases w' with _ | ⟨i', ⟨j', hj'⟩⟩
  · exact (h : False).elim
  · simp only [starAdj] at h
    subst h
    exact Or.inr ⟨i', 0, Nat.zero_le _, by simp [pa], rfl⟩
  · simp only [starAdj] at h
    subst h
    exact Or.inl ⟨i, 0, Nat.zero_le _, rfl, by simp [pa]⟩
  · change i' = i ∧ (j = j' + 1 ∨ j' = j + 1) at h
    obtain ⟨hii, h⟩ := h
    subst hii
    rcases h with h | h
    · subst h
      exact Or.inl ⟨i', j' + 1, Nat.lt_succ_iff.1 hj, rfl, (pa_succ i' j' _).symm⟩
    · subst h
      exact Or.inr ⟨i', j + 1, Nat.lt_succ_iff.1 hj', (pa_succ i' j _).symm, rfl⟩

theorem child_ch_pa (i : Fin t) (j : ℕ) (hj : j ≤ L i) : child (ch i j hj) (pa i j hj) = ch i j hj := by
  unfold child pa
  split_ifs with h1 h2 <;> simp_all [starDepth, ch] <;> omega

theorem child_pa_ch (i : Fin t) (j : ℕ) (hj : j ≤ L i) : child (pa i j hj) (ch i j hj) = ch i j hj := by
  unfold child pa
  split_ifs with h1 h2 <;> simp_all [starDepth, ch]

/-! ### The coefficient function of `Q` -/

variable {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : (starTree L).ZVert ⥤q V)
  {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)

theorem c_congr {x x' : Q.nonprojective} {y y' : V} (hx : x = x') (hy : y = y') (a : y ⟶ x.1)
    (a' : y' ⟶ x'.1) : c x y a = c x' y' a' := by
  subst hx hy; rw [Subsingleton.elim a a']

theorem par_two (w : StarV L) (h : ℤ) (hh : ((h : ℤ) : ZMod 2) = (starTree L).par w) :
    ((h + 2 : ℤ) : ZMod 2) = (starTree L).par w := by
  push_cast; rw [hh, show (2 : ZMod 2) = 0 from rfl, add_zero]

theorem par_one {w w' : StarV L} (hadj : (starTree L).G.Adj w' w) (h : ℤ)
    (hh : ((h : ℤ) : ZMod 2) = (starTree L).par w) :
    ((h + 1 : ℤ) : ZMod 2) = (starTree L).par w' := by
  push_cast; rw [hh, (starTree L).par_adj hadj, add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl,
    add_zero]

open Classical in
/-- The coefficient of `Q` at `π (w, h + 2)` of the image of the arrow from
`(w', h + 1)`. -/
def Cf (w w' : StarV L) (h : ℤ) : kˣ :=
  if hv : (starTree L).G.Adj w' w ∧ ((h : ℤ) : ZMod 2) = (starTree L).par w then
    c ⟨π.obj ⟨w, h + 2, par_two w h hv.2⟩, hQ.mem_nonprojective _⟩
      (π.obj ⟨w', h + 1, par_one hv.1 h hv.2⟩) (π.map ⟨⟨hv.1, by ring⟩⟩)
  else 1

theorem pullCoeff_eq (X : (starTree L).zQuiver.nonprojective) (Y : (starTree L).ZVert)
    (A : Y ⟶ X.1) :
    (starTree L).pullCoeff hQ π c X Y A = Cf hQ π c X.1.v Y.v (X.1.t - 2) := by
  obtain ⟨⟨w, s, hs⟩, hX⟩ := X
  obtain ⟨w', s', hs'⟩ := Y
  obtain ⟨hadj, ht⟩ := A.down
  change s = s' + 1 at ht
  subst ht
  have hpar : (((s' + 1 - 2 : ℤ)) : ZMod 2) = (starTree L).par w := by
    rw [← hs]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, sub_zero]
  unfold Cf
  rw [dif_pos ⟨hadj, hpar⟩]
  exact c_congr c (Subtype.ext (congrArg π.obj (by ext <;> simp <;> ring)))
    (congrArg π.obj (by ext <;> simp <;> ring)) _ _

variable (σ : StarV L ≃ StarV L) (hσ : ∀ a b, (starTree L).G.Adj (σ a) (σ b) ↔ (starTree L).G.Adj a b)
  (c0 : ℕ) (hσp : ∀ v, (starTree L).par (σ v) = (starTree L).par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj (((starTree L).zAct σ hσ (c0 : ℤ) hσp).obj Z) = π.obj Z)

include hdeck in
theorem Cf_inv (w w' : StarV L) (h : ℤ) :
    Cf hQ π c (σ w) (σ w') (h + c0) = Cf hQ π c w w' h := by
  unfold Cf
  by_cases hv : (starTree L).G.Adj w' w ∧ ((h : ℤ) : ZMod 2) = (starTree L).par w
  · have hv' : (starTree L).G.Adj (σ w') (σ w) ∧
        ((h + c0 : ℤ) : ZMod 2) = (starTree L).par (σ w) := by
      refine ⟨(hσ _ _).2 hv.1, ?_⟩
      rw [hσp, ← hv.2]; push_cast; ring
    rw [dif_pos hv, dif_pos hv']
    refine c_congr c (Subtype.ext ?_) ?_ _ _
    · refine (congrArg π.obj ?_).trans (hdeck ⟨w, h + 2, par_two w h hv.2⟩)
      ext <;> simp [OrientedTree.zAct] <;> ring
    · refine (congrArg π.obj ?_).trans (hdeck ⟨w', h + 1, par_one hv.1 h hv.2⟩)
      ext <;> simp [OrientedTree.zAct] <;> ring
  · have hv' : ¬ ((starTree L).G.Adj (σ w') (σ w) ∧
        ((h + c0 : ℤ) : ZMod 2) = (starTree L).par (σ w)) := by
      rintro ⟨h1, h2⟩
      refine hv ⟨(hσ _ _).1 h1, ?_⟩
      rw [hσp] at h2; push_cast at h2
      exact add_right_cancel h2
    rw [dif_neg hv, dif_neg hv']

theorem par_ch (i : Fin t) (j : ℕ) (hj : j ≤ L i) :
    (starTree L).par (ch i j hj) = ((j + 1 : ℕ) : ZMod 2) := rfl

theorem par_pa (i : Fin t) (j : ℕ) (hj : j ≤ L i) :
    (starTree L).par (pa i j hj) = ((j : ℕ) : ZMod 2) := by
  unfold pa
  split_ifs with h
  · subst h; rfl
  · change (((j - 1 + 1 : ℕ) : ℕ) : ZMod 2) = _
    rw [Nat.sub_add_cancel (by omega)]

theorem ne_succ_zmod (j : ℕ) : ((j : ℕ) : ZMod 2) ≠ ((j + 1 : ℕ) : ZMod 2) := by
  push_cast; intro h
  have := congrArg (· - (j : ZMod 2)) h
  simp at this

variable (θ : Equiv.Perm (Fin t)) (hL : ∀ i, L (θ i) = L i) (hσo : σ none = none)
  (hθ : ∀ i j (h : j ≤ L i), σ (ch i j h) = ch (θ i) j (by rw [hL]; exact h))

include hσo hθ in
theorem depth_σ (v : StarV L) : starDepth (σ v) = starDepth v := by
  rcases v with _ | ⟨i, ⟨j, hj⟩⟩
  · rw [hσo]
  · have := hθ i j (Nat.lt_succ_iff.1 hj)
    change starDepth (σ (ch i j (Nat.lt_succ_iff.1 hj))) = _
    rw [this]; rfl

include hσ hσo hθ in
theorem sgn_σ (w w' : StarV L) : (starTree L).sgn k (σ w) (σ w') = (starTree L).sgn k w w' := by
  unfold OrientedTree.sgn
  have e : (starTree L).orient (σ w) (σ w') ↔ (starTree L).orient w w' := by
    change starOrient (σ w) (σ w') ↔ starOrient w w'
    unfold starOrient
    rw [depth_σ σ θ hL hσo hθ, depth_σ σ θ hL hσo hθ]
    exact and_congr_left' (hσ w w')
  by_cases h : (starTree L).orient w w'
  · rw [if_pos h, if_pos (e.2 h)]
  · rw [if_neg h, if_neg (fun h' ↦ h (e.1 h'))]

/-- The relation scales and arrow scales on `ℤΔ`. -/
abbrev Nz := Nf (Cf hQ π c) (fun w w' ↦ (starTree L).sgn k w w') θ c0
abbrev Mz := Mf (Cf hQ π c) (fun w w' ↦ (starTree L).sgn k w w') θ c0

include hσ hdeck hσo hθ in
/-- **The gauge equations on `ℤΔ`**. -/
theorem zEq (hc0 : 0 < c0) (hc0e : Even c0) (X : (starTree L).zQuiver.nonprojective)
    (Y : (starTree L).ZVert) (A : Y ⟶ X.1) :
    (starTree L).zSigned k X Y A =
      Nz hQ π c c0 θ X.1.v X.1.t * (starTree L).pullCoeff hQ π c X Y A *
        Mz hQ π c c0 θ (child X.1.v Y.v) (X.1.t - 2) * Mz hQ π c c0 θ (child Y.v X.1.v) Y.t := by
  rw [pullCoeff_eq]
  obtain ⟨⟨w, s, hs⟩, hX⟩ := X
  obtain ⟨w', s', hs'⟩ := Y
  obtain ⟨hadj, ht⟩ := A.down
  change s = s' + 1 at ht
  subst ht
  change (starTree L).sgn k w w' = Nz hQ π c c0 θ w (s' + 1) * Cf hQ π c w w' (s' + 1 - 2) *
    Mz hQ π c c0 θ (child w w') (s' + 1 - 2) * Mz hQ π c c0 θ (child w' w) s'
  have hpar : ((s' + 1 - 2 : ℤ) : ZMod 2) = (starTree L).par w := by
    rw [← hs]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, sub_zero]
  have hCinv := Cf_inv hQ π c σ hσ c0 hσp hdeck
  have hsg := sgn_σ (k := k) σ hσ θ hL hσo hθ
  have hE := edge_eq (Cf hQ π c) (fun w w' ↦ (starTree L).sgn k w w') θ hL σ hσo hθ c0 hCinv
    hsg hc0 hc0e
  set u := s' + 1 - 2 with hu
  rw [show s' = u + 1 by omega, show u + 1 + 1 = u + 2 by ring]
  rcases adj_cases hadj with ⟨i, j, hj, rfl, rfl⟩ | ⟨i, j, hj, rfl, rfl⟩
  · have e := hE i j hj u
    rw [hpar, par_ch, if_pos rfl] at e
    simp only [lineS, hpar, par_ch, if_true] at e
    rw [child_ch_pa, child_pa_ch]
    rw [eq_mul_inv_iff_mul_eq] at e
    rw [← e]; simp only [Mz, Nz]; ac_rfl
  · have e := hE i j hj u
    rw [hpar, par_pa, if_neg (ne_succ_zmod j)] at e
    simp only [lineS, hpar, par_pa, if_neg (ne_succ_zmod j)] at e
    rw [child_pa_ch, child_ch_pa]
    rw [mul_one, eq_mul_inv_iff_mul_eq] at e
    rw [← e]; simp only [Mz, Nz]; ac_rfl

/-! ### Descent to `Q` -/

/-- The deck transformation on vertices. -/
abbrev gZ : (starTree L).ZVert → (starTree L).ZVert := ((starTree L).zAct σ hσ (c0 : ℤ) hσp).obj

theorem gZ_iter (n : ℕ) (X : (starTree L).ZVert) :
    ((gZ σ hσ c0 hσp)^[n] X).v = (σ ^ n) X.v ∧ ((gZ σ hσ c0 hσp)^[n] X).t = X.t + n * c0 := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      obtain ⟨h1, h2⟩ := ih X
      refine ⟨?_, ?_⟩
      · change σ ((gZ σ hσ c0 hσp)^[n] X).v = σ ((σ ^ n) X.v); rw [h1]
      · change ((gZ σ hσ c0 hσp)^[n] X).t + c0 = _; rw [h2]; push_cast; ring

theorem gZ_arrow (n : ℕ) {X Y : (starTree L).ZVert} (A : Nonempty (Y ⟶ X)) :
    Nonempty ((gZ σ hσ c0 hσp)^[n] Y ⟶ (gZ σ hσ c0 hσp)^[n] X) := by
  induction n with
  | zero => exact A
  | succ n ih =>
      obtain ⟨B⟩ := ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ⟨((starTree L).zAct σ hσ (c0 : ℤ) hσp).map B⟩

include hdeck in
theorem π_gZ_iter (n : ℕ) (X : (starTree L).ZVert) :
    π.obj ((gZ σ hσ c0 hσp)^[n] X) = π.obj X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hdeck, ih]

include hσo hθ in
theorem child_σ (w w' : StarV L) : child (σ w) (σ w') = σ (child w w') := by
  unfold child
  rw [depth_σ σ θ hL hσo hθ, depth_σ σ θ hL hσo hθ]
  split_ifs <;> rfl

/-- The relation scale at a vertex of `ℤΔ`. -/
def Ez (X : (starTree L).ZVert) : kˣ := Nz hQ π c c0 θ X.v X.t

/-- The arrow scale of the arrow `Y → X` of `ℤΔ`. -/
def Fz (Y X : (starTree L).ZVert) : kˣ := Mz hQ π c c0 θ (child Y.v X.v) Y.t

include hσ hdeck hσo hθ in
theorem Ez_iter (hc0 : 0 < c0) (hc0e : Even c0) (n : ℕ) (X : (starTree L).ZVert) :
    Ez hQ π c c0 θ ((gZ σ hσ c0 hσp)^[n] X) = Ez hQ π c c0 θ X := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ← ih]
      exact Nf_inv (Cf hQ π c) (fun w w' ↦ (starTree L).sgn k w w') θ hL σ hσo hθ c0
        (Cf_inv hQ π c σ hσ c0 hσp hdeck) hc0 hc0e _ _

include hσ hdeck hσo hθ in
theorem Fz_iter (hc0 : 0 < c0) (hc0e : Even c0) (n : ℕ) (Y X : (starTree L).ZVert) :
    Fz hQ π c c0 θ ((gZ σ hσ c0 hσp)^[n] Y) ((gZ σ hσ c0 hσp)^[n] X) = Fz hQ π c c0 θ Y X := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      unfold Fz
      change Mz hQ π c c0 θ (child (σ _) (σ _)) (_ + c0) = _
      rw [child_σ σ θ hL hσo hθ]
      exact Mf_inv (Cf hQ π c) (fun w w' ↦ (starTree L).sgn k w w') θ hL σ hσo hθ c0
        (Cf_inv hQ π c σ hσ c0 hσp hdeck) hc0 hc0e _ _

variable (hπ : π.IsCovering)

include hπ in
/-- Arrows into a vertex of `ℤΔ` are determined by the image of their source. -/
theorem lift_unique (X : (starTree L).ZVert) {Y₁ Y₂ : (starTree L).ZVert} (A₁ : Y₁ ⟶ X)
    (A₂ : Y₂ ⟶ X) (h : π.obj Y₁ = π.obj Y₂) : Y₁ = Y₂ := by
  have := (hπ.costar_bijective X).1 (a₁ := ⟨Y₁, A₁⟩) (a₂ := ⟨Y₂, A₂⟩)
    (Sigma.ext h (Subsingleton.helim (congrArg (· ⟶ π.obj X) h) _ _))
  exact congrArg Sigma.fst this

include hπ in
theorem lift_exists (X : (starTree L).ZVert) {y : V} (a : y ⟶ π.obj X) :
    ∃ Y, Nonempty (Y ⟶ X) ∧ π.obj Y = y := by
  obtain ⟨⟨Y, A⟩, hYA⟩ := (hπ.costar_bijective X).2 ⟨y, a⟩
  exact ⟨Y, ⟨A⟩, congrArg Sigma.fst hYA⟩

variable (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (hfib : ∀ X Y : (starTree L).ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ σ hσ c0 hσp)^[n] X ∨ X = (gZ σ hσ c0 hσp)^[n] Y)

/-- The relation scales on `Q`. -/
def ηQ (x : Q.nonprojective) : kˣ := Ez hQ π c c0 θ (hsurj x.1).choose

/-- The arrow scales on `Q`. -/
def μQ {y x : V} (a : y ⟶ x) : kˣ :=
  Fz hQ π c c0 θ (lift_exists π hπ (hsurj x).choose
    (Quiver.Hom.cast rfl (hsurj x).choose_spec.symm a)).choose (hsurj x).choose

include hσ hdeck hσo hθ hfib in
theorem ηQ_eq (hc0 : 0 < c0) (hc0e : Even c0) (X : (starTree L).ZVert) :
    ηQ hQ π c c0 θ hsurj ⟨π.obj X, hQ.mem_nonprojective _⟩ = Ez hQ π c c0 θ X := by
  unfold ηQ
  set X' := (hsurj (π.obj X)).choose
  have hX' : π.obj X' = π.obj X := (hsurj _).choose_spec
  obtain ⟨n, h | h⟩ := hfib X' X hX'
  · rw [h, Ez_iter hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hc0 hc0e]
  · rw [h, Ez_iter hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hc0 hc0e]

include hσ hdeck hσo hθ hfib hπ in
theorem Fz_fibre (hc0 : 0 < c0) (hc0e : Even c0) {X X' Y Y' : (starTree L).ZVert}
    (hX : π.obj X' = π.obj X) (hY : π.obj Y' = π.obj Y) (A : Y ⟶ X) (A' : Y' ⟶ X') :
    Fz hQ π c c0 θ Y' X' = Fz hQ π c c0 θ Y X := by
  obtain ⟨n, h | h⟩ := hfib X X' hX.symm
  · obtain ⟨B⟩ := gZ_arrow σ hσ c0 hσp n ⟨A⟩
    rw [← h] at B
    have hY' : Y' = (gZ σ hσ c0 hσp)^[n] Y :=
      lift_unique π hπ X' A' B (by rw [hY, π_gZ_iter π σ hσ c0 hσp hdeck])
    rw [hY', h, Fz_iter hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hc0 hc0e]
  · obtain ⟨B⟩ := gZ_arrow σ hσ c0 hσp n ⟨A'⟩
    rw [← h] at B
    have hY' : Y = (gZ σ hσ c0 hσp)^[n] Y' :=
      lift_unique π hπ X A B (by rw [π_gZ_iter π σ hσ c0 hσp hdeck, hY])
    rw [hY', h, Fz_iter hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hc0 hc0e]

include hσ hdeck hσo hθ hfib in
theorem μQ_eq (hc0 : 0 < c0) (hc0e : Even c0) {Y X : (starTree L).ZVert} (A : Y ⟶ X) :
    μQ hQ π c c0 θ hπ hsurj (π.map A) = Fz hQ π c c0 θ Y X := by
  unfold μQ
  have hX' := (hsurj (π.obj X)).choose_spec
  obtain ⟨⟨A'⟩, hY'⟩ := (lift_exists π hπ (hsurj (π.obj X)).choose
    (Quiver.Hom.cast rfl hX'.symm (π.map A))).choose_spec
  exact Fz_fibre hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hπ hfib hc0 hc0e hX' hY' A A'

theorem μQ_congr {y x y' x' : V} (a : y ⟶ x) (a' : y' ⟶ x') (hy : y = y') (hx : x = x') :
    μQ hQ π c c0 θ hπ hsurj a = μQ hQ π c c0 θ hπ hsurj a' := by
  subst hy hx; rw [Subsingleton.elim a a']

variable (hτ : ∀ Y, π.obj ((starTree L).ztau Y) = hQ.tauE (π.obj Y))

include hσ hdeck hσo hθ hfib hτ hπ hsurj in
/-- **Lemma A.1(1)**: rescaling arrows and entire mesh relations of `Q` turns
every coefficient system into the signed preprojective coefficients. -/
theorem exists_signed_gauge (hc0 : 0 < c0) (hc0e : Even c0) :
    ∃ (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ),
      (starTree L).pullCoeff hQ π (fun x y a ↦ η x * c x y a * μ (Q.mate x y a) * μ a) =
        (starTree L).zSigned k := by
  refine ⟨fun a ↦ μQ hQ π c c0 θ hπ hsurj a, ηQ hQ π c c0 θ hsurj, ?_⟩
  funext X Y A
  rw [zEq hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hc0 hc0e X Y A]
  change ηQ hQ π c c0 θ hsurj ⟨π.obj X.1, hQ.mem_nonprojective _⟩ * _ *
    μQ hQ π c c0 θ hπ hsurj _ * μQ hQ π c c0 θ hπ hsurj (π.map A) = _
  rw [ηQ_eq hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hsurj hfib hc0 hc0e,
    μQ_eq hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hπ hsurj hfib hc0 hc0e A,
    μQ_congr hQ π c c0 θ hπ hsurj _ (π.map ((starTree L).zQuiver.mate X Y A)) (hτ X.1).symm rfl,
    μQ_eq hQ π c σ hσ c0 hσp hdeck θ hL hσo hθ hπ hsurj hfib hc0 hc0e]
  rfl

end StarGauge

end MultiplicativeBasisDeformations
