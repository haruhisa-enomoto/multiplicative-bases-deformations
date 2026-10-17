import MultiplicativeBasisDeformations.Foundations.PeriodicGauge
import MultiplicativeBasisDeformations.Foundations.OrbitReps
import MultiplicativeBasisDeformations.Foundations.TwistedTrace

/-!
# Lemma A.1(1) for an arbitrary rooted tree

`lem:periodic-scalar-gauges` (1), `periodic-mesh-calculations.tex`: "Let
`Q = ℤΔ/⟨τ^s ρ⟩`, where `Δ` is a finite tree oriented away from a root fixed by `ρ`. Every
nonzero coefficient system `c` can be changed to the signed preprojective coefficients."
Proof: "Label the arrows over a parent-child edge orbit […] Such labels can be assigned
recursively down the rooted orbit tree. […] Dividing the two equations gives a recurrence for
`μ_a`. It closes around the cycle exactly when [a product of the `η`] equals a prescribed number.
Choose the root product freely and assign the child products down the tree. Realize each product
by one factor, setting the other factors to one."

The rooted tree is given by a parent map `pa` reaching the root `o` (`Rooted`), and the twist
`σ` fixes `o` and commutes with `pa`. For each vertex `v ≠ o` the edge line `{v, pa v}` is solved
on the representative `rep v` of the `σ`-orbit of `v`, with period `per v · c₀`, from the relation
scales of its parent (`step`, `exists_periodic_line_vertex`), and transported along the orbit; the
recursion runs on the depth (`NM`). The solution is `g`-invariant and solves every edge equation
(`main`). The star version is `StarGauge.exists_signed_gauge`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u

namespace RootedGauge

open OrbitReps

/-- **A rooted tree with a twist**: a parent map reaching the root `o`, and a permutation `σ`
fixing the root and commuting with the parent map. -/
structure Rooted (D : Type*) where
  o : D
  pa : D → D
  root : ∀ v, ∃ n, pa^[n] v = o
  σ : Equiv.Perm D
  σ_o : σ o = o
  σ_pa : ∀ v, σ (pa v) = pa (σ v)

namespace Rooted

variable {k : Type u} [CommRing k] {D : Type*} [Fintype D] [DecidableEq D] [LinearOrder D]
  (R : Rooted D)

/-- The depth: the number of parent steps to the root. -/
def dep (v : D) : ℕ := Nat.find (R.root v)

theorem iter_σ (n : ℕ) (v : D) : R.pa^[n] (R.σ v) = R.σ (R.pa^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← R.σ_pa, ih]

theorem σ_eq_o_iff (v : D) : R.σ v = R.o ↔ v = R.o := by
  constructor
  · intro h; apply R.σ.injective; rw [h, R.σ_o]
  · rintro rfl; exact R.σ_o

theorem dep_σ (v : D) : R.dep (R.σ v) = R.dep v := by
  have e : ∀ n, R.pa^[n] (R.σ v) = R.o ↔ R.pa^[n] v = R.o := fun n ↦ by
    rw [iter_σ, σ_eq_o_iff]
  exact le_antisymm (Nat.find_min' _ ((e _).2 (Nat.find_spec (R.root v))))
    (Nat.find_min' _ ((e _).1 (Nat.find_spec (R.root (R.σ v)))))

theorem dep_pa (v : D) (hv : v ≠ R.o) : R.dep (R.pa v) < R.dep v := by
  have hspec : R.pa^[R.dep v] v = R.o := Nat.find_spec (R.root v)
  have h0 : R.dep v ≠ 0 := fun h ↦ hv (by rw [h] at hspec; exact hspec)
  have : R.pa^[R.dep v - 1] (R.pa v) = R.o := by
    rw [← Function.iterate_succ_apply, show (R.dep v - 1).succ = R.dep v by omega, hspec]
  exact lt_of_le_of_lt (Nat.find_min' _ this) (by omega)

theorem pow_σ_o (n : ℕ) : (R.σ ^ n) R.o = R.o := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, R.σ_o]

theorem pow_σ_pa (n : ℕ) (v : D) : (R.σ ^ n) (R.pa v) = R.pa ((R.σ ^ n) v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih, R.σ_pa]

theorem dep_pow (n : ℕ) (v : D) : R.dep ((R.σ ^ n) v) = R.dep v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, dep_σ, ih]

theorem rep_ne (v : D) (hv : v ≠ R.o) : rep R.σ v ≠ R.o := by
  intro h
  apply hv
  rw [← pow_ord R.σ v, h, pow_σ_o]

theorem dep_rep (v : D) : R.dep (rep R.σ v) = R.dep v := by
  conv_rhs => rw [← pow_ord R.σ v]
  rw [dep_pow]

/-! ### The edge lines -/

variable (Cf : D → D → ℤ → kˣ) (sg : D → D → kˣ) (pr : D → ZMod 2) (c0 : ℕ)

/-- The prescribed products on the edge line `{v, pa v}`, given the relation scales `Np` of the
parent. -/
def lineS (v : D) (Np : ℤ → kˣ) (s : ℤ) : kˣ :=
  if (s : ZMod 2) = pr v then sg v (R.pa v) * (Cf v (R.pa v) s)⁻¹
  else sg (R.pa v) v * (Np (s + 2) * Cf (R.pa v) v s)⁻¹

open Classical in
/-- One edge: the child's relation scales and the edge's arrow scales. -/
def step (P : ℕ) (v : D) (Np : ℤ → kˣ) : (ℤ → kˣ) × (ℤ → kˣ) :=
  if hP : 0 < P ∧ Even P ∧ ∀ s, R.lineS Cf sg pr v Np (s + P) = R.lineS Cf sg pr v Np s then
    ((exists_periodic_line_vertex P hP.1 hP.2.1 _ hP.2.2 (pr v)).choose,
      (exists_periodic_line_vertex P hP.1 hP.2.1 _ hP.2.2 (pr v)).choose_spec.choose)
  else (fun _ ↦ 1, fun _ ↦ 1)

theorem step_spec (P : ℕ) (v : D) (Np : ℤ → kˣ) (hP : 0 < P) (hPe : Even P)
    (hS : ∀ s, R.lineS Cf sg pr v Np (s + P) = R.lineS Cf sg pr v Np s) :
    (∀ s, (R.step Cf sg pr P v Np).1 (s + P) = (R.step Cf sg pr P v Np).1 s) ∧
    (∀ s, (R.step Cf sg pr P v Np).2 (s + P) = (R.step Cf sg pr P v Np).2 s) ∧
    ∀ s, (R.step Cf sg pr P v Np).2 s * (R.step Cf sg pr P v Np).2 (s + 1) *
      (if (s : ZMod 2) = pr v then (R.step Cf sg pr P v Np).1 (s + 2) else 1) =
        R.lineS Cf sg pr v Np s := by
  unfold step
  rw [dif_pos ⟨hP, hPe, hS⟩]
  exact (exists_periodic_line_vertex P hP hPe _ hS _).choose_spec.choose_spec

/-- **The scales**, recursively down the tree: at `v ≠ o`, the relation scales of `v` and the
arrow scales of the edge `{v, pa v}`, solved on the orbit representative and transported. -/
def NM (v : D) : (ℤ → kˣ) × (ℤ → kˣ) :=
  if hv : v = R.o then (fun _ ↦ 1, fun _ ↦ 1) else
    (fun s ↦ (R.step Cf sg pr (per R.σ v * c0) (rep R.σ v)
        (NM (R.pa (rep R.σ v))).1).1 (s - ord R.σ v * c0),
      fun s ↦ (R.step Cf sg pr (per R.σ v * c0) (rep R.σ v)
        (NM (R.pa (rep R.σ v))).1).2 (s - ord R.σ v * c0))
termination_by R.dep v
decreasing_by
  all_goals (rw [← R.dep_rep v]; exact R.dep_pa _ (R.rep_ne v hv))

/-- The relation scales. -/
def N (v : D) : ℤ → kˣ := (R.NM Cf sg pr c0 v).1

/-- The arrow scales of the edge `{v, pa v}`. -/
def M (v : D) : ℤ → kˣ := (R.NM Cf sg pr c0 v).2

theorem N_o : R.N Cf sg pr c0 R.o = fun _ ↦ 1 := by
  unfold N; rw [NM, dif_pos rfl]

theorem M_o : R.M Cf sg pr c0 R.o = fun _ ↦ 1 := by
  unfold M; rw [NM, dif_pos rfl]

/-- The step on the representative of `v`. -/
abbrev B (v : D) : (ℤ → kˣ) × (ℤ → kˣ) :=
  R.step Cf sg pr (per R.σ v * c0) (rep R.σ v) (R.N Cf sg pr c0 (R.pa (rep R.σ v)))

theorem N_ne (v : D) (hv : v ≠ R.o) (s : ℤ) :
    R.N Cf sg pr c0 v s = (R.B Cf sg pr c0 v).1 (s - ord R.σ v * c0) := by
  unfold N; rw [NM, dif_neg hv]; rfl

theorem M_ne (v : D) (hv : v ≠ R.o) (s : ℤ) :
    R.M Cf sg pr c0 v s = (R.B Cf sg pr c0 v).2 (s - ord R.σ v * c0) := by
  unfold M; rw [NM, dif_neg hv]; rfl

/-! ### Invariance and the edge equations -/

variable (hc0 : 0 < c0) (hc0e : Even c0)
  (hCinv : ∀ w w' s, Cf (R.σ w) (R.σ w') (s + c0) = Cf w w' s)
  (hsg : ∀ w w', sg (R.σ w) (R.σ w') = sg w w') (hpr : ∀ w, pr (R.σ w) = pr w)

include hCinv in
theorem Cf_pow (n : ℕ) (w w' : D) (s : ℤ) :
    Cf ((R.σ ^ n) w) ((R.σ ^ n) w') (s + n * c0) = Cf w w' s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        show s + ((n + 1 : ℕ) : ℤ) * c0 = (s + n * c0) + c0 by push_cast; ring, hCinv, ih]

include hsg in
theorem sg_pow (n : ℕ) (w w' : D) : sg ((R.σ ^ n) w) ((R.σ ^ n) w') = sg w w' := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsg, ih]

include hpr in
theorem pr_pow (n : ℕ) (w : D) : pr ((R.σ ^ n) w) = pr w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hpr, ih]

theorem par_even (hc0e : Even c0) (s : ℤ) (n : ℤ) : ((s + n * c0 : ℤ) : ZMod 2) = (s : ZMod 2) := by
  obtain ⟨r, hr⟩ := hc0e
  push_cast; rw [hr]; push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, mul_zero, add_zero]

/-- One-step invariance iterates. -/
theorem N_pow (x : D) (hx : ∀ j : ℕ, ∀ s, R.N Cf sg pr c0 (R.σ ((R.σ ^ j) x)) (s + c0) =
    R.N Cf sg pr c0 ((R.σ ^ j) x) s) (n : ℕ) (s : ℤ) :
    R.N Cf sg pr c0 ((R.σ ^ n) x) (s + n * c0) = R.N Cf sg pr c0 x s := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        show s + ((n + 1 : ℕ) : ℤ) * c0 = (s + n * c0) + c0 by push_cast; ring, hx, ih]

include hc0 hc0e hCinv hsg hpr in
/-- **The scales are `g`-invariant and solve the edge equations**, by induction on the depth. -/
theorem main : ∀ d, ∀ v, R.dep v = d →
    (∀ s, R.N Cf sg pr c0 (R.σ v) (s + c0) = R.N Cf sg pr c0 v s ∧
      R.M Cf sg pr c0 (R.σ v) (s + c0) = R.M Cf sg pr c0 v s) ∧
    (v ≠ R.o → ∀ s, R.M Cf sg pr c0 v s * R.M Cf sg pr c0 v (s + 1) *
      (if (s : ZMod 2) = pr v then R.N Cf sg pr c0 v (s + 2) else 1) =
        R.lineS Cf sg pr v (R.N Cf sg pr c0 (R.pa v)) s) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro v hvd
  by_cases hv : v = R.o
  · subst hv
    refine ⟨fun s ↦ ?_, fun h ↦ absurd rfl h⟩
    rw [R.σ_o, N_o, M_o]; exact ⟨rfl, rfl⟩
  set r := rep R.σ v with hr
  set n := ord R.σ v
  set P := per R.σ v * c0 with hP
  have hrv : (R.σ ^ n) r = v := pow_ord R.σ v
  have hr0 : r ≠ R.o := R.rep_ne v hv
  -- the parent of the representative is shallower
  have hlt : ∀ j : ℕ, R.dep ((R.σ ^ j) (R.pa r)) < d := fun j ↦ by
    rw [dep_pow, ← hvd, ← R.dep_rep v]; exact R.dep_pa r hr0
  have hinvP : ∀ j : ℕ, ∀ s, R.N Cf sg pr c0 (R.σ ((R.σ ^ j) (R.pa r))) (s + c0) =
      R.N Cf sg pr c0 ((R.σ ^ j) (R.pa r)) s := fun j s ↦
    ((ih _ (hlt j) _ rfl).1 s).1
  have hPpos : 0 < P := Nat.mul_pos (per_pos R.σ v) hc0
  have hPe : Even P := hc0e.mul_left _
  have hfix : (R.σ ^ per R.σ v) r = r := pow_per R.σ v
  have hfixp : (R.σ ^ per R.σ v) (R.pa r) = R.pa r := by rw [pow_σ_pa, hfix]
  -- the edge line of the representative is `P`-periodic
  have hS : ∀ s, R.lineS Cf sg pr r (R.N Cf sg pr c0 (R.pa r)) (s + P) =
      R.lineS Cf sg pr r (R.N Cf sg pr c0 (R.pa r)) s := by
    intro s
    have e1 := R.Cf_pow Cf c0 hCinv (per R.σ v) r (R.pa r) s
    have e2 := R.Cf_pow Cf c0 hCinv (per R.σ v) (R.pa r) r s
    have e3 := R.N_pow Cf sg pr c0 (R.pa r) hinvP (per R.σ v) (s + 2)
    rw [hfix, hfixp] at e1 e2
    rw [hfixp] at e3
    have hpar : ((s + P : ℤ) : ZMod 2) = (s : ZMod 2) := by
      have := par_even c0 hc0e s (per R.σ v); rw [← this, hP]; push_cast; ring_nf
    unfold lineS
    rw [hpar, show s + (P : ℤ) = s + (per R.σ v : ℕ) * c0 by rw [hP]; push_cast; ring, e1, e2,
      show s + (per R.σ v : ℕ) * c0 + 2 = s + 2 + (per R.σ v : ℕ) * c0 by ring, e3]
  obtain ⟨hB1, hB2, hBeq⟩ := R.step_spec Cf sg pr P r _ hPpos hPe hS
  refine ⟨fun s ↦ ?_, fun _ s ↦ ?_⟩
  · -- invariance: `σ v` has the same representative and period
    have hσv : R.σ v ≠ R.o := fun h ↦ hv ((R.σ_eq_o_iff v).1 h)
    have hB : R.B Cf sg pr c0 (R.σ v) = R.B Cf sg pr c0 v := by
      simp only [B, rep_apply, per_apply]
    obtain ⟨q, hq⟩ := ord_apply R.σ v
    have hshift : s + c0 - (ord R.σ (R.σ v) : ℤ) * c0 = (s - n * c0) + q * (P : ℕ) := by
      rw [hP]; push_cast; linear_combination (c0 : ℤ) * hq
    rw [N_ne _ _ _ _ _ _ hσv, N_ne _ _ _ _ _ _ hv, M_ne _ _ _ _ _ _ hσv, M_ne _ _ _ _ _ _ hv, hB,
      hshift]
    have hp1 : Function.Periodic (R.B Cf sg pr c0 v).1 (P : ℤ) := fun s ↦ hB1 s
    have hp2 : Function.Periodic (R.B Cf sg pr c0 v).2 (P : ℤ) := fun s ↦ hB2 s
    exact ⟨hp1.int_mul q _, hp2.int_mul q _⟩
  · -- the edge equation, transported from the representative
    have hpar : ((s - n * c0 : ℤ) : ZMod 2) = (s : ZMod 2) := by
      have := par_even c0 hc0e s (-(n : ℤ)); rw [← this]; ring_nf
    have hprv : pr r = pr v := by rw [← hrv, pr_pow R pr hpr]
    have hs := hBeq (s - n * c0)
    rw [hpar, hprv] at hs
    rw [M_ne _ _ _ _ _ _ hv, M_ne _ _ _ _ _ _ hv, N_ne _ _ _ _ _ _ hv,
      show s + 1 - n * c0 = s - n * c0 + 1 by ring, show s + 2 - n * c0 = s - n * c0 + 2 by ring]
    rw [hs]
    have hpav : (R.σ ^ n) (R.pa r) = R.pa v := by rw [pow_σ_pa, hrv]
    unfold lineS
    rw [hpar, hprv, ← R.Cf_pow Cf c0 hCinv n r (R.pa r) (s - n * c0),
      ← R.Cf_pow Cf c0 hCinv n (R.pa r) r (s - n * c0),
      ← R.sg_pow sg hsg n r (R.pa r), ← R.sg_pow sg hsg n (R.pa r) r,
      hrv, hpav, show s - n * c0 + n * c0 = s by ring,
      ← R.N_pow Cf sg pr c0 (R.pa r) hinvP n (s - n * c0 + 2), hpav,
      show s - n * c0 + 2 + n * c0 = s + 2 by ring]

end Rooted

/-! ### The coefficients of `Q` along the covering -/

section Tree

open CategoryTheory OrientedTree

universe v' w

variable {D : Type*} [Fintype D] [DecidableEq D] (T : OrientedTree D) [DecidableRel T.orient]
  {V : Type v'} [Quiver.{w} V] [∀ x y : V, Subsingleton (x ⟶ y)] {Q : TranslationQuiver V}
  (hQ : Q.IsStable) (π : T.ZVert ⥤q V)
  {k : Type u} [CommRing k] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] (c : MeshCoefficients k Q)

theorem c_congr {x x' : Q.nonprojective} {y y' : V} (hx : x = x') (hy : y = y') (a : y ⟶ x.1)
    (a' : y' ⟶ x'.1) : c x y a = c x' y' a' := by
  subst hx hy; rw [Subsingleton.elim a a']

theorem par_two (w : D) (h : ℤ) (hh : ((h : ℤ) : ZMod 2) = T.par w) :
    ((h + 2 : ℤ) : ZMod 2) = T.par w := by
  push_cast; rw [hh, show (2 : ZMod 2) = 0 from rfl, add_zero]

theorem par_one {w w' : D} (hadj : T.G.Adj w' w) (h : ℤ) (hh : ((h : ℤ) : ZMod 2) = T.par w) :
    ((h + 1 : ℤ) : ZMod 2) = T.par w' := by
  push_cast; rw [hh, T.par_adj hadj, add_assoc, show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]

open Classical in
/-- The coefficient of `Q` at `π (w, h + 2)` of the image of the arrow from `(w', h + 1)`. -/
def Cf (w w' : D) (h : ℤ) : kˣ :=
  if hv : T.G.Adj w' w ∧ ((h : ℤ) : ZMod 2) = T.par w then
    c ⟨π.obj ⟨w, h + 2, par_two T w h hv.2⟩, hQ.mem_nonprojective _⟩
      (π.obj ⟨w', h + 1, par_one T hv.1 h hv.2⟩) (π.map ⟨⟨hv.1, by ring⟩⟩)
  else 1

theorem pullCoeff_eq (X : T.zQuiver.nonprojective) (Y : T.ZVert) (A : Y ⟶ X.1) :
    T.pullCoeff hQ π c X Y A = Cf T hQ π c X.1.v Y.v (X.1.t - 2) := by
  obtain ⟨⟨w, s, hs⟩, hX⟩ := X
  obtain ⟨w', s', hs'⟩ := Y
  obtain ⟨hadj, ht⟩ := A.down
  change s = s' + 1 at ht
  subst ht
  have hpar : (((s' + 1 - 2 : ℤ)) : ZMod 2) = T.par w := by
    rw [← hs]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, sub_zero]
  unfold Cf
  rw [dif_pos ⟨hadj, hpar⟩]
  exact c_congr c (Subtype.ext (congrArg π.obj (by ext <;> simp <;> ring)))
    (congrArg π.obj (by ext <;> simp <;> ring)) _ _

variable [LinearOrder D] (R : Rooted D) (hσ : ∀ a b, T.G.Adj (R.σ a) (R.σ b) ↔ T.G.Adj a b)
  (c0 : ℕ) (hσp : ∀ v, T.par (R.σ v) = T.par v + ((c0 : ℤ) : ZMod 2))
  (hdeck : ∀ Z, π.obj ((T.zAct R.σ hσ (c0 : ℤ) hσp).obj Z) = π.obj Z)

include hdeck in
theorem Cf_inv (w w' : D) (h : ℤ) :
    Cf T hQ π c (R.σ w) (R.σ w') (h + c0) = Cf T hQ π c w w' h := by
  unfold Cf
  by_cases hv : T.G.Adj w' w ∧ ((h : ℤ) : ZMod 2) = T.par w
  · have hv' : T.G.Adj (R.σ w') (R.σ w) ∧ ((h + c0 : ℤ) : ZMod 2) = T.par (R.σ w) := by
      refine ⟨(hσ _ _).2 hv.1, ?_⟩
      rw [hσp, ← hv.2]; push_cast; ring
    rw [dif_pos hv, dif_pos hv']
    refine c_congr c (Subtype.ext ?_) ?_ _ _
    · refine (congrArg π.obj ?_).trans (hdeck ⟨w, h + 2, par_two T w h hv.2⟩)
      ext <;> simp [OrientedTree.zAct] <;> ring
    · refine (congrArg π.obj ?_).trans (hdeck ⟨w', h + 1, par_one T hv.1 h hv.2⟩)
      ext <;> simp [OrientedTree.zAct] <;> ring
  · have hv' : ¬ (T.G.Adj (R.σ w') (R.σ w) ∧ ((h + c0 : ℤ) : ZMod 2) = T.par (R.σ w)) := by
      rintro ⟨h1, h2⟩
      refine hv ⟨(hσ _ _).1 h1, ?_⟩
      rw [hσp] at h2; push_cast at h2
      exact add_right_cancel h2
    rw [dif_neg hv, dif_neg hv']

/-- The endpoint of an edge further from the root. -/
def child (w w' : D) : D := if w' ≠ R.o ∧ R.pa w' = w then w' else w

variable (hadj : ∀ u w, T.G.Adj u w ↔ (u ≠ R.o ∧ R.pa u = w) ∨ (w ≠ R.o ∧ R.pa w = u))
  (horient : ∀ u w, T.orient u w ↔ (w ≠ R.o ∧ R.pa w = u))

theorem pa_pa_ne (v : D) (hv : v ≠ R.o) (hpv : R.pa v ≠ R.o) : R.pa (R.pa v) ≠ v := by
  intro h
  have h1 := R.dep_pa v hv
  have h2 := R.dep_pa (R.pa v) hpv
  rw [h] at h2; omega

theorem child_up (v : D) (hv : v ≠ R.o) : child R v (R.pa v) = v := by
  unfold child
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact pa_pa_ne R v hv h1 h2

theorem child_down (v : D) (hv : v ≠ R.o) : child R (R.pa v) v = v := by
  unfold child; rw [if_pos ⟨hv, rfl⟩]

theorem child_σ (w w' : D) : child R (R.σ w) (R.σ w') = R.σ (child R w w') := by
  unfold child
  have e : (R.σ w' ≠ R.o ∧ R.pa (R.σ w') = R.σ w) ↔ (w' ≠ R.o ∧ R.pa w' = w) := by
    rw [ne_eq, ne_eq, R.σ_eq_o_iff, ← R.σ_pa, R.σ.injective.eq_iff]
  by_cases h : w' ≠ R.o ∧ R.pa w' = w
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' ↦ h (e.1 h')), if_neg h]

include horient in
theorem sgn_σ (w w' : D) : T.sgn k (R.σ w) (R.σ w') = T.sgn k w w' := by
  unfold OrientedTree.sgn
  have e : T.orient (R.σ w) (R.σ w') ↔ T.orient w w' := by
    rw [horient, horient, ne_eq, ne_eq, R.σ_eq_o_iff, ← R.σ_pa, R.σ.injective.eq_iff]
  by_cases h : T.orient w w'
  · rw [if_pos h, if_pos (e.2 h)]
  · rw [if_neg h, if_neg (fun h' ↦ h (e.1 h'))]

/-- The relation scales and arrow scales on `ℤΔ`. -/
abbrev Nz := R.N (Cf T hQ π c) (fun w w' ↦ T.sgn k w w') T.par c0
abbrev Mz := R.M (Cf T hQ π c) (fun w w' ↦ T.sgn k w w') T.par c0

include hσp in
theorem hpr_of (hc0e : Even c0) (w : D) : T.par (R.σ w) = T.par w := by
  rw [hσp]; obtain ⟨r, hr⟩ := hc0e; rw [hr]; push_cast
  rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul, add_zero]

include hσ hdeck hadj horient in
/-- **The gauge equations on `ℤΔ`**. -/
theorem zEq (hc0 : 0 < c0) (hc0e : Even c0) (X : T.zQuiver.nonprojective) (Y : T.ZVert)
    (A : Y ⟶ X.1) :
    T.zSigned k X Y A =
      Nz T hQ π c R c0 X.1.v X.1.t * T.pullCoeff hQ π c X Y A *
        Mz T hQ π c R c0 (child R X.1.v Y.v) (X.1.t - 2) *
          Mz T hQ π c R c0 (child R Y.v X.1.v) Y.t := by
  rw [pullCoeff_eq]
  obtain ⟨⟨w, s, hs⟩, hX⟩ := X
  obtain ⟨w', s', hs'⟩ := Y
  obtain ⟨hadjw, ht⟩ := A.down
  change s = s' + 1 at ht
  subst ht
  change T.sgn k w w' = Nz T hQ π c R c0 w (s' + 1) * Cf T hQ π c w w' (s' + 1 - 2) *
    Mz T hQ π c R c0 (child R w w') (s' + 1 - 2) * Mz T hQ π c R c0 (child R w' w) s'
  have hpar : ((s' + 1 - 2 : ℤ) : ZMod 2) = T.par w := by
    rw [← hs]; push_cast; rw [show (2 : ZMod 2) = 0 from rfl, sub_zero]
  set u := s' + 1 - 2 with hu
  rw [show s' = u + 1 by omega, show u + 1 + 1 = u + 2 by ring]
  rcases (hadj w' w).1 hadjw with ⟨hw'o, hpw'⟩ | ⟨hwo, hpw⟩
  · -- `w'` is the child
    subst hpw'
    have e := (R.main (Cf T hQ π c) (fun w w' ↦ T.sgn k w w') T.par c0 hc0 hc0e
      (Cf_inv T hQ π c R hσ c0 hσp hdeck) (sgn_σ T R horient) (hpr_of T R c0 hσp hc0e) _ w'
      rfl).2 hw'o u
    have hne : (u : ZMod 2) ≠ T.par w' := by
      rw [hpar, T.par_adj hadjw]; intro h
      have := congrArg (· - T.par w') h; simp at this
    rw [if_neg hne] at e
    rw [child_down R w' hw'o, child_up R w' hw'o]
    simp only [Rooted.lineS, if_neg hne, mul_one] at e
    rw [eq_mul_inv_iff_mul_eq] at e
    rw [← e]; simp only [Nz, Mz]; ac_rfl
  · -- `w` is the child
    subst hpw
    have e := (R.main (Cf T hQ π c) (fun w w' ↦ T.sgn k w w') T.par c0 hc0 hc0e
      (Cf_inv T hQ π c R hσ c0 hσp hdeck) (sgn_σ T R horient) (hpr_of T R c0 hσp hc0e) _ w
      rfl).2 hwo u
    rw [if_pos hpar] at e
    rw [child_up R w hwo, child_down R w hwo]
    simp only [Rooted.lineS, if_pos hpar] at e
    rw [eq_mul_inv_iff_mul_eq] at e
    rw [← e]; simp only [Nz, Mz]; ac_rfl

/-! ### Descent to `Q` -/

/-- The deck transformation on vertices. -/
abbrev gZ : T.ZVert → T.ZVert := (T.zAct R.σ hσ (c0 : ℤ) hσp).obj

theorem gZ_iter (n : ℕ) (X : T.ZVert) :
    ((gZ T R hσ c0 hσp)^[n] X).v = (R.σ ^ n) X.v ∧ ((gZ T R hσ c0 hσp)^[n] X).t = X.t + n * c0 := by
  induction n generalizing X with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      obtain ⟨h1, h2⟩ := ih X
      refine ⟨?_, ?_⟩
      · change R.σ ((gZ T R hσ c0 hσp)^[n] X).v = R.σ ((R.σ ^ n) X.v); rw [h1]
      · change ((gZ T R hσ c0 hσp)^[n] X).t + c0 = _; rw [h2]; push_cast; ring

theorem gZ_arrow (n : ℕ) {X Y : T.ZVert} (A : Nonempty (Y ⟶ X)) :
    Nonempty ((gZ T R hσ c0 hσp)^[n] Y ⟶ (gZ T R hσ c0 hσp)^[n] X) := by
  induction n with
  | zero => exact A
  | succ n ih =>
      obtain ⟨B⟩ := ih
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ⟨(T.zAct R.σ hσ (c0 : ℤ) hσp).map B⟩

include hdeck in
theorem π_gZ_iter (n : ℕ) (X : T.ZVert) : π.obj ((gZ T R hσ c0 hσp)^[n] X) = π.obj X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', hdeck, ih]

/-- The relation scale at a vertex of `ℤΔ`. -/
def Ez (X : T.ZVert) : kˣ := Nz T hQ π c R c0 X.v X.t

/-- The arrow scale of the arrow `Y → X` of `ℤΔ`. -/
def Fz (Y X : T.ZVert) : kˣ := Mz T hQ π c R c0 (child R Y.v X.v) Y.t

include hσ hdeck horient in
theorem inv_all (hc0 : 0 < c0) (hc0e : Even c0) (v : D) (s : ℤ) :
    Nz T hQ π c R c0 (R.σ v) (s + c0) = Nz T hQ π c R c0 v s ∧
      Mz T hQ π c R c0 (R.σ v) (s + c0) = Mz T hQ π c R c0 v s :=
  (R.main (Cf T hQ π c) (fun w w' ↦ T.sgn k w w') T.par c0 hc0 hc0e
    (Cf_inv T hQ π c R hσ c0 hσp hdeck) (sgn_σ T R horient) (hpr_of T R c0 hσp hc0e) _ v
    rfl).1 s

include hσ hdeck horient in
theorem Ez_iter (hc0 : 0 < c0) (hc0e : Even c0) (n : ℕ) (X : T.ZVert) :
    Ez T hQ π c R c0 ((gZ T R hσ c0 hσp)^[n] X) = Ez T hQ π c R c0 X := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ← ih]
      exact (inv_all T hQ π c R hσ c0 hσp hdeck horient hc0 hc0e _ _).1

include hσ hdeck horient in
theorem Fz_iter (hc0 : 0 < c0) (hc0e : Even c0) (n : ℕ) (Y X : T.ZVert) :
    Fz T hQ π c R c0 ((gZ T R hσ c0 hσp)^[n] Y) ((gZ T R hσ c0 hσp)^[n] X) =
      Fz T hQ π c R c0 Y X := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      unfold Fz
      change Mz T hQ π c R c0 (child R (R.σ _) (R.σ _)) (_ + c0) = _
      rw [child_σ R]
      exact (inv_all T hQ π c R hσ c0 hσp hdeck horient hc0 hc0e _ _).2

variable (hπ : π.IsCovering)

include hπ in
/-- Arrows into a vertex of `ℤΔ` are determined by the image of their source. -/
theorem lift_unique (X : T.ZVert) {Y₁ Y₂ : T.ZVert} (A₁ : Y₁ ⟶ X) (A₂ : Y₂ ⟶ X)
    (h : π.obj Y₁ = π.obj Y₂) : Y₁ = Y₂ := by
  have := (hπ.costar_bijective X).1 (a₁ := ⟨Y₁, A₁⟩) (a₂ := ⟨Y₂, A₂⟩)
    (Sigma.ext h (Subsingleton.helim (congrArg (· ⟶ π.obj X) h) _ _))
  exact congrArg Sigma.fst this

include hπ in
theorem lift_exists (X : T.ZVert) {y : V} (a : y ⟶ π.obj X) :
    ∃ Y, Nonempty (Y ⟶ X) ∧ π.obj Y = y := by
  obtain ⟨⟨Y, A⟩, hYA⟩ := (hπ.costar_bijective X).2 ⟨y, a⟩
  exact ⟨Y, ⟨A⟩, congrArg Sigma.fst hYA⟩

variable (hsurj : ∀ x : V, ∃ X, π.obj X = x)
  (hfib : ∀ X Y : T.ZVert, π.obj X = π.obj Y →
    ∃ n : ℕ, Y = (gZ T R hσ c0 hσp)^[n] X ∨ X = (gZ T R hσ c0 hσp)^[n] Y)

/-- The relation scales on `Q`. -/
def ηQ (x : Q.nonprojective) : kˣ := Ez T hQ π c R c0 (hsurj x.1).choose

/-- The arrow scales on `Q`. -/
def μQ {y x : V} (a : y ⟶ x) : kˣ :=
  Fz T hQ π c R c0 (lift_exists T π hπ (hsurj x).choose
    (Quiver.Hom.cast rfl (hsurj x).choose_spec.symm a)).choose (hsurj x).choose

include hσ hdeck horient hfib in
theorem ηQ_eq (hc0 : 0 < c0) (hc0e : Even c0) (X : T.ZVert) :
    ηQ T hQ π c R c0 hsurj ⟨π.obj X, hQ.mem_nonprojective _⟩ = Ez T hQ π c R c0 X := by
  unfold ηQ
  set X' := (hsurj (π.obj X)).choose
  have hX' : π.obj X' = π.obj X := (hsurj _).choose_spec
  obtain ⟨n, h | h⟩ := hfib X' X hX'
  · rw [h, Ez_iter T hQ π c R hσ c0 hσp hdeck horient hc0 hc0e]
  · rw [h, Ez_iter T hQ π c R hσ c0 hσp hdeck horient hc0 hc0e]

include hσ hdeck horient hfib hπ in
theorem Fz_fibre (hc0 : 0 < c0) (hc0e : Even c0) {X X' Y Y' : T.ZVert}
    (hX : π.obj X' = π.obj X) (hY : π.obj Y' = π.obj Y) (A : Y ⟶ X) (A' : Y' ⟶ X') :
    Fz T hQ π c R c0 Y' X' = Fz T hQ π c R c0 Y X := by
  obtain ⟨n, h | h⟩ := hfib X X' hX.symm
  · obtain ⟨B⟩ := gZ_arrow T R hσ c0 hσp n ⟨A⟩
    rw [← h] at B
    have hY' : Y' = (gZ T R hσ c0 hσp)^[n] Y :=
      lift_unique T π hπ X' A' B (by rw [hY, π_gZ_iter T π R hσ c0 hσp hdeck])
    rw [hY', h, Fz_iter T hQ π c R hσ c0 hσp hdeck horient hc0 hc0e]
  · obtain ⟨B⟩ := gZ_arrow T R hσ c0 hσp n ⟨A'⟩
    rw [← h] at B
    have hY' : Y = (gZ T R hσ c0 hσp)^[n] Y' :=
      lift_unique T π hπ X A B (by rw [π_gZ_iter T π R hσ c0 hσp hdeck, hY])
    rw [hY', h, Fz_iter T hQ π c R hσ c0 hσp hdeck horient hc0 hc0e]

include hσ hdeck horient hfib in
theorem μQ_eq (hc0 : 0 < c0) (hc0e : Even c0) {Y X : T.ZVert} (A : Y ⟶ X) :
    μQ T hQ π c R c0 hπ hsurj (π.map A) = Fz T hQ π c R c0 Y X := by
  unfold μQ
  have hX' := (hsurj (π.obj X)).choose_spec
  obtain ⟨⟨A'⟩, hY'⟩ := (lift_exists T π hπ (hsurj (π.obj X)).choose
    (Quiver.Hom.cast rfl hX'.symm (π.map A))).choose_spec
  exact Fz_fibre T hQ π c R hσ c0 hσp hdeck horient hπ hfib hc0 hc0e hX' hY' A A'

theorem μQ_congr {y x y' x' : V} (a : y ⟶ x) (a' : y' ⟶ x') (hy : y = y') (hx : x = x') :
    μQ T hQ π c R c0 hπ hsurj a = μQ T hQ π c R c0 hπ hsurj a' := by
  subst hy hx; rw [Subsingleton.elim a a']

variable (hτ : ∀ Y, π.obj (T.ztau Y) = hQ.tauE (π.obj Y))

include hσ hdeck hadj horient hfib hτ hπ hsurj in
/-- **Lemma A.1(1)** (`lem:periodic-scalar-gauges`), for an arbitrary finite tree `Δ`
oriented away from a root `o` fixed by the twist `σ`: for a covering `π : ℤΔ → Q` commuting
with translation whose fibres are the orbits of `g (v, t) = (σ v, t + c₀)`, rescaling arrows and
entire mesh relations of `Q` turns every coefficient system into the signed preprojective
coefficients. -/
theorem exists_signed_gauge (hc0 : 0 < c0) (hc0e : Even c0) :
    ∃ (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ),
      T.pullCoeff hQ π (fun x y a ↦ η x * c x y a * μ (Q.mate x y a) * μ a) = T.zSigned k := by
  refine ⟨fun a ↦ μQ T hQ π c R c0 hπ hsurj a, ηQ T hQ π c R c0 hsurj, ?_⟩
  funext X Y A
  rw [zEq T hQ π c R hσ c0 hσp hdeck hadj horient hc0 hc0e X Y A]
  change ηQ T hQ π c R c0 hsurj ⟨π.obj X.1, hQ.mem_nonprojective _⟩ * _ *
    μQ T hQ π c R c0 hπ hsurj _ * μQ T hQ π c R c0 hπ hsurj (π.map A) = _
  have hm := μQ_congr T hQ π c R c0 hπ hsurj (Q.mate (T.piNP hQ π X.1) (π.obj Y) (π.map A))
    (π.map (T.zQuiver.mate X Y A)) (hτ X.1).symm rfl
  rw [ηQ_eq T hQ π c R hσ c0 hσp hdeck horient hsurj hfib hc0 hc0e,
    μQ_eq T hQ π c R hσ c0 hσp hdeck horient hπ hsurj hfib hc0 hc0e A, hm,
    μQ_eq T hQ π c R hσ c0 hσp hdeck horient hπ hsurj hfib hc0 hc0e]
  rfl

omit [LinearOrder D] in
include hσ hdeck hadj horient hfib hτ hπ hsurj in
/-- **Lemma A.1(1)**, without an auxiliary order on the vertices. -/
theorem exists_signed_gauge' (hc0 : 0 < c0) (hc0e : Even c0) :
    ∃ (μ : ∀ {x y : V}, (x ⟶ y) → kˣ) (η : Q.nonprojective → kˣ),
      T.pullCoeff hQ π (fun x y a ↦ η x * c x y a * μ (Q.mate x y a) * μ a) = T.zSigned k := by
  letI : LinearOrder D := LinearOrder.lift' (Fintype.equivFin D) (Fintype.equivFin D).injective
  exact exists_signed_gauge T hQ π c R hσ c0 hσp hdeck hadj horient hπ hsurj hfib hτ hc0 hc0e

end Tree

end RootedGauge

end MultiplicativeBasisDeformations
