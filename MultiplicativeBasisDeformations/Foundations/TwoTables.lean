import Mathlib

/-!
# Lemma 11.1: two associative tables

`binary-families.tex:23–70` (`lem:two-associative-tables`): "Let `S` be a finite set with an
absorbing zero, and let `m, m_*` be associative products on `S` […] Suppose
`m_*(a,b) = m(a,b)` whenever `m(a,b) ≠ 0`. Put `Z = {(a,b) : m(a,b) = 0, m_*(a,b) ≠ 0}` and
let `ε_z` be the bilinear map supported at `z = (a,b)` with value `m_*(a,b)` […] Assume all
nested insertions vanish. There is an equivalence relation on `Z` such that, over every
commutative ring `R`, the Hochschild two-cocycles among the cochains `∑ a_z ε_z` have basis
`μ_E = ∑_{z∈E} ε_z`, indexed by its classes. The product `m + ∑_E T_E μ_E` is associative
over the polynomial ring in the `T_E`. When every `T_E` is zero or one, `S ∖ {0}` is a
multiplicative basis for this product."

Formalization: an `R`-algebra `Λ` with a basis `b` indexed by `S` (the nonzero elements),
`b x * b y = b (m x y)` or `0` (`m : S → S → Option S`), and a second associative table
`ms` agreeing with `m` where `m` is nonzero. For coefficients `a : S → S → R`, `eps a` is
`∑_{z ∈ Z} a_z ε_z`. Each cocycle equation at a basis triple `t` has the form
`(a (L t) − a (Rt t)) • U t = 0` with a common value `U t` (`dEps_eq`). Hence a cochain is a
cocycle iff `a` is constant along the relation `Rel` of the nonvanishing equations
(`isCocycle_iff`); the product `m + eps T` is associative for such `T` (`assoc_add_eps`),
and has `b` as a multiplicative basis when `T` takes values `0, 1` (`mul_basis_of_binary`).
-/

set_option autoImplicit false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace TwoTables

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {S : Type*}
  [DecidableEq S] (b : Module.Basis S R Λ) (m ms : S → S → Option S)

/-- The basis vector of an optional index. -/
def ob (o : Option S) : Λ := o.elim 0 b

@[simp] theorem ob_none : ob b none = 0 := rfl
@[simp] theorem ob_some (s : S) : ob b (some s) = b s := rfl

/-- The support `Z`. -/
def InZ (x y : S) : Prop := m x y = none ∧ ms x y ≠ none

instance (x y : S) : Decidable (InZ m ms x y) := by unfold InZ; infer_instance

/-- The values of the supported cochain with coefficients `a` on basis pairs. -/
def epsVal (a : S → S → R) (x y : S) : Λ := if InZ m ms x y then a x y • ob b (ms x y) else 0

/-- **The supported cochain** `∑_{z ∈ Z} a_z ε_z`. -/
def eps (a : S → S → R) : Λ →ₗ[R] Λ →ₗ[R] Λ :=
  b.constr R fun x ↦ b.constr R fun y ↦ epsVal b m ms a x y

theorem eps_basis (a : S → S → R) (x y : S) : eps b m ms a (b x) (b y) = epsVal b m ms a x y := by
  simp [eps, Module.Basis.constr_basis]

theorem eps_ob_left (a : S → S → R) (o : Option S) (y : S) :
    eps b m ms a (ob b o) (b y) = o.elim 0 fun x ↦ epsVal b m ms a x y := by
  cases o <;> simp [eps_basis]

theorem eps_ob_right (a : S → S → R) (x : S) (o : Option S) :
    eps b m ms a (b x) (ob b o) = o.elim 0 fun y ↦ epsVal b m ms a x y := by
  cases o <;> simp [eps_basis]

variable (hm : ∀ x y, b x * b y = ob b (m x y))

include hm in
theorem mul_ob (x : S) (o : Option S) : b x * ob b o = ob b (o.bind (m x ·)) := by
  cases o <;> simp [hm]

include hm in
theorem ob_mul (o : Option S) (w : S) : ob b o * b w = ob b (o.bind (m · w)) := by
  cases o <;> simp [hm]

/-- The cocycle defect of `eps a` at a basis triple. -/
def D (a : S → S → R) (x y w : S) : Λ :=
  b x * eps b m ms a (b y) (b w) - eps b m ms a (b x * b y) (b w) + eps b m ms a (b x) (b y * b w) -
    eps b m ms a (b x) (b y) * b w

variable (hagree : ∀ x y s, m x y = some s → ms x y = some s)
  (hms : ∀ x y w, (ms x y).bind (ms · w) = (ms y w).bind (ms x ·))
  (hnest : ∀ x y s, InZ m ms x y → ms x y = some s → ∀ w, ¬ InZ m ms s w ∧ ¬ InZ m ms w s)

/-- The second table as a bilinear map. -/
def mstar : Λ →ₗ[R] Λ →ₗ[R] Λ := b.constr R fun x ↦ b.constr R fun y ↦ ob b (ms x y)

theorem mstar_basis (x y : S) : mstar b ms (b x) (b y) = ob b (ms x y) := by
  simp [mstar, Module.Basis.constr_basis]

include hm hagree in
theorem mstar_eq (x y : S) :
    mstar b ms (b x) (b y) = b x * b y + eps b m ms (fun _ _ ↦ 1) (b x) (b y) := by
  rw [mstar_basis, eps_basis, hm, epsVal]
  by_cases hxy : m x y = none
  · by_cases hs : ms x y = none
    · simp [hxy, hs, InZ]
    · rw [if_pos ⟨hxy, hs⟩, hxy]; simp
  · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 hxy
    rw [hagree x y s hs, if_neg (fun h ↦ hxy h.1), hs]; simp

include hm hagree hms hnest in
/-- **`d ε = 0`** for the full cochain `ε = ∑_{z ∈ Z} ε_z`. -/
theorem D_one (x y w : S) : D b m ms (fun _ _ ↦ 1) x y w = 0 := by
  set e := eps b m ms (fun _ _ ↦ (1 : R))
  -- associativity of the second table on basis vectors
  have hl : ∀ o : Option S, mstar b ms (ob b o) (b w) = ob b (o.bind (ms · w)) := by
    intro o; cases o <;> simp [mstar_basis]
  have hr : ∀ o : Option S, mstar b ms (b x) (ob b o) = ob b (o.bind (ms x ·)) := by
    intro o; cases o <;> simp [mstar_basis]
  have hass : mstar b ms (mstar b ms (b x) (b y)) (b w) = mstar b ms (b x) (mstar b ms (b y) (b w)) := by
    rw [mstar_basis, mstar_basis, hl, hr, hms]
  -- nested insertions vanish
  have hn1 : e (e (b x) (b y)) (b w) = 0 := by
    rw [eps_basis, epsVal]
    split_ifs with h
    · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h.2
      rw [hs, map_smul, LinearMap.smul_apply, ob_some, eps_basis, epsVal,
        if_neg (hnest x y s h hs w).1, smul_zero]
    · simp
  have hn2 : e (b x) (e (b y) (b w)) = 0 := by
    rw [eps_basis b m ms (fun _ _ ↦ (1 : R)) y w, epsVal]
    split_ifs with h
    · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h.2
      rw [hs, map_smul, ob_some, eps_basis, epsVal, if_neg (hnest y w s h hs x).2, smul_zero]
    · simp
  -- expand `m_* = m + ε` on both sides
  have hexp : ∀ p q : Λ, mstar b ms p q = p * q + e p q := by
    intro p q
    have h1 : mstar b ms = LinearMap.mul R Λ + e := by
      refine b.ext fun x' ↦ b.ext fun y' ↦ ?_
      rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.mul_apply',
        mstar_eq b m ms hm hagree]
    rw [h1, LinearMap.add_apply, LinearMap.add_apply, LinearMap.mul_apply']
  rw [hexp, hexp, hexp (b y), hexp] at hass
  simp only [map_add, LinearMap.add_apply, add_mul, mul_add, hn1, hn2, add_zero] at hass
  rw [mul_assoc] at hass
  have h0 := sub_eq_zero.2 hass.symm
  unfold D
  change b x * e (b y) (b w) - e (b x * b y) (b w) + e (b x) (b y * b w) - e (b x) (b y) * b w = 0
  rw [← h0]
  abel

/-! ### Each cocycle equation compares two coefficients -/

theorem T1 (a : S → S → R) (x y w : S) :
    b x * eps b m ms a (b y) (b w) = a y w • (b x * eps b m ms (fun _ _ ↦ 1) (b y) (b w)) := by
  rw [eps_basis, eps_basis, epsVal, epsVal]
  split_ifs <;> simp [mul_smul_comm]

theorem T4 (a : S → S → R) (x y w : S) :
    eps b m ms a (b x) (b y) * b w = a x y • (eps b m ms (fun _ _ ↦ 1) (b x) (b y) * b w) := by
  rw [eps_basis, eps_basis, epsVal, epsVal]
  split_ifs <;> simp [smul_mul_assoc]

theorem T2 (x y w : S) : ∃ p : S × S, ∀ a : S → S → R,
    eps b m ms a (ob b (m x y)) (b w) = a p.1 p.2 • eps b m ms (fun _ _ ↦ 1) (ob b (m x y)) (b w) := by
  cases h : m x y with
  | none => exact ⟨(x, w), fun a ↦ by simp⟩
  | some s =>
    refine ⟨(s, w), fun a ↦ ?_⟩
    simp only [ob_some, eps_basis, epsVal]
    split_ifs <;> simp

theorem T3 (x y w : S) : ∃ p : S × S, ∀ a : S → S → R,
    eps b m ms a (b x) (ob b (m y w)) = a p.1 p.2 • eps b m ms (fun _ _ ↦ 1) (b x) (ob b (m y w)) := by
  cases h : m y w with
  | none => exact ⟨(x, w), fun a ↦ by simp⟩
  | some s =>
    refine ⟨(x, s), fun a ↦ ?_⟩
    simp only [ob_some, eps_basis, epsVal]
    split_ifs <;> simp

include hm in
theorem W1_ob (x y w : S) : ∃ o : Option S, b x * eps b m ms (fun _ _ ↦ (1 : R)) (b y) (b w) = ob b o := by
  rw [eps_basis, epsVal]
  split_ifs
  · exact ⟨(ms y w).bind (m x ·), by rw [one_smul, mul_ob b m hm]⟩
  · exact ⟨none, by simp⟩

theorem W3_ob (x : S) (o' : Option S) :
    ∃ o : Option S, eps b m ms (fun _ _ ↦ (1 : R)) (b x) (ob b o') = ob b o := by
  cases o' with
  | none => exact ⟨none, by simp⟩
  | some s =>
    rw [ob_some, eps_basis, epsVal]
    split_ifs
    · exact ⟨ms x s, by rw [one_smul]⟩
    · exact ⟨none, by simp⟩

include hm hagree hms hnest in
/-- **The form of a cocycle equation**: `d(∑ a_z ε_z)` at a basis triple is
`(a_z − a_{z'}) u` for two pairs `z, z'` and a basis vector or zero `u`. -/
theorem dEps_eq (x y w : S) : ∃ (zl zr : S × S) (o : Option S),
    ∀ a : S → S → R, D b m ms a x y w = (a zl.1 zl.2 - a zr.1 zr.2) • ob b o := by
  obtain ⟨p2, hp2⟩ := T2 b m ms x y w
  obtain ⟨p3, hp3⟩ := T3 b m ms x y w
  have hD : ∀ a, D b m ms a x y w =
      a y w • (b x * eps b m ms (fun _ _ ↦ 1) (b y) (b w)) -
      a p2.1 p2.2 • eps b m ms (fun _ _ ↦ 1) (ob b (m x y)) (b w) +
      a p3.1 p3.2 • eps b m ms (fun _ _ ↦ 1) (b x) (ob b (m y w)) -
      a x y • (eps b m ms (fun _ _ ↦ 1) (b x) (b y) * b w) := by
    intro a
    unfold D
    rw [T1, T4, hm x y, hm y w, hp2 a, hp3 a]
  have h1 := D_one b m ms hm hagree hms hnest x y w
  rw [hD] at h1
  simp only [one_smul] at h1
  obtain ⟨o1, ho1⟩ := W1_ob b m ms hm x y w
  obtain ⟨o3, ho3⟩ := W3_ob b m ms x (m y w)
  -- vanishing terms
  have hz4 : m x y ≠ none → eps b m ms (fun _ _ ↦ (1 : R)) (b x) (b y) * b w = 0 := fun h ↦ by
    rw [eps_basis, epsVal, if_neg (fun h' ↦ h h'.1), zero_mul]
  have hz1 : m y w ≠ none → b x * eps b m ms (fun _ _ ↦ (1 : R)) (b y) (b w) = 0 := fun h ↦ by
    rw [eps_basis, epsVal, if_neg (fun h' ↦ h h'.1), mul_zero]
  cases hxy : m x y with
  | none =>
    have hz2 : eps b m ms (fun _ _ ↦ (1 : R)) (ob b (m x y)) (b w) = 0 := by rw [hxy]; simp
    cases hyw : m y w with
    | none =>
      have hz3 : eps b m ms (fun _ _ ↦ (1 : R)) (b x) (ob b (m y w)) = 0 := by rw [hyw]; simp
      rw [hz2, hz3] at h1
      refine ⟨(y, w), (x, y), o1, fun a ↦ ?_⟩
      rw [hD, hz2, hz3, ← ho1, sub_smul]
      have : b x * eps b m ms (fun _ _ ↦ (1 : R)) (b y) (b w) =
          eps b m ms (fun _ _ ↦ (1 : R)) (b x) (b y) * b w := by
        rw [← sub_eq_zero, ← h1]; abel
      rw [this]; simp
    | some s =>
      rw [hz2, hz1 (by rw [hyw]; simp)] at h1
      refine ⟨p3, (x, y), o3, fun a ↦ ?_⟩
      rw [hD, hz2, hz1 (by rw [hyw]; simp), ← ho3, sub_smul]
      have : eps b m ms (fun _ _ ↦ (1 : R)) (b x) (ob b (m y w)) =
          eps b m ms (fun _ _ ↦ (1 : R)) (b x) (b y) * b w := by
        rw [← sub_eq_zero, ← h1]; abel
      rw [this]; simp
  | some s =>
    have hn4 := hz4 (by rw [hxy]; simp)
    cases hyw : m y w with
    | none =>
      have hz3 : eps b m ms (fun _ _ ↦ (1 : R)) (b x) (ob b (m y w)) = 0 := by rw [hyw]; simp
      rw [hz3, hn4] at h1
      refine ⟨(y, w), p2, o1, fun a ↦ ?_⟩
      rw [hD, hz3, hn4, ← ho1, sub_smul]
      have : b x * eps b m ms (fun _ _ ↦ (1 : R)) (b y) (b w) =
          eps b m ms (fun _ _ ↦ (1 : R)) (ob b (m x y)) (b w) := by
        rw [← sub_eq_zero, ← h1]; abel
      rw [this]; simp
    | some s' =>
      have hn1 := hz1 (by rw [hyw]; simp)
      rw [hn1, hn4] at h1
      refine ⟨p3, p2, o3, fun a ↦ ?_⟩
      rw [hD, hn1, hn4, ← ho3, sub_smul]
      have : eps b m ms (fun _ _ ↦ (1 : R)) (b x) (ob b (m y w)) =
          eps b m ms (fun _ _ ↦ (1 : R)) (ob b (m x y)) (b w) := by
        rw [← sub_eq_zero, ← h1]; abel
      rw [this]; simp; abel

/-! ### Cocycles, associativity and binary points -/

omit [DecidableEq S] in
/-- Trilinear expressions vanishing on basis triples vanish. -/
theorem tri_ext (F : Λ → Λ → Λ → Λ)
    (h1 : ∀ q r, ∃ L : Λ →ₗ[R] Λ, ∀ p, F p q r = L p)
    (h2 : ∀ p r, ∃ L : Λ →ₗ[R] Λ, ∀ q, F p q r = L q)
    (h3 : ∀ p q, ∃ L : Λ →ₗ[R] Λ, ∀ r, F p q r = L r)
    (h0 : ∀ x y w, F (b x) (b y) (b w) = 0) : ∀ p q r, F p q r = 0 := by
  have s1 : ∀ p y w, F p (b y) (b w) = 0 := by
    intro p y w
    obtain ⟨L, hL⟩ := h1 (b y) (b w)
    have : L = 0 := b.ext fun x ↦ by rw [← hL, h0, LinearMap.zero_apply]
    rw [hL, this, LinearMap.zero_apply]
  have s2 : ∀ p q w, F p q (b w) = 0 := by
    intro p q w
    obtain ⟨L, hL⟩ := h2 p (b w)
    have : L = 0 := b.ext fun y ↦ by rw [← hL, s1, LinearMap.zero_apply]
    rw [hL, this, LinearMap.zero_apply]
  intro p q r
  obtain ⟨L, hL⟩ := h3 p q
  have : L = 0 := b.ext fun w ↦ by rw [← hL, s2, LinearMap.zero_apply]
  rw [hL, this, LinearMap.zero_apply]

/-- The relation of the nonvanishing cocycle equations. -/
def Rel (z z' : S × S) : Prop :=
  ∃ (x y w s : S), ∀ a : S → S → R, D b m ms a x y w = (a z.1 z.2 - a z'.1 z'.2) • b s

include hm hagree hms hnest in
theorem D_eq_zero_of_inv (a : S → S → R) (ha : ∀ z z', Rel b m ms z z' → a z.1 z.2 = a z'.1 z'.2)
    (x y w : S) : D b m ms a x y w = 0 := by
  obtain ⟨zl, zr, o, h⟩ := dEps_eq b m ms hm hagree hms hnest x y w
  cases o with
  | none => rw [h a, ob_none, smul_zero]
  | some s =>
    rw [h a, ha zl zr ⟨x, y, w, s, fun a ↦ by simpa using h a⟩, sub_self, zero_smul]

theorem inv_of_D_eq_zero (a : S → S → R) (h0 : ∀ x y w, D b m ms a x y w = 0) (z z' : S × S)
    (hr : Rel b m ms z z') : a z.1 z.2 = a z'.1 z'.2 := by
  obtain ⟨x, y, w, s, h⟩ := hr
  have h1 := h a
  rw [h0] at h1
  have h2 := congrArg (fun v ↦ b.repr v s) h1
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, map_smul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h2
  exact sub_eq_zero.1 h2.symm

theorem eps_lin1 (a : S → S → R) (q r : Λ) : ∃ L : Λ →ₗ[R] Λ, ∀ p,
    p * eps b m ms a q r - eps b m ms a (p * q) r + eps b m ms a p (q * r) - eps b m ms a p q * r =
      L p :=
  ⟨{ toFun := fun p ↦ p * eps b m ms a q r - eps b m ms a (p * q) r + eps b m ms a p (q * r) -
        eps b m ms a p q * r
     map_add' := fun p p' ↦ by simp only [add_mul, map_add, LinearMap.add_apply]; abel
     map_smul' := fun c p ↦ by
       simp only [smul_mul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_sub,
         smul_add] }, fun _ ↦ rfl⟩

theorem eps_lin2 (a : S → S → R) (p r : Λ) : ∃ L : Λ →ₗ[R] Λ, ∀ q,
    p * eps b m ms a q r - eps b m ms a (p * q) r + eps b m ms a p (q * r) - eps b m ms a p q * r =
      L q :=
  ⟨{ toFun := fun q ↦ p * eps b m ms a q r - eps b m ms a (p * q) r + eps b m ms a p (q * r) -
        eps b m ms a p q * r
     map_add' := fun q q' ↦ by simp only [mul_add, add_mul, map_add, LinearMap.add_apply]; abel
     map_smul' := fun c q ↦ by
       simp only [mul_smul_comm, smul_mul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply,
         smul_sub, smul_add] }, fun _ ↦ rfl⟩

theorem eps_lin3 (a : S → S → R) (p q : Λ) : ∃ L : Λ →ₗ[R] Λ, ∀ r,
    p * eps b m ms a q r - eps b m ms a (p * q) r + eps b m ms a p (q * r) - eps b m ms a p q * r =
      L r :=
  ⟨{ toFun := fun r ↦ p * eps b m ms a q r - eps b m ms a (p * q) r + eps b m ms a p (q * r) -
        eps b m ms a p q * r
     map_add' := fun r r' ↦ by simp only [mul_add, map_add]; abel
     map_smul' := fun c r ↦ by
       simp only [mul_smul_comm, map_smul, RingHom.id_apply, smul_sub, smul_add] }, fun _ ↦ rfl⟩

include hm hagree hms hnest in
/-- **Lemma 11.1, cocycles**: `∑ a_z ε_z` is a Hochschild cocycle when `a` is constant
along `Rel`. -/
theorem isCocycle_eps (a : S → S → R) (ha : ∀ z z', Rel b m ms z z' → a z.1 z.2 = a z'.1 z'.2) :
    ∀ p q r : Λ, p * eps b m ms a q r - eps b m ms a (p * q) r + eps b m ms a p (q * r) -
      eps b m ms a p q * r = 0 :=
  tri_ext b _ (eps_lin1 b m ms a) (eps_lin2 b m ms a) (eps_lin3 b m ms a)
    fun x y w ↦ D_eq_zero_of_inv b m ms hm hagree hms hnest a ha x y w

/-- The deformed product `m + ∑ T_z ε_z`. -/
def mT (T : S → S → R) : Λ →ₗ[R] Λ →ₗ[R] Λ := LinearMap.mul R Λ + eps b m ms T

theorem mT_lin1 (T : S → S → R) (q r : Λ) : ∃ L : Λ →ₗ[R] Λ, ∀ p,
    mT b m ms T (mT b m ms T p q) r - mT b m ms T p (mT b m ms T q r) = L p :=
  ⟨{ toFun := fun p ↦ mT b m ms T (mT b m ms T p q) r - mT b m ms T p (mT b m ms T q r)
     map_add' := fun p p' ↦ by simp only [map_add, LinearMap.add_apply]; abel
     map_smul' := fun c p ↦ by
       simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_sub] }, fun _ ↦ rfl⟩

theorem mT_lin2 (T : S → S → R) (p r : Λ) : ∃ L : Λ →ₗ[R] Λ, ∀ q,
    mT b m ms T (mT b m ms T p q) r - mT b m ms T p (mT b m ms T q r) = L q :=
  ⟨{ toFun := fun q ↦ mT b m ms T (mT b m ms T p q) r - mT b m ms T p (mT b m ms T q r)
     map_add' := fun q q' ↦ by simp only [map_add, LinearMap.add_apply]; abel
     map_smul' := fun c q ↦ by
       simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_sub] }, fun _ ↦ rfl⟩

theorem mT_lin3 (T : S → S → R) (p q : Λ) : ∃ L : Λ →ₗ[R] Λ, ∀ r,
    mT b m ms T (mT b m ms T p q) r - mT b m ms T p (mT b m ms T q r) = L r :=
  ⟨{ toFun := fun r ↦ mT b m ms T (mT b m ms T p q) r - mT b m ms T p (mT b m ms T q r)
     map_add' := fun r r' ↦ by simp only [map_add, LinearMap.add_apply]; abel
     map_smul' := fun c r ↦ by
       simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_sub] }, fun _ ↦ rfl⟩

include hm hagree hms hnest in
/-- **Lemma 11.1, associativity**: `m + ∑ T_z ε_z` is associative when `T` is constant along
`Rel`. -/
theorem assoc_mT (T : S → S → R) (hT : ∀ z z', Rel b m ms z z' → T z.1 z.2 = T z'.1 z'.2) :
    ∀ p q r : Λ, mT b m ms T (mT b m ms T p q) r = mT b m ms T p (mT b m ms T q r) := by
  intro p q r
  rw [← sub_eq_zero]
  revert p q r
  refine tri_ext b (fun p q r ↦ mT b m ms T (mT b m ms T p q) r - mT b m ms T p (mT b m ms T q r))
    (mT_lin1 b m ms T) (mT_lin2 b m ms T) (mT_lin3 b m ms T) fun x y w ↦ ?_
  have hD := D_eq_zero_of_inv b m ms hm hagree hms hnest T hT x y w
  -- nested insertions vanish
  have hn1 : eps b m ms T (eps b m ms T (b x) (b y)) (b w) = 0 := by
    rw [eps_basis, epsVal]
    split_ifs with h
    · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h.2
      rw [hs, map_smul, LinearMap.smul_apply, ob_some, eps_basis, epsVal,
        if_neg (hnest x y s h hs w).1, smul_zero]
    · simp
  have hn2 : eps b m ms T (b x) (eps b m ms T (b y) (b w)) = 0 := by
    rw [eps_basis b m ms T y w, epsVal]
    split_ifs with h
    · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.1 h.2
      rw [hs, map_smul, ob_some, eps_basis, epsVal, if_neg (hnest y w s h hs x).2, smul_zero]
    · simp
  simp only [mT, LinearMap.add_apply, LinearMap.mul_apply', map_add, add_mul, mul_add, hn1, hn2,
    add_zero]
  unfold D at hD
  rw [← mul_assoc, ← neg_eq_zero.2 hD]
  abel

include hm in
/-- **Lemma 11.1, binary points**: when `T` takes the values `0` and `1`, the basis is
multiplicative for `m + ∑ T_z ε_z`. -/
theorem mT_basis_of_binary (T : S → S → R) (hT : ∀ x y, T x y = 0 ∨ T x y = 1) (x y : S) :
    ∃ o : Option S, mT b m ms T (b x) (b y) = ob b o := by
  simp only [mT, LinearMap.add_apply, LinearMap.mul_apply', hm, eps_basis, epsVal]
  split_ifs with h
  · rw [h.1, ob_none, zero_add]
    rcases hT x y with h0 | h1
    · exact ⟨none, by rw [h0, zero_smul, ob_none]⟩
    · exact ⟨ms x y, by rw [h1, one_smul]⟩
  · exact ⟨m x y, add_zero _⟩

end TwoTables

end MultiplicativeBasisDeformations
