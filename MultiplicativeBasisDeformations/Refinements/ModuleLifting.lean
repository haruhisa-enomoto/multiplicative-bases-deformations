import MultiplicativeBasisDeformations.Foundations.SquareZero

/-!
# Proposition 6.5: lifting modules to positive deformations

`positive-deformations.tex:226–318` (`prop:positive-module-lifting`). After Lemma 6.4 the
multiplication of a positive filtered deformation `B` of `Λ` is `μ₀ + Σ_{q>0} μ_q` on the vector
space `Λ`, with `μ₀` the product of `Λ` and `μ_q` raising internal degree by `q` (`PosDef`).
"Seek an action `ν₀ + ν₁ + ⋯` on `M_i` […]. Suppose the action identity holds through internal
degree `t − 1`. Its error in internal degree `t` […] is a bar cocycle of bar degree two. […] Its
class belongs to `Ext²_Λ(M_i, M_i)_t = 0` by hypothesis. A cochain `ν_t` of bar degree one
therefore removes the error."

Formalization. An action is a family `ν n` of bilinear maps raising degree by `n`, with
`ν 0` the given action; the action identity in internal degree `n` is the vanishing of the
associator `assocErr ν μ n` (`ActFam`). The cocycle identity of the error is the degree-`n`
part of the identity `A(E(m,a,b),c) − E(A(m,a),b,c) + E(m,a⋆b,c) − E(m,a,b⋆c) = 0`, proved by
reindexing triple sums (`assocErr_identity`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace MultiplicativeBasisDeformations

namespace GExt

/-! ### Triple sums -/

section Tri

variable {X : Type*} [AddCommGroup X]

/-- The triples of natural numbers with sum `j`. -/
def tri (j : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (j + 1)) ×ˢ (range (j + 1)) ×ˢ (range (j + 1))).filter
    (fun t ↦ t.1 + t.2.1 + t.2.2 = j)

theorem mem_tri {j : ℕ} {t : ℕ × ℕ × ℕ} : t ∈ tri j ↔ t.1 + t.2.1 + t.2.2 = j := by
  simp only [tri, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h ↦ h.2
  · intro h; exact ⟨⟨by omega, by omega, by omega⟩, h⟩

theorem sum_ad_ad_right (j : ℕ) (F : ℕ → ℕ → ℕ → X) :
    ∑ x ∈ antidiagonal j, ∑ y ∈ antidiagonal x.2, F x.1 y.1 y.2 =
      ∑ t ∈ tri j, F t.1 t.2.1 t.2.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ ↦ (x.1.1, x.2.1, x.2.2))
    (fun t _ ↦ ⟨(t.1, t.2.1 + t.2.2), (t.2.1, t.2.2)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨i, l⟩, ⟨u, v⟩⟩ h
    simp only [mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    exact mem_tri.2 (by simp only; omega)
  · rintro ⟨i, u, v⟩ h
    have := mem_tri.1 h
    simp only [mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨by simp only at this ⊢; omega, trivial⟩
  · rintro ⟨⟨i, l⟩, ⟨u, v⟩⟩ h
    simp only [mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    simp only [Sigma.mk.injEq, Prod.mk.injEq, true_and]
    refine ⟨by omega, ?_⟩
    have : l = u + v := by omega
    subst this
    rfl
  · intro t _; rfl
  · intro x _; rfl

theorem sum_ad_ad_left (j : ℕ) (F : ℕ → ℕ → ℕ → X) :
    ∑ x ∈ antidiagonal j, ∑ y ∈ antidiagonal x.1, F y.1 y.2 x.2 =
      ∑ t ∈ tri j, F t.1 t.2.1 t.2.2 := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ ↦ (x.2.1, x.2.2, x.1.2))
    (fun t _ ↦ ⟨(t.1 + t.2.1, t.2.2), (t.1, t.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨l, v⟩, ⟨i, u⟩⟩ h
    simp only [mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    exact mem_tri.2 (by simp only; omega)
  · rintro ⟨i, u, v⟩ h
    have := mem_tri.1 h
    simp only [mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨by simp only at this ⊢; omega, trivial⟩
  · rintro ⟨⟨l, v⟩, ⟨i, u⟩⟩ h
    simp only [mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at h
    simp only [Sigma.mk.injEq, Prod.mk.injEq, and_true]
    have : l = i + u := by omega
    subst this
    exact ⟨rfl, HEq.rfl⟩
  · intro t _; rfl
  · intro x _; rfl

/-- Reindexing a triple sum by a sum-preserving bijection. -/
theorem sum_tri_equiv (j : ℕ) (f : ℕ × ℕ × ℕ → X) (e : ℕ × ℕ × ℕ ≃ ℕ × ℕ × ℕ)
    (he : ∀ t, (e t).1 + (e t).2.1 + (e t).2.2 = t.1 + t.2.1 + t.2.2) :
    ∑ t ∈ tri j, f (e t) = ∑ t ∈ tri j, f t :=
  Finset.sum_equiv e (fun t ↦ by rw [mem_tri, mem_tri, he]) (fun _ _ ↦ rfl)

/-- The coordinate permutation `(a, b, c) ↦ (b, c, a)`. -/
def cyc3 : ℕ × ℕ × ℕ ≃ ℕ × ℕ × ℕ where
  toFun t := (t.2.1, t.2.2, t.1)
  invFun t := (t.2.2, t.1, t.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinate permutation `(a, b, c) ↦ (c, b, a)`. -/
def swap13 : ℕ × ℕ × ℕ ≃ ℕ × ℕ × ℕ where
  toFun t := (t.2.2, t.2.1, t.1)
  invFun t := (t.2.2, t.2.1, t.1)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_tri_cyc (j : ℕ) (F : ℕ → ℕ → ℕ → X) :
    ∑ t ∈ tri j, F t.2.1 t.2.2 t.1 = ∑ t ∈ tri j, F t.1 t.2.1 t.2.2 :=
  sum_tri_equiv j (fun t ↦ F t.1 t.2.1 t.2.2) cyc3 (fun t ↦ by simp only [cyc3]; dsimp; omega)

theorem sum_tri_swap13 (j : ℕ) (F : ℕ → ℕ → ℕ → X) :
    ∑ t ∈ tri j, F t.2.2 t.2.1 t.1 = ∑ t ∈ tri j, F t.1 t.2.1 t.2.2 :=
  sum_tri_equiv j (fun t ↦ F t.1 t.2.1 t.2.2) swap13 (fun t ↦ by simp only [swap13]; dsimp; omega)

/-- The coordinate permutation `(a, b, c) ↦ (b, a, c)`. -/
def swap12 : ℕ × ℕ × ℕ ≃ ℕ × ℕ × ℕ where
  toFun t := (t.2.1, t.1, t.2.2)
  invFun t := (t.2.1, t.1, t.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_tri_swap12 (j : ℕ) (F : ℕ → ℕ → ℕ → X) :
    ∑ t ∈ tri j, F t.2.1 t.1 t.2.2 = ∑ t ∈ tri j, F t.1 t.2.1 t.2.2 :=
  sum_tri_equiv j (fun t ↦ F t.1 t.2.1 t.2.2) swap12 (fun t ↦ by simp only [swap12]; dsimp; omega)

theorem sum_tri_cyc' (j : ℕ) (F : ℕ → ℕ → ℕ → X) :
    ∑ t ∈ tri j, F t.2.2 t.1 t.2.1 = ∑ t ∈ tri j, F t.1 t.2.1 t.2.2 := by
  rw [← sum_tri_cyc j (fun a b c ↦ F c a b)]

end Tri

/-! ### The associator of an action family -/

section Assoc

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- **The action identity in internal degree `n`**: its error
`Σ_{i+j=n} ν_j(ν_i(m,a),b) − Σ_{i+j=n} ν_i(m, μ_j(a,b))`. -/
def assocErr (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (n : ℕ) (m : M)
    (a b : Λ) : M :=
  ∑ x ∈ antidiagonal n, ν x.2 (ν x.1 m a) b - ∑ x ∈ antidiagonal n, ν x.1 m (μ x.2 a b)

/-- The associator of the deformed product in internal degree `n`. -/
def μAssoc (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (n : ℕ) (a b c : Λ) : Λ :=
  ∑ y ∈ antidiagonal n, μ y.2 (μ y.1 a b) c - ∑ y ∈ antidiagonal n, μ y.2 a (μ y.1 b c)

/-- **The cocycle identity of the action error**, in every internal degree `j`: the degree-`j`
part of `A(E(m,a,b),c) − E(A(m,a),b,c) + E(m,a⋆b,c) − E(m,a,b⋆c) = −A(m, assoc(a,b,c))`. -/
theorem assocErr_identity (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (j : ℕ)
    (m : M) (a b c : Λ) :
    ∑ x ∈ antidiagonal j, (ν x.1 (assocErr ν μ x.2 m a b) c -
        assocErr ν μ x.2 (ν x.1 m a) b c + assocErr ν μ x.2 m (μ x.1 a b) c -
        assocErr ν μ x.2 m a (μ x.1 b c)) =
      -∑ x ∈ antidiagonal j, ν x.1 m (μAssoc μ x.2 a b c) := by
  have hT1 : ∑ x ∈ antidiagonal j, ν x.1 (assocErr ν μ x.2 m a b) c =
      ∑ t ∈ tri j, ν t.1 (ν t.2.2 (ν t.2.1 m a) b) c -
        ∑ t ∈ tri j, ν t.1 (ν t.2.1 m (μ t.2.2 a b)) c := by
    rw [← sum_ad_ad_right j (fun i u v ↦ ν i (ν v (ν u m a) b) c),
      ← sum_ad_ad_right j (fun i u v ↦ ν i (ν u m (μ v a b)) c), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [assocErr, map_sub, map_sum, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.sum_apply]
  have hT2 : ∑ x ∈ antidiagonal j, assocErr ν μ x.2 (ν x.1 m a) b c =
      ∑ t ∈ tri j, ν t.2.2 (ν t.2.1 (ν t.1 m a) b) c -
        ∑ t ∈ tri j, ν t.2.1 (ν t.1 m a) (μ t.2.2 b c) := by
    rw [← sum_ad_ad_right j (fun i u v ↦ ν v (ν u (ν i m a) b) c),
      ← sum_ad_ad_right j (fun i u v ↦ ν u (ν i m a) (μ v b c)), ← Finset.sum_sub_distrib]
    rfl
  have hT3 : ∑ x ∈ antidiagonal j, assocErr ν μ x.2 m (μ x.1 a b) c =
      ∑ t ∈ tri j, ν t.2.2 (ν t.2.1 m (μ t.1 a b)) c -
        ∑ t ∈ tri j, ν t.2.1 m (μ t.2.2 (μ t.1 a b) c) := by
    rw [← sum_ad_ad_right j (fun i u v ↦ ν v (ν u m (μ i a b)) c),
      ← sum_ad_ad_right j (fun i u v ↦ ν u m (μ v (μ i a b) c)), ← Finset.sum_sub_distrib]
    rfl
  have hT4 : ∑ x ∈ antidiagonal j, assocErr ν μ x.2 m a (μ x.1 b c) =
      ∑ t ∈ tri j, ν t.2.2 (ν t.2.1 m a) (μ t.1 b c) -
        ∑ t ∈ tri j, ν t.2.1 m (μ t.2.2 a (μ t.1 b c)) := by
    rw [← sum_ad_ad_right j (fun i u v ↦ ν v (ν u m a) (μ i b c)),
      ← sum_ad_ad_right j (fun i u v ↦ ν u m (μ v a (μ i b c))), ← Finset.sum_sub_distrib]
    rfl
  have hR : ∑ x ∈ antidiagonal j, ν x.1 m (μAssoc μ x.2 a b c) =
      ∑ t ∈ tri j, ν t.1 m (μ t.2.2 (μ t.2.1 a b) c) -
        ∑ t ∈ tri j, ν t.1 m (μ t.2.2 a (μ t.2.1 b c)) := by
    rw [← sum_ad_ad_right j (fun i u v ↦ ν i m (μ v (μ u a b) c)),
      ← sum_ad_ad_right j (fun i u v ↦ ν i m (μ v a (μ u b c))), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [μAssoc, map_sub, map_sum, map_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, hT1, hT2, hT3, hT4,
    hR]
  -- pair the terms by permuting the triples
  have e1 := sum_tri_cyc' j (fun i u v ↦ ν i (ν v (ν u m a) b) c)
  have e2 := sum_tri_swap13 j (fun i u v ↦ ν i (ν u m (μ v a b)) c)
  have e3 := sum_tri_cyc j (fun i u v ↦ ν u (ν i m a) (μ v b c))
  have e4 := sum_tri_swap12 j (fun i u v ↦ ν i m (μ v (μ u a b) c))
  have e5 := sum_tri_swap12 j (fun i u v ↦ ν i m (μ v a (μ u b c)))
  rw [← e4, ← e5]
  rw [show ∑ t ∈ tri j, ν t.2.2 (ν t.2.1 (ν t.1 m a) b) c =
    ∑ t ∈ tri j, ν t.1 (ν t.2.2 (ν t.2.1 m a) b) c from by rw [← e1]]
  rw [← e2, ← e3]
  abel

theorem assocErr_congr {ν ν' : ℕ → M →ₗ[R] Λ →ₗ[R] M} (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) {n : ℕ}
    (h : ∀ i ≤ n, ν' i = ν i) (m : M) (a b : Λ) :
    assocErr ν' μ n m a b = assocErr ν μ n m a b := by
  unfold assocErr
  congr 1
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [h x.2 (by omega), h x.1 (by omega)]
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [h x.1 (by omega)]

/-- Adding a correction `D` in a positive degree `n` to a family vanishing in degree `n`. -/
theorem assocErr_update {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M} (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) {n : ℕ}
    (hn : 0 < n) (h0 : ν n = 0) (D : M →ₗ[R] Λ →ₗ[R] M) (m : M) (a b : Λ) :
    assocErr (Function.update ν n D) μ n m a b =
      assocErr ν μ n m a b + (D (ν 0 m a) b + ν 0 (D m a) b - D m (μ 0 a b)) := by
  classical
  have hu : ∀ i, Function.update ν n D i = ν i + if i = n then D else 0 := by
    intro i
    by_cases hi : i = n
    · subst hi; rw [Function.update_self, h0, zero_add, if_pos rfl]
    · rw [Function.update_of_ne hi, if_neg hi, add_zero]
  unfold assocErr
  simp only [hu, LinearMap.add_apply, map_add]
  have s1 : ∑ x ∈ antidiagonal n, (if x.2 = n then D else 0) (ν x.1 m a) b = D (ν 0 m a) b := by
    rw [Finset.sum_eq_single (0, n)]
    · simp
    · intro x hx hne
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have : x.2 ≠ n := fun h ↦ hne (Prod.ext (by omega) h)
      simp [this]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  have s2 : ∑ x ∈ antidiagonal n, ν x.2 ((if x.1 = n then D else 0) m a) b = ν 0 (D m a) b := by
    rw [Finset.sum_eq_single (n, 0)]
    · simp
    · intro x hx hne
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have : x.1 ≠ n := fun h ↦ hne (Prod.ext h (by omega))
      simp [this]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  have s3 : ∑ x ∈ antidiagonal n, (if x.2 = n then D else 0) ((if x.1 = n then D else 0) m a) b =
      0 := by
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h1 : x.1 = n
    · have : x.2 ≠ n := by omega
      simp [this]
    · simp [h1]
  have s4 : ∑ x ∈ antidiagonal n, (if x.1 = n then D else 0) m (μ x.2 a b) = D m (μ 0 a b) := by
    rw [Finset.sum_eq_single (n, 0)]
    · simp
    · intro x hx hne
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have : x.1 ≠ n := fun h ↦ hne (Prod.ext h (by omega))
      simp [this]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  simp only [LinearMap.add_apply, Finset.sum_add_distrib, s1, s2, s3, s4]
  abel

variable (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (n : ℕ)

theorem assocErr_add_left (m m' : M) (a b : Λ) :
    assocErr ν μ n (m + m') a b = assocErr ν μ n m a b + assocErr ν μ n m' a b := by
  simp only [assocErr, map_add, LinearMap.add_apply, Finset.sum_add_distrib]; abel

theorem assocErr_add_mid (m : M) (a a' b : Λ) :
    assocErr ν μ n m (a + a') b = assocErr ν μ n m a b + assocErr ν μ n m a' b := by
  simp only [assocErr, map_add, LinearMap.add_apply, Finset.sum_add_distrib]; abel

theorem assocErr_add_right (m : M) (a b b' : Λ) :
    assocErr ν μ n m a (b + b') = assocErr ν μ n m a b + assocErr ν μ n m a b' := by
  simp only [assocErr, map_add, LinearMap.add_apply, Finset.sum_add_distrib]; abel

theorem assocErr_smul_left (c : R) (m : M) (a b : Λ) :
    assocErr ν μ n (c • m) a b = c • assocErr ν μ n m a b := by
  simp only [assocErr, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_sub]

theorem assocErr_smul_mid (c : R) (m : M) (a b : Λ) :
    assocErr ν μ n m (c • a) b = c • assocErr ν μ n m a b := by
  simp only [assocErr, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_sub]

theorem assocErr_smul_right (c : R) (m : M) (a b : Λ) :
    assocErr ν μ n m a (c • b) = c • assocErr ν μ n m a b := by
  simp only [assocErr, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_sub]

/-- The error as a linear map in `m`. -/
def assocErrL (a b : Λ) : M →ₗ[R] M where
  toFun m := assocErr ν μ n m a b
  map_add' m m' := assocErr_add_left ν μ n m m' a b
  map_smul' c m := assocErr_smul_left ν μ n c m a b

/-- The error as a linear map in the first algebra input. -/
def assocErrL₁ (m : M) (b : Λ) : Λ →ₗ[R] M where
  toFun a := assocErr ν μ n m a b
  map_add' a a' := assocErr_add_mid ν μ n m a a' b
  map_smul' c a := assocErr_smul_mid ν μ n c m a b

/-- The error as a linear map in the second algebra input. -/
def assocErrL₂ (m : M) (a : Λ) : Λ →ₗ[R] M where
  toFun b := assocErr ν μ n m a b
  map_add' b b' := assocErr_add_right ν μ n m a b b'
  map_smul' c b := assocErr_smul_right ν μ n c m a b

end Assoc

/-! ### Positive deformations and lifted actions -/

section Lift

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ]

variable (GΛ : GAlg (R := R) Λ) in
/-- **A positive deformation of `Λ` in split form** (Lemma 6.4): the multiplication
`μ₀ + Σ_{q>0} μ_q`, with `μ₀` the product of `Λ` and `μ_q` of internal degree `q`. -/
structure PosDef where
  μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ
  μ_zero : ∀ a b, μ 0 a b = a * b
  deg : ∀ q : ℕ, HDeg GΛ (μ q) q
  assoc : ∀ n a b c, μAssoc μ n a b c = 0
  unit_left : ∀ q : ℕ, 0 < q → ∀ a, μ q 1 a = 0
  unit_right : ∀ q : ℕ, 0 < q → ∀ a, μ q a 1 = 0

variable {GΛ : GAlg (R := R) Λ} {M : Type*} [AddCommGroup M] [Module R M]

/-- A bilinear map `M × Λ → M` raising internal degree by `n`. -/
def IsShift (MM : GMod GΛ M) (n : ℤ) (f : M →ₗ[R] Λ →ₗ[R] M) : Prop :=
  ∀ p q m a, MM.gr.IsHom p m → GΛ.gr.IsHom q a → MM.gr.IsHom (p + q + n) (f m a)

/-- **A filtered lift of the action of `M` to the deformation** (Proposition 6.5(1)):
`m · a = Σ_n ν_n(m, a)` with `ν₀` the given action and the action identity in every internal
degree. -/
structure ActFam (P : PosDef GΛ) (MM : GMod GΛ M) where
  ν : ℕ → M →ₗ[R] Λ →ₗ[R] M
  ν_zero : ∀ m a, ν 0 m a = MM.act m a
  deg : ∀ n : ℕ, IsShift MM n (ν n)
  assoc : ∀ n m a b, assocErr ν P.μ n m a b = 0

variable {MM : GMod GΛ M}

/-- **The error cochain** of a family in internal degree `n`, a bar two-cochain. -/
def errCoch (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (n : ℕ) :
    Bar.Cochain Λ (M →ₗ[R] M) := fun a ↦ assocErrL ν μ n (a 0) (a 1)

theorem errCoch_apply (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (n : ℕ)
    (a : ℕ → Λ) (m : M) : errCoch ν μ n a m = assocErr ν μ n m (a 0) (a 1) := rfl

theorem assocErr_isHom {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M} (hν : ∀ i : ℕ, IsShift MM i (ν i)) (P : PosDef GΛ)
    (n : ℕ) {p q r : ℤ} {m : M} {a b : Λ} (hm : MM.gr.IsHom p m) (ha : GΛ.gr.IsHom q a)
    (hb : GΛ.gr.IsHom r b) : MM.gr.IsHom (p + q + r + n) (assocErr ν P.μ n m a b) := by
  unfold assocErr
  rw [sub_eq_add_neg]
  refine MM.gr.isHom_add (MM.gr.isHom_sum _ _ fun x hx ↦ ?_)
    (MM.gr.isHom_neg (MM.gr.isHom_sum _ _ fun x hx ↦ ?_))
  · have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have := hν x.2 _ _ _ _ (hν x.1 _ _ _ _ hm ha) hb
    convert this using 1
    rw [← hx']; push_cast; ring
  · have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have := hν x.1 _ _ _ _ hm (P.deg x.2 _ _ _ _ ha hb)
    convert this using 1
    rw [← hx']; push_cast; ring

theorem errCoch_good {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M} (hν : ∀ i : ℕ, IsShift MM i (ν i))
    (P : PosDef GΛ) (n : ℕ) : Good MM MM 2 n (errCoch ν P.μ n) where
  tr a := by
    ext m
    simp only [errCoch_apply, Bar.tr_apply_lt (by norm_num : 0 < 2),
      Bar.tr_apply_lt (by norm_num : 1 < 2)]
  add a i x y hi := by
    ext m
    simp only [errCoch_apply, LinearMap.add_apply]
    interval_cases i
    · simp only [Function.update_self, Function.update_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
      exact assocErr_add_mid _ _ _ _ _ _ _
    · simp only [Function.update_self, Function.update_of_ne (by norm_num : (0 : ℕ) ≠ 1)]
      exact assocErr_add_right _ _ _ _ _ _ _
  smul a i c x hi := by
    ext m
    simp only [errCoch_apply, LinearMap.smul_apply]
    interval_cases i
    · simp only [Function.update_self, Function.update_of_ne (by norm_num : (1 : ℕ) ≠ 0)]
      exact assocErr_smul_mid _ _ _ _ _ _ _
    · simp only [Function.update_self, Function.update_of_ne (by norm_num : (0 : ℕ) ≠ 1)]
      exact assocErr_smul_right _ _ _ _ _ _ _
  deg a ds p m ha hm := by
    rw [errCoch_apply]
    have := assocErr_isHom hν P n hm (ha 0 (by norm_num)) (ha 1 (by norm_num))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    convert this using 1
    ring

/-- **The error is a cocycle** once the action identity holds in lower internal degrees. -/
theorem errCoch_d {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M} (hν0 : ∀ m a, ν 0 m a = MM.act m a)
    (P : PosDef GΛ) (n : ℕ) (hlow : ∀ l < n, ∀ m a b, assocErr ν P.μ l m a b = 0) :
    Bar.d (homAct MM MM) 2 (errCoch ν P.μ n) = 0 := by
  funext a
  ext m
  rw [Bar.d_two_apply]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, homAct_l, homAct_r, errCoch_apply,
    Pi.zero_apply, LinearMap.zero_apply]
  have hid := assocErr_identity ν P.μ n m (a 0) (a 1) (a 2)
  rw [Finset.sum_eq_single (0, n)] at hid
  · have hR : ∑ x ∈ antidiagonal n, ν x.1 m (μAssoc P.μ x.2 (a 0) (a 1) (a 2)) = 0 :=
      Finset.sum_eq_zero fun x _ ↦ by rw [P.assoc, map_zero]
    rw [hR, neg_zero] at hid
    simp only [hν0, P.μ_zero] at hid
    simp only [Bar.sh, Bar.ct, Bar.tr]
    norm_num
    rw [← neg_eq_zero, ← hid]
    abel
  · intro x hx hne
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hl : x.2 < n := by
      by_contra h
      exact hne (Prod.ext (by omega) (by omega))
    rw [hlow x.2 hl, hlow x.2 hl, hlow x.2 hl, hlow x.2 hl, map_zero, LinearMap.zero_apply]
    abel
  · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

/-- The bilinear map of a good one-cochain. -/
def cochBil {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] M)} (hF : Good MM MM 1 t F) :
    M →ₗ[R] Λ →ₗ[R] M :=
  LinearMap.mk₂ R (fun m a ↦ F (single a) m) (fun m m' a ↦ map_add _ m m')
    (fun c m a ↦ map_smul _ c m) (fun m a a' ↦ by rw [hF.single_add, LinearMap.add_apply])
    (fun c m a ↦ by rw [hF.single_smul, LinearMap.smul_apply])

theorem cochBil_apply {t : ℤ} {F : Bar.Cochain Λ (M →ₗ[R] M)} (hF : Good MM MM 1 t F) (m : M)
    (a : Λ) : cochBil hF m a = F (single a) m := rfl

variable (P : PosDef GΛ) (MM)

/-- **The degree-by-degree construction** (proof of Proposition 6.5(1)): a family satisfying the
action identity through internal degree `N`, vanishing above `N`. -/
theorem exists_partial (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM MM 1 t) (N : ℕ) :
    ∃ ν : ℕ → M →ₗ[R] Λ →ₗ[R] M, (∀ m a, ν 0 m a = MM.act m a) ∧
      (∀ n : ℕ, IsShift MM n (ν n)) ∧ (∀ n, N < n → ν n = 0) ∧
        ∀ n ≤ N, ∀ m a b, assocErr ν P.μ n m a b = 0 := by
  classical
  induction N with
  | zero =>
    refine ⟨fun n ↦ if n = 0 then MM.act else 0, fun m a ↦ by simp, fun n ↦ ?_,
      fun n hn ↦ by simp [show n ≠ 0 by omega], fun n hn m a b ↦ ?_⟩
    · by_cases hn : n = 0
      · subst hn
        intro p q m a hm ha
        simp only [if_pos rfl, Nat.cast_zero, add_zero]
        exact MM.act_hom _ _ _ _ hm ha
      · intro p q m a _ _
        simp only [if_neg hn, LinearMap.zero_apply]
        exact MM.gr.isHom_zero _
    · obtain rfl : n = 0 := by omega
      simp [assocErr, P.μ_zero, MM.act_mul]
  | succ N ih =>
    obtain ⟨ν, hν0, hν, hνN, hνa⟩ := ih
    obtain ⟨H, hH, hdH⟩ := hExt (N + 1) (by omega) (errCoch ν P.μ (N + 1))
      (errCoch_good hν P (N + 1))
      (errCoch_d hν0 P (N + 1) fun l hl ↦ hνa l (by omega))
    let D : M →ₗ[R] Λ →ₗ[R] M := -cochBil hH
    refine ⟨Function.update ν (N + 1) D, fun m a ↦ ?_, fun n ↦ ?_, fun n hn ↦ ?_,
      fun n hn m a b ↦ ?_⟩
    · rw [Function.update_of_ne (by omega), hν0]
    · by_cases hn : n = N + 1
      · subst hn
        rw [Function.update_self]
        intro p q m a hm ha
        have := hH.deg (single a) (fun _ ↦ q) p m (fun i hi ↦ by
          obtain rfl : i = 0 := by omega
          simpa [single, Bar.cons] using ha) hm
        simp only [Finset.sum_range_one] at this
        simp only [D, LinearMap.neg_apply, cochBil_apply]
        exact MM.gr.isHom_neg (by push_cast at this ⊢; exact this)
      · rw [Function.update_of_ne hn]; exact hν n
    · rw [Function.update_of_ne (by omega), hνN n (by omega)]
    · rcases Nat.lt_or_ge n (N + 1) with hlt | hge
      · rw [assocErr_congr (ν := ν) (ν' := Function.update ν (N + 1) D) P.μ (n := n)
          (fun i hi ↦ Function.update_of_ne (by omega) _ _)]
        exact hνa n (by omega) m a b
      · obtain rfl : n = N + 1 := by omega
        rw [assocErr_update P.μ (by omega) (hνN (N + 1) (by omega)) D]
        have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] M) ↦ G (Bar.cons a (single b)) m)
          hdH
        simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l,
          homAct_r, errCoch_apply] at h1
        rw [hH.one_eq (Bar.sh _), hH.one_eq (Bar.ct 0 _), hH.one_eq (Bar.tr 1 _)] at h1
        simp only [Bar.sh_cons, Bar.ct_zero_cons, Bar.cons_zero, Bar.tr_cons] at h1
        simp only [D, LinearMap.neg_apply, cochBil_apply, map_neg, LinearMap.neg_apply, hν0,
          P.μ_zero]
        simp only [single, Bar.cons_zero, Bar.cons, Bar.sh, Bar.tr] at h1 ⊢
        norm_num at h1 ⊢
        rw [← h1]
        abel

variable {MM}

/-- A trilinear identity holds when it holds on homogeneous inputs. -/
theorem assocErr_eq_zero_of_hom (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (n : ℕ)
    (h : ∀ p q r m a b, MM.gr.IsHom p m → GΛ.gr.IsHom q a → GΛ.gr.IsHom r b →
      assocErr ν μ n m a b = 0) (m : M) (a b : Λ) : assocErr ν μ n m a b = 0 := by
  have h1 : ∀ p m, MM.gr.IsHom p m → ∀ q a, GΛ.gr.IsHom q a → ∀ b,
      assocErr ν μ n m a b = 0 := by
    intro p m hm q a ha b
    have := GΛ.gr.ext_of_hom (f := assocErrL₂ ν μ n m a) (f' := 0)
      (fun r b hb ↦ h p q r m a b hm ha hb)
    exact LinearMap.congr_fun this b
  have h2 : ∀ p m, MM.gr.IsHom p m → ∀ a b, assocErr ν μ n m a b = 0 := by
    intro p m hm a b
    have := GΛ.gr.ext_of_hom (f := assocErrL₁ ν μ n m b) (f' := 0)
      (fun q a ha ↦ h1 p m hm q a ha b)
    exact LinearMap.congr_fun this a
  have := MM.gr.ext_of_hom (f := assocErrL ν μ n a b) (f' := 0) (fun p m hm ↦ h2 p m hm a b)
  exact LinearMap.congr_fun this m

/-- A bound for the internal degrees of `M`. -/
def degBound (g : ZGr (R := R) M) : ℕ := (g.supp.image Int.natAbs).sup id

theorem le_degBound {g : ZGr (R := R) M} {x : ℤ} (hx : x ∈ g.supp) : |x| ≤ degBound g := by
  have : x.natAbs ≤ degBound g :=
    Finset.le_sup (f := id) (Finset.mem_image.2 ⟨x, hx, rfl⟩)
  rw [Int.abs_eq_natAbs]; exact_mod_cast this

variable (MM)

/-- **Proposition 6.5(1), existence**: under `Ext²_Λ(M, M)_t = 0` for `t > 0`, the action of
`M` lifts to the positive deformation. -/
theorem exists_actFam (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q)
    (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM MM 1 t) : Nonempty (ActFam P MM) := by
  obtain ⟨ν, hν0, hν, -, hνa⟩ := exists_partial MM P hExt (2 * degBound MM.gr)
  refine ⟨⟨ν, hν0, hν, fun n m a b ↦ ?_⟩⟩
  rcases Nat.lt_or_ge (2 * degBound MM.gr) n with hn | hn
  · refine assocErr_eq_zero_of_hom (MM := MM) ν P.μ n (fun p q r m a b hm ha hb ↦ ?_) m a b
    by_cases hp : p ∈ MM.gr.supp
    · by_cases hq : q ∈ GΛ.gr.supp
      · by_cases hr : r ∈ GΛ.gr.supp
        · refine MM.gr.eq_zero_of_isHom_out (assocErr_isHom hν P n hm ha hb) fun hmem ↦ ?_
          have h1 := le_degBound hp
          have h2 := le_degBound hmem
          have h3 := hnn q hq
          have h4 := hnn r hr
          rw [abs_le] at h1 h2
          omega
        · rw [GΛ.gr.eq_zero_of_isHom_out hb hr, ← zero_smul R (0 : Λ),
            assocErr_smul_right, zero_smul]
      · rw [GΛ.gr.eq_zero_of_isHom_out ha hq, ← zero_smul R (0 : Λ), assocErr_smul_mid,
          zero_smul]
    · rw [MM.gr.eq_zero_of_isHom_out hm hp]
      simpa using assocErr_smul_left ν P.μ n (0 : R) (0 : M) a b
  · exact hνa n hn m a b

end Lift

/-! ### Lifting maps (Proposition 6.5(1) uniqueness and (2)) -/

section Inter

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **The linearity error of a lifted map in internal degree `n`**:
`Σ_{i+j=n} F_j(ν_i(m,a)) − Σ_{i+j=n} ν'_i(F_j(m), a)`. -/
def interErr (F : ℕ → M →ₗ[R] N) (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N)
    (n : ℕ) (m : M) (a : Λ) : N :=
  ∑ x ∈ antidiagonal n, F x.2 (ν x.1 m a) - ∑ x ∈ antidiagonal n, ν' x.1 (F x.2 m) a

/-- **The cocycle identity of the linearity error.** -/
theorem interErr_identity (F : ℕ → M →ₗ[R] N) (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M)
    (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N) (μ : ℕ → Λ →ₗ[R] Λ →ₗ[R] Λ) (j : ℕ) (m : M) (a b : Λ) :
    ∑ x ∈ antidiagonal j, (interErr F ν ν' x.2 (ν x.1 m a) b - interErr F ν ν' x.2 m (μ x.1 a b) +
        ν' x.1 (interErr F ν ν' x.2 m a) b) =
      ∑ x ∈ antidiagonal j, (F x.1 (assocErr ν μ x.2 m a b) - assocErr ν' μ x.2 (F x.1 m) a b) := by
  have hT1 : ∑ x ∈ antidiagonal j, interErr F ν ν' x.2 (ν x.1 m a) b =
      ∑ t ∈ tri j, F t.2.2 (ν t.2.1 (ν t.1 m a) b) -
        ∑ t ∈ tri j, ν' t.2.1 (F t.2.2 (ν t.1 m a)) b := by
    rw [← sum_ad_ad_right j (fun i u v ↦ F v (ν u (ν i m a) b)),
      ← sum_ad_ad_right j (fun i u v ↦ ν' u (F v (ν i m a)) b), ← Finset.sum_sub_distrib]
    rfl
  have hT2 : ∑ x ∈ antidiagonal j, interErr F ν ν' x.2 m (μ x.1 a b) =
      ∑ t ∈ tri j, F t.2.2 (ν t.2.1 m (μ t.1 a b)) -
        ∑ t ∈ tri j, ν' t.2.1 (F t.2.2 m) (μ t.1 a b) := by
    rw [← sum_ad_ad_right j (fun i u v ↦ F v (ν u m (μ i a b))),
      ← sum_ad_ad_right j (fun i u v ↦ ν' u (F v m) (μ i a b)), ← Finset.sum_sub_distrib]
    rfl
  have hT3 : ∑ x ∈ antidiagonal j, ν' x.1 (interErr F ν ν' x.2 m a) b =
      ∑ t ∈ tri j, ν' t.1 (F t.2.2 (ν t.2.1 m a)) b -
        ∑ t ∈ tri j, ν' t.1 (ν' t.2.1 (F t.2.2 m) a) b := by
    rw [← sum_ad_ad_right j (fun i u v ↦ ν' i (F v (ν u m a)) b),
      ← sum_ad_ad_right j (fun i u v ↦ ν' i (ν' u (F v m) a) b), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [interErr, map_sub, map_sum, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.sum_apply]
  have hR1 : ∑ x ∈ antidiagonal j, F x.1 (assocErr ν μ x.2 m a b) =
      ∑ t ∈ tri j, F t.1 (ν t.2.2 (ν t.2.1 m a) b) -
        ∑ t ∈ tri j, F t.1 (ν t.2.1 m (μ t.2.2 a b)) := by
    rw [← sum_ad_ad_right j (fun i u v ↦ F i (ν v (ν u m a) b)),
      ← sum_ad_ad_right j (fun i u v ↦ F i (ν u m (μ v a b))), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [assocErr, map_sub, map_sum, map_sum]
  have hR2 : ∑ x ∈ antidiagonal j, assocErr ν' μ x.2 (F x.1 m) a b =
      ∑ t ∈ tri j, ν' t.2.2 (ν' t.2.1 (F t.1 m) a) b -
        ∑ t ∈ tri j, ν' t.2.1 (F t.1 m) (μ t.2.2 a b) := by
    rw [← sum_ad_ad_right j (fun i u v ↦ ν' v (ν' u (F i m) a) b),
      ← sum_ad_ad_right j (fun i u v ↦ ν' u (F i m) (μ v a b)), ← Finset.sum_sub_distrib]
    rfl
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hT1, hT2, hT3,
    hR1, hR2]
  have e1 := sum_tri_cyc' j (fun i u v ↦ F i (ν v (ν u m a) b))
  have e2 := sum_tri_swap13 j (fun i u v ↦ F i (ν u m (μ v a b)))
  have e3 := sum_tri_swap12 j (fun i u v ↦ ν' u (F v (ν i m a)) b)
  have e4 := sum_tri_swap13 j (fun i u v ↦ ν' u (F i m) (μ v a b))
  have e5 := sum_tri_swap13 j (fun i u v ↦ ν' v (ν' u (F i m) a) b)
  rw [← e1, ← e2, ← e4, ← e5]
  rw [show ∑ t ∈ tri j, ν' t.1 (F t.2.2 (ν t.2.1 m a)) b =
    ∑ t ∈ tri j, ν' t.2.1 (F t.2.2 (ν t.1 m a)) b from by rw [← e3]]
  abel

theorem interErr_congr {F F' : ℕ → M →ₗ[R] N} (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M)
    (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N) {n : ℕ} (h : ∀ i ≤ n, F' i = F i) (m : M) (a : Λ) :
    interErr F' ν ν' n m a = interErr F ν ν' n m a := by
  unfold interErr
  congr 1
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [h x.2 (by omega)]
  · refine Finset.sum_congr rfl fun x hx ↦ ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [h x.2 (by omega)]

theorem interErr_update {F : ℕ → M →ₗ[R] N} (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M)
    (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N) {n : ℕ} (h0 : F n = 0) (D : M →ₗ[R] N) (m : M) (a : Λ) :
    interErr (Function.update F n D) ν ν' n m a =
      interErr F ν ν' n m a + (D (ν 0 m a) - ν' 0 (D m) a) := by
  classical
  have hu : ∀ i, Function.update F n D i = F i + if i = n then D else 0 := by
    intro i
    by_cases hi : i = n
    · subst hi; rw [Function.update_self, h0, zero_add, if_pos rfl]
    · rw [Function.update_of_ne hi, if_neg hi, add_zero]
  unfold interErr
  simp only [hu, LinearMap.add_apply, map_add]
  have s1 : ∑ x ∈ antidiagonal n, (if x.2 = n then D else 0) (ν x.1 m a) = D (ν 0 m a) := by
    rw [Finset.sum_eq_single (0, n)]
    · simp
    · intro x hx hne
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have : x.2 ≠ n := fun h ↦ hne (Prod.ext (by omega) h)
      simp [this]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  have s2 : ∑ x ∈ antidiagonal n, ν' x.1 ((if x.2 = n then D else 0) m) a = ν' 0 (D m) a := by
    rw [Finset.sum_eq_single (0, n)]
    · simp
    · intro x hx hne
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      have : x.2 ≠ n := fun h ↦ hne (Prod.ext (by omega) h)
      simp [this]
    · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  simp only [LinearMap.add_apply, Finset.sum_add_distrib, s1, s2]
  abel

variable (F : ℕ → M →ₗ[R] N) (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N) (n : ℕ)

/-- The linearity error as a linear map in `m`. -/
def interErrL (a : Λ) : M →ₗ[R] N where
  toFun m := interErr F ν ν' n m a
  map_add' m m' := by
    simp only [interErr, map_add, LinearMap.add_apply, Finset.sum_add_distrib]; abel
  map_smul' c m := by
    simp only [interErr, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_sub,
      RingHom.id_apply]

/-- The linearity error as a linear map in `a`. -/
def interErrL₁ (m : M) : Λ →ₗ[R] N where
  toFun a := interErr F ν ν' n m a
  map_add' a a' := by
    simp only [interErr, map_add, LinearMap.add_apply, Finset.sum_add_distrib]; abel
  map_smul' c a := by
    simp only [interErr, map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_sub,
      RingHom.id_apply]

end Inter

section InterLift

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {MM : GMod GΛ M} {NN : GMod GΛ N}

theorem interErr_eq_zero_of_hom (F : ℕ → M →ₗ[R] N) (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M)
    (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N) (n : ℕ)
    (h : ∀ p q m a, MM.gr.IsHom p m → GΛ.gr.IsHom q a → interErr F ν ν' n m a = 0)
    (m : M) (a : Λ) : interErr F ν ν' n m a = 0 := by
  have h1 : ∀ p m, MM.gr.IsHom p m → ∀ a, interErr F ν ν' n m a = 0 := by
    intro p m hm a
    have := GΛ.gr.ext_of_hom (f := interErrL₁ F ν ν' n m) (f' := 0) (fun q a ha ↦ h p q m a hm ha)
    exact LinearMap.congr_fun this a
  have := MM.gr.ext_of_hom (f := interErrL F ν ν' n a) (f' := 0) (fun p m hm ↦ h1 p m hm a)
  exact LinearMap.congr_fun this m

theorem interErr_isHom {F : ℕ → M →ₗ[R] N} {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M}
    {ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N} {r : ℤ}
    (hF : ∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (F i m))
    (hν : ∀ i : ℕ, IsShift MM i (ν i)) (hν' : ∀ i : ℕ, IsShift NN i (ν' i)) (n : ℕ) {p q : ℤ}
    {m : M} {a : Λ} (hm : MM.gr.IsHom p m) (ha : GΛ.gr.IsHom q a) :
    NN.gr.IsHom (p + q + r + n) (interErr F ν ν' n m a) := by
  unfold interErr
  rw [sub_eq_add_neg]
  refine NN.gr.isHom_add (NN.gr.isHom_sum _ _ fun x hx ↦ ?_)
    (NN.gr.isHom_neg (NN.gr.isHom_sum _ _ fun x hx ↦ ?_))
  · have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have := hF x.2 _ _ (hν x.1 _ _ _ _ hm ha)
    convert this using 1
    rw [← hx']; push_cast; ring
  · have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have := hν' x.1 _ _ _ _ (hF x.2 _ _ hm) ha
    convert this using 1
    rw [← hx']; push_cast; ring

/-- **The linearity error cochain**, a bar one-cochain. -/
def interCoch (F : ℕ → M →ₗ[R] N) (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M) (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N)
    (n : ℕ) : Bar.Cochain Λ (M →ₗ[R] N) := fun a ↦ interErrL F ν ν' n (a 0)

theorem interCoch_apply (F : ℕ → M →ₗ[R] N) (ν : ℕ → M →ₗ[R] Λ →ₗ[R] M)
    (ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N) (n : ℕ) (a : ℕ → Λ) (m : M) :
    interCoch F ν ν' n a m = interErr F ν ν' n m (a 0) := rfl

theorem interCoch_good {F : ℕ → M →ₗ[R] N} {ν : ℕ → M →ₗ[R] Λ →ₗ[R] M}
    {ν' : ℕ → N →ₗ[R] Λ →ₗ[R] N} {r : ℤ}
    (hF : ∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (F i m))
    (hν : ∀ i : ℕ, IsShift MM i (ν i)) (hν' : ∀ i : ℕ, IsShift NN i (ν' i)) (n : ℕ) :
    Good MM NN 1 (r + n) (interCoch F ν ν' n) where
  tr a := by
    ext m
    simp only [interCoch_apply, Bar.tr_apply_lt (by norm_num : 0 < 1)]
  add a i x y hi := by
    ext m
    obtain rfl : i = 0 := by omega
    simp only [interCoch_apply, LinearMap.add_apply, Function.update_self]
    exact (interErrL₁ F ν ν' n m).map_add x y
  smul a i c x hi := by
    ext m
    obtain rfl : i = 0 := by omega
    simp only [interCoch_apply, LinearMap.smul_apply, Function.update_self]
    exact (interErrL₁ F ν ν' n m).map_smul c x
  deg a ds p m ha hm := by
    rw [interCoch_apply]
    have := interErr_isHom hF hν hν' n hm (ha 0 (by norm_num))
    simp only [Finset.sum_range_one]
    convert this using 1
    ring

/-- **The linearity error is a cocycle** once it vanishes in lower internal degrees. -/
theorem interCoch_d (P : PosDef GΛ) (L : ActFam P MM) (L' : ActFam P NN) {F : ℕ → M →ₗ[R] N}
    (n : ℕ) (hlow : ∀ l < n, ∀ m a, interErr F L.ν L'.ν l m a = 0) :
    Bar.d (homAct MM NN) 1 (interCoch F L.ν L'.ν n) = 0 := by
  funext a
  ext m
  rw [Bar.d_one_apply]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, homAct_l, homAct_r, interCoch_apply,
    Pi.zero_apply, LinearMap.zero_apply]
  have hid := interErr_identity F L.ν L'.ν P.μ n m (a 0) (a 1)
  have hR : ∑ x ∈ antidiagonal n, (F x.1 (assocErr L.ν P.μ x.2 m (a 0) (a 1)) -
      assocErr L'.ν P.μ x.2 (F x.1 m) (a 0) (a 1)) = 0 :=
    Finset.sum_eq_zero fun x _ ↦ by rw [L.assoc, L'.assoc, map_zero, sub_zero]
  rw [hR, Finset.sum_eq_single (0, n)] at hid
  · simp only [L.ν_zero, L'.ν_zero, P.μ_zero] at hid
    simp only [Bar.sh, Bar.ct, Bar.tr]
    norm_num
    exact hid
  · intro x hx hne
    have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hl : x.2 < n := by
      by_contra h
      exact hne (Prod.ext (by omega) (by omega))
    rw [hlow x.2 hl, hlow x.2 hl, hlow x.2 hl, map_zero, LinearMap.zero_apply]
    abel
  · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

variable (P : PosDef GΛ) (L : ActFam P MM) (L' : ActFam P NN) {r : ℤ} (f : M →ₗ[R] N)
  (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
  (hfd : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m))

include hf hfd in
/-- **The degree-by-degree lift of a map** (proof of Proposition 6.5(2)). -/
theorem exists_partialMap (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM NN 0 (r + t)) (K : ℕ) :
    ∃ F : ℕ → M →ₗ[R] N, F 0 = f ∧
      (∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (F i m)) ∧
        (∀ n, K < n → F n = 0) ∧ ∀ n ≤ K, ∀ m a, interErr F L.ν L'.ν n m a = 0 := by
  classical
  induction K with
  | zero =>
    refine ⟨fun n ↦ if n = 0 then f else 0, by simp, fun i p m hm ↦ ?_,
      fun n hn ↦ by simp [show n ≠ 0 by omega], fun n hn m a ↦ ?_⟩
    · by_cases hi : i = 0
      · subst hi; simpa using hfd p m hm
      · simp only [if_neg hi, LinearMap.zero_apply]; exact NN.gr.isHom_zero _
    · obtain rfl : n = 0 := by omega
      simp [interErr, L.ν_zero, L'.ν_zero, hf]
  | succ K ih =>
    obtain ⟨F, hF0, hF, hFK, hFa⟩ := ih
    obtain ⟨H, hH, hdH⟩ := hExt (K + 1) (by omega) (interCoch F L.ν L'.ν (K + 1))
      (by simpa using interCoch_good hF L.deg L'.deg (K + 1))
      (interCoch_d P L L' (K + 1) fun l hl ↦ hFa l (by omega))
    let D : M →ₗ[R] N := -H (fun _ ↦ 0)
    have hH0 : ∀ b : ℕ → Λ, H b = H (fun _ ↦ 0) := fun b ↦ by
      rw [hH.tr b]; congr 1
    refine ⟨Function.update F (K + 1) D, by rw [Function.update_of_ne (by omega), hF0],
      fun i p m hm ↦ ?_, fun n hn ↦ ?_, fun n hn m a ↦ ?_⟩
    · by_cases hi : i = K + 1
      · subst hi
        rw [Function.update_self]
        have := hH.deg (fun _ ↦ 0) (fun _ ↦ 0) p m (fun i hi ↦ absurd hi (by omega)) hm
        simp only [Finset.sum_range_zero, add_zero] at this
        simp only [D, LinearMap.neg_apply]
        exact NN.gr.isHom_neg (by push_cast at this ⊢; convert this using 1; ring)
      · rw [Function.update_of_ne hi]; exact hF i p m hm
    · rw [Function.update_of_ne (by omega), hFK n (by omega)]
    · rcases Nat.lt_or_ge n (K + 1) with hlt | hge
      · rw [interErr_congr (F := F) (F' := Function.update F (K + 1) D) L.ν L'.ν (n := n)
          (fun i hi ↦ Function.update_of_ne (by omega) _ _)]
        exact hFa n (by omega) m a
      · obtain rfl : n = K + 1 := by omega
        rw [interErr_update L.ν L'.ν (hFK (K + 1) (by omega)) D]
        have h1 := congrArg (fun G : Bar.Cochain Λ (M →ₗ[R] N) ↦ G (single a) m) hdH
        simp only [Bar.d_zero_apply, LinearMap.sub_apply, homAct_l, homAct_r,
          interCoch_apply] at h1
        rw [hH0 (Bar.sh _), hH0 (Bar.tr 0 _)] at h1
        simp only [D, LinearMap.neg_apply, map_neg, L.ν_zero, L'.ν_zero, LinearMap.neg_apply]
        simp only [single, Bar.cons_zero] at h1
        rw [← h1]
        abel

include hf hfd in
/-- **Proposition 6.5(2), lifts of maps** (and, for `M = N`, `f = id`, the uniqueness of
lifted actions up to a coordinate change `id + (higher)`): a homogeneous `Λ`-linear map of
degree `r` lifts with prescribed leading term, under `Ext¹_Λ(M, N)_{r+t} = 0` for `t > 0`. -/
theorem exists_liftMap (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q)
    (hExt : ∀ t : ℕ, 0 < t → ExtVanish MM NN 0 (r + t)) :
    ∃ F : ℕ → M →ₗ[R] N, F 0 = f ∧
      (∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (F i m)) ∧
        ∀ n m a, interErr F L.ν L'.ν n m a = 0 := by
  obtain ⟨F, hF0, hF, -, hFa⟩ :=
    exists_partialMap P L L' f hf hfd hExt (degBound MM.gr + degBound NN.gr + r.natAbs)
  refine ⟨F, hF0, hF, fun n m a ↦ ?_⟩
  rcases Nat.lt_or_ge (degBound MM.gr + degBound NN.gr + r.natAbs) n with hn | hn
  · refine interErr_eq_zero_of_hom (MM := MM) F L.ν L'.ν n (fun p q m a hm ha ↦ ?_) m a
    by_cases hp : p ∈ MM.gr.supp
    · by_cases hq : q ∈ GΛ.gr.supp
      · refine NN.gr.eq_zero_of_isHom_out (interErr_isHom hF L.deg L'.deg n hm ha) fun hmem ↦ ?_
        have h1 := le_degBound hp
        have h2 := le_degBound hmem
        have h3 := hnn q hq
        rw [abs_le] at h1 h2
        have h4 : (r.natAbs : ℤ) = |r| := Int.natCast_natAbs r
        have h5 := le_abs_self r
        have h6 := neg_abs_le r
        omega
      · rw [GΛ.gr.eq_zero_of_isHom_out ha hq]
        exact (interErrL₁ F L.ν L'.ν n m).map_zero
    · rw [MM.gr.eq_zero_of_isHom_out hm hp]
      exact (interErrL F L.ν L'.ν n a).map_zero
  · exact hFa n hn m a

end InterLift

/-! ### Totals -/

section Totals

variable {X : Type*} [AddCommGroup X]

/-- Summing the degree-`n` identities over all `n` gives the total identity. -/
theorem sum_range_ad (N : ℕ) (g : ℕ → ℕ → X) :
    ∑ n ∈ range N, ∑ x ∈ antidiagonal n, g x.1 x.2 =
      ∑ i ∈ range N, ∑ j ∈ range (N - i), g i j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ (fun i ↦ ∑ j ∈ range (N + 1 - i), g i j)]
    rw [show N + 1 - N = 1 by omega, Finset.sum_range_one]
    have h : ∀ i ∈ range N, ∑ j ∈ range (N + 1 - i), g i j =
        ∑ j ∈ range (N - i), g i j + g i (N - i) := by
      intro i hi
      have hi' := Finset.mem_range.1 hi
      rw [show N + 1 - i = N - i + 1 by omega, Finset.sum_range_succ]
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_range_succ (fun k ↦ g k (N - k))]
    simp only [Nat.sub_self]
    abel

/-- Double sums of a function vanishing outside a box. -/
theorem sum_range_ad_box (A C : ℕ) (g : ℕ → ℕ → X) (hA : ∀ i j, A < i → g i j = 0)
    (hC : ∀ i j, C < j → g i j = 0) :
    ∑ n ∈ range (A + C + 1), ∑ x ∈ antidiagonal n, g x.1 x.2 =
      ∑ i ∈ range (A + 1), ∑ j ∈ range (C + 1), g i j := by
  rw [sum_range_ad]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : A + 1 ≤ A + C + 1))
    (fun i _ hi ↦ Finset.sum_eq_zero fun j _ ↦ hA i j (by simp at hi; omega))]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  rcases Nat.lt_or_ge (A + C + 1 - i) (C + 1) with h | h
  · rw [← Finset.sum_subset (Finset.range_subset_range.2 h.le) (fun j hj hj' ↦ ?_)]
    simp only [Finset.mem_range] at hj hj'
    exact hC i j (by omega)
  · rw [Finset.sum_subset (Finset.range_subset_range.2 h) (fun j hj hj' ↦ ?_)]
    simp only [Finset.mem_range] at hj hj'
    exact hC i j (by omega)

/-- The same, over any longer range. -/
theorem sum_range_ad_box' (A C K : ℕ) (hK : A + C + 1 ≤ K) (g : ℕ → ℕ → X)
    (hA : ∀ i j, A < i → g i j = 0) (hC : ∀ i j, C < j → g i j = 0) :
    ∑ n ∈ range K, ∑ x ∈ antidiagonal n, g x.1 x.2 =
      ∑ i ∈ range (A + 1), ∑ j ∈ range (C + 1), g i j := by
  rw [← sum_range_ad_box A C g hA hC, ← Finset.sum_range_add_sum_Ico _ hK]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun n hn ↦ Finset.sum_eq_zero fun x hx ↦ ?_),
    add_zero]
  have h1 := (Finset.mem_Ico.1 hn).1
  have h2 := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  rcases Nat.lt_or_ge A x.1 with h | h
  · exact hA _ _ h
  · exact hC _ _ (by omega)

end Totals

section TotalAction

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {MM : GMod GΛ M} {NN : GMod GΛ N}

/-- A shift beyond the spread of the degrees of `M` vanishes. -/
theorem shift_eq_zero (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q) {n : ℕ} {f : M →ₗ[R] Λ →ₗ[R] M}
    (hf : IsShift MM n f) (hn : 2 * degBound MM.gr < n) : f = 0 := by
  refine LinearMap.ext fun m ↦ ?_
  have key : ∀ p m, MM.gr.IsHom p m → f m = 0 := by
    intro p m hm
    refine GΛ.gr.ext_of_hom (f := f m) (f' := 0) fun q a ha ↦ ?_
    by_cases hp : p ∈ MM.gr.supp
    · by_cases hq : q ∈ GΛ.gr.supp
      · refine MM.gr.eq_zero_of_isHom_out (hf p q m a hm ha) fun hmem ↦ ?_
        have h1 := le_degBound hp
        have h2 := le_degBound hmem
        have h3 := hnn q hq
        rw [abs_le] at h1 h2
        omega
      · rw [GΛ.gr.eq_zero_of_isHom_out ha hq, map_zero, map_zero]
    · rw [MM.gr.eq_zero_of_isHom_out hm hp, map_zero]
  have := MM.gr.ext_of_hom (f := f) (f' := 0) (fun p m hm ↦ key p m hm)
  rw [this]

variable (P : PosDef GΛ)

/-- **The total lifted action** `m · a = Σ_n ν_n(m, a)`. -/
def ActFam.tot {P : PosDef GΛ} (L : ActFam P MM) : M →ₗ[R] Λ →ₗ[R] M :=
  ∑ n ∈ range (2 * degBound MM.gr + 1), L.ν n

/-- **The total deformed product** `a ⋆ b = Σ_q μ_q(a, b)`. -/
def PosDef.tot : Λ →ₗ[R] Λ →ₗ[R] Λ := ∑ q ∈ range (degBound GΛ.gr + 1), P.μ q

/-- A product of internal degree `q` beyond the degrees of `Λ` vanishes. -/
theorem PosDef.μ_eq_zero (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q) {q : ℕ} (hq : degBound GΛ.gr < q) :
    P.μ q = 0 := by
  refine LinearMap.ext fun a ↦ ?_
  have key : ∀ p a, GΛ.gr.IsHom p a → P.μ q a = 0 := by
    intro p a ha
    refine GΛ.gr.ext_of_hom (f := P.μ q a) (f' := 0) fun p' b hb ↦ ?_
    by_cases hp : p ∈ GΛ.gr.supp
    · by_cases hp' : p' ∈ GΛ.gr.supp
      · refine GΛ.gr.eq_zero_of_isHom_out (P.deg q p p' a b ha hb) fun hmem ↦ ?_
        have h1 := hnn p hp
        have h2 := hnn p' hp'
        have h3 := le_degBound hmem
        rw [abs_le] at h3
        omega
      · rw [GΛ.gr.eq_zero_of_isHom_out hb hp', map_zero, map_zero]
    · rw [GΛ.gr.eq_zero_of_isHom_out ha hp, map_zero]
  exact LinearMap.congr_fun (GΛ.gr.ext_of_hom (f := P.μ q) (f' := 0) key) a

/-- **The total action identity** `(m · a) · b = m · (a ⋆ b)`. -/
theorem ActFam.tot_assoc (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q) {P : PosDef GΛ} (L : ActFam P MM)
    (m : M) (a b : Λ) :
    L.tot (L.tot m a) b = L.tot m (P.tot a b) := by
  set A := 2 * degBound MM.gr
  set C := degBound GΛ.gr
  have hν : ∀ n, A < n → L.ν n = 0 := fun n hn ↦ shift_eq_zero hnn (L.deg n) hn
  have hμ : ∀ q, C < q → P.μ q = 0 := fun q hq ↦ P.μ_eq_zero hnn hq
  set K := A + A + C + 1
  have lhs : L.tot (L.tot m a) b = ∑ n ∈ range K, ∑ x ∈ antidiagonal n,
      L.ν x.2 (L.ν x.1 m a) b := by
    rw [sum_range_ad_box' A A K (by omega) (fun i j ↦ L.ν j (L.ν i m a) b)
      (fun i j hi ↦ by simp only [hν i hi, LinearMap.zero_apply, map_zero])
      (fun i j hj ↦ by simp only [hν j hj, LinearMap.zero_apply])]
    change (∑ n ∈ range (2 * degBound MM.gr + 1), L.ν n)
      ((∑ n ∈ range (2 * degBound MM.gr + 1), L.ν n) m a) b = _
    simp only [LinearMap.sum_apply, map_sum]
    rw [Finset.sum_comm]
  have rhs : L.tot m (P.tot a b) = ∑ n ∈ range K, ∑ x ∈ antidiagonal n,
      L.ν x.1 m (P.μ x.2 a b) := by
    rw [sum_range_ad_box' A C K (by omega) (fun i j ↦ L.ν i m (P.μ j a b))
      (fun i j hi ↦ by simp only [hν i hi, LinearMap.zero_apply])
      (fun i j hj ↦ by simp only [hμ j hj, LinearMap.zero_apply, map_zero])]
    simp only [ActFam.tot, PosDef.tot, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_comm]
  rw [lhs, rhs]
  exact Finset.sum_congr rfl fun n _ ↦ sub_eq_zero.1 (L.assoc n m a b)

/-- The higher terms of a lifted action vanish on `1`. -/
theorem ActFam.ν_one {P : PosDef GΛ} (L : ActFam P MM) :
    ∀ n : ℕ, 0 < n → ∀ m, L.ν n m 1 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn m
    have h := L.assoc n m 1 1
    unfold assocErr at h
    have hl : ∑ x ∈ antidiagonal n, L.ν x.2 (L.ν x.1 m 1) 1 = L.ν n m 1 + L.ν n m 1 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        Finset.sum_range_succ', Finset.sum_eq_zero (fun i hi ↦ ?_)]
      · simp only [Nat.sub_zero, Nat.sub_self, L.ν_zero, MM.act_one, zero_add]
      · have hi' := Finset.mem_range.1 hi
        simp only
        rw [ih (i + 1) (by omega) (by omega), map_zero, LinearMap.zero_apply]
    have hr : ∑ x ∈ antidiagonal n, L.ν x.1 m (P.μ x.2 1 1) = L.ν n m 1 := by
      rw [Finset.sum_eq_single (n, 0)]
      · simp [P.μ_zero]
      · intro x hx hne
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        have h2 : 0 < x.2 := by
          by_contra h0
          exact hne (Prod.ext (by omega) (by omega))
        rw [P.unit_left x.2 h2, map_zero]
      · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
    rw [hl, hr] at h
    simpa using h

/-- **The unit law** `m · 1 = m`. -/
theorem ActFam.tot_one {P : PosDef GΛ} (L : ActFam P MM) (m : M) : L.tot m 1 = m := by
  simp only [ActFam.tot, LinearMap.sum_apply]
  rw [Finset.sum_eq_single 0]
  · rw [L.ν_zero, MM.act_one]
  · intro n _ hn; exact L.ν_one n (by omega) m
  · intro h; exact absurd (Finset.mem_range.2 (by omega)) h

/-! ### Total lifted maps -/

/-- The bound for the terms of a lifted map. -/
def mapBound (MM : GMod GΛ M) (NN : GMod GΛ N) (r : ℤ) : ℕ :=
  degBound MM.gr + degBound NN.gr + r.natAbs

theorem map_eq_zero {r : ℤ} {i : ℕ} {g : M →ₗ[R] N}
    (hg : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (g m))
    (hi : mapBound MM NN r < i) : g = 0 := by
  refine MM.gr.ext_of_hom (f := g) (f' := 0) fun p m hm ↦ ?_
  by_cases hp : p ∈ MM.gr.supp
  · refine NN.gr.eq_zero_of_isHom_out (hg p m hm) fun hmem ↦ ?_
    have h1 := le_degBound hp
    have h2 := le_degBound hmem
    rw [abs_le] at h1 h2
    have h4 : (r.natAbs : ℤ) = |r| := Int.natCast_natAbs r
    have h5 := le_abs_self r
    have h6 := neg_abs_le r
    unfold mapBound at hi
    omega
  · rw [MM.gr.eq_zero_of_isHom_out hm hp, map_zero, map_zero]

/-- The total lifted map `Σ_i F_i`. -/
def mapTot (MM : GMod GΛ M) (NN : GMod GΛ N) (r : ℤ) (F : ℕ → M →ₗ[R] N) : M →ₗ[R] N :=
  ∑ i ∈ range (mapBound MM NN r + 1), F i

/-- **A lifted map is linear for the lifted actions.** -/
theorem mapTot_comm (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q) {P : PosDef GΛ} (L : ActFam P MM)
    (L' : ActFam P NN) {r : ℤ} {F : ℕ → M →ₗ[R] N}
    (hF : ∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r + i) (F i m))
    (hFa : ∀ n m a, interErr F L.ν L'.ν n m a = 0) (m : M) (a : Λ) :
    mapTot MM NN r F (L.tot m a) = L'.tot (mapTot MM NN r F m) a := by
  set A := 2 * degBound MM.gr
  set A' := 2 * degBound NN.gr
  set C := mapBound MM NN r
  have hν : ∀ n, A < n → L.ν n = 0 := fun n hn ↦ shift_eq_zero hnn (L.deg n) hn
  have hν' : ∀ n, A' < n → L'.ν n = 0 := fun n hn ↦ shift_eq_zero hnn (L'.deg n) hn
  have hFz : ∀ i, C < i → F i = 0 := fun i hi ↦ map_eq_zero (hF i) hi
  set K := A + A' + C + 1
  have lhs : mapTot MM NN r F (L.tot m a) = ∑ n ∈ range K, ∑ x ∈ antidiagonal n,
      F x.2 (L.ν x.1 m a) := by
    rw [sum_range_ad_box' A C K (by omega) (fun i j ↦ F j (L.ν i m a))
      (fun i j hi ↦ by simp only [hν i hi, LinearMap.zero_apply, map_zero])
      (fun i j hj ↦ by simp only [hFz j hj, LinearMap.zero_apply])]
    simp only [mapTot, ActFam.tot, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_comm]
  have rhs : L'.tot (mapTot MM NN r F m) a = ∑ n ∈ range K, ∑ x ∈ antidiagonal n,
      L'.ν x.1 (F x.2 m) a := by
    rw [sum_range_ad_box' A' C K (by omega) (fun i j ↦ L'.ν i (F j m) a)
      (fun i j hi ↦ by simp only [hν' i hi, LinearMap.zero_apply])
      (fun i j hj ↦ by simp only [hFz j hj, LinearMap.zero_apply, map_zero])]
    simp only [mapTot, ActFam.tot, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_comm]
  rw [lhs, rhs]
  exact Finset.sum_congr rfl fun n _ ↦ sub_eq_zero.1 (hFa n m a)

/-! ### Maps raising degree -/

/-- `f` raises internal degree by at least `j`. -/
def RaisesBy (MM : GMod GΛ M) (j : ℤ) (f : M →ₗ[R] M) : Prop :=
  ∀ p m, MM.gr.IsHom p m → ∀ d, d < p + j → MM.gr.proj d (f m) = 0

theorem RaisesBy.comp {j j' : ℤ} {f g : M →ₗ[R] M} (hf : RaisesBy MM j f) (hg : RaisesBy MM j' g) :
    RaisesBy MM (j + j') (g ∘ₗ f) := by
  intro p m hm e he
  rw [LinearMap.comp_apply, MM.gr.sum (f m), map_sum, map_sum]
  refine Finset.sum_eq_zero fun d _ ↦ ?_
  by_cases hd : d < p + j
  · rw [hf p m hm d hd, map_zero, map_zero]
  · exact hg d _ (MM.gr.isHom_proj d (f m)) e (by omega)

theorem RaisesBy.eq_zero {k : ℤ} {f : M →ₗ[R] M} (hf : RaisesBy MM k f)
    (hk : 2 * (degBound MM.gr : ℤ) < k) : f = 0 := by
  refine MM.gr.ext_of_hom (f := f) (f' := 0) fun p m hm ↦ ?_
  by_cases hp : p ∈ MM.gr.supp
  · rw [MM.gr.sum (f m), LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun d hd ↦ hf p m hm d ?_
    have h1 := le_degBound hp
    have h2 := le_degBound hd
    rw [abs_le] at h1 h2
    omega
  · rw [MM.gr.eq_zero_of_isHom_out hm hp, map_zero, map_zero]

theorem RaisesBy.pow {f : M →ₗ[R] M} (hf : RaisesBy MM 1 f) :
    ∀ k : ℕ, RaisesBy MM k (f ^ k) := by
  intro k
  induction k with
  | zero =>
    intro p m hm d hd
    rw [pow_zero, Module.End.one_apply, MM.gr.proj_of_isHom hm, if_neg (by omega)]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_eq_comp]
    have := RaisesBy.comp hf ih
    rw [show (1 : ℤ) + k = ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
    exact this

theorem RaisesBy.isNilpotent {f : M →ₗ[R] M} (hf : RaisesBy MM 1 f) : IsNilpotent f :=
  ⟨2 * degBound MM.gr + 1, (hf.pow _).eq_zero (by push_cast; omega)⟩

/-- **The coordinate change of a lifted identity is invertible.** -/
theorem mapTot_bijective {F : ℕ → M →ₗ[R] M} (hF0 : F 0 = LinearMap.id)
    (hF : ∀ i : ℕ, ∀ p m, MM.gr.IsHom p m → MM.gr.IsHom (p + 0 + i) (F i m)) :
    Function.Bijective (mapTot MM MM 0 F) := by
  set K := mapBound MM MM 0
  have hsplit : mapTot MM MM 0 F = 1 + ∑ i ∈ Finset.Ico 1 (K + 1), F i := by
    rw [mapTot, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hF0]
    rfl
  have hN : RaisesBy MM 1 (∑ i ∈ Finset.Ico 1 (K + 1), F i) := by
    intro p m hm d hd
    rw [LinearMap.sum_apply, map_sum]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hi' := (Finset.mem_Ico.1 hi).1
    rw [MM.gr.proj_of_isHom (hF i p m hm), if_neg (by omega)]
  rw [← Module.End.isUnit_iff, hsplit]
  exact hN.isNilpotent.isUnit_one_add

/-! ### Leading terms of filtered maps -/

/-- A map `M → N` of filtration order at least `r`. -/
def OrderGe (MM : GMod GΛ M) (NN : GMod GΛ N) (r : ℤ) (g : M →ₗ[R] N) : Prop :=
  ∀ p m, MM.gr.IsHom p m → ∀ d, d < p + r → NN.gr.proj d (g m) = 0

/-- **The leading term of a filtered map of the lifts is `Λ`-linear** (proof of
Proposition 6.5(2): "the leading term of a nonzero filtered map is a homogeneous `Λ`-linear map
of the same degree"). -/
theorem leading_linear (hnn : ∀ q ∈ GΛ.gr.supp, 0 ≤ q) {P : PosDef GΛ} (L : ActFam P MM)
    (L' : ActFam P NN) {r : ℤ} {g : M →ₗ[R] N} (hg : ∀ m a, g (L.tot m a) = L'.tot (g m) a)
    (hord : OrderGe MM NN r g) (m : M) (a : Λ) :
    ZGr.comp MM.gr NN.gr r g (MM.act m a) = NN.act (ZGr.comp MM.gr NN.gr r g m) a := by
  -- reduce to homogeneous inputs
  let φ₁ : M →ₗ[R] Λ →ₗ[R] N := LinearMap.mk₂ R
    (fun m a ↦ ZGr.comp MM.gr NN.gr r g (MM.act m a) - NN.act (ZGr.comp MM.gr NN.gr r g m) a)
    (fun m m' a ↦ by simp only [map_add, LinearMap.add_apply]; abel)
    (fun c m a ↦ by simp only [map_smul, LinearMap.smul_apply, smul_sub])
    (fun m a a' ↦ by simp only [map_add, LinearMap.add_apply]; abel)
    (fun c m a ↦ by simp only [map_smul, LinearMap.smul_apply, smul_sub])
  suffices h : φ₁ = 0 by
    have := LinearMap.congr_fun (LinearMap.congr_fun h m) a
    simpa [φ₁, sub_eq_zero] using this
  refine MM.gr.ext_of_hom (f := φ₁) (f' := 0) fun p m hm ↦ ?_
  refine GΛ.gr.ext_of_hom (f := φ₁ m) (f' := 0) fun q a ha ↦ ?_
  simp only [φ₁, LinearMap.mk₂_apply, LinearMap.zero_apply, sub_eq_zero]
  have hA := hg m a
  have hproj := congrArg (NN.gr.proj (p + q + r)) hA
  -- left side: only `ν₀` contributes
  have hl : NN.gr.proj (p + q + r) (g (L.tot m a)) =
      ZGr.comp MM.gr NN.gr r g (MM.act m a) := by
    rw [ZGr.comp_hom MM.gr NN.gr g (MM.act_hom _ _ _ _ hm ha)]
    simp only [ActFam.tot, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_eq_single 0]
    · rw [L.ν_zero]
    · intro n _ hn
      exact hord _ _ (L.deg n p q m a hm ha) _ (by omega)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  -- right side: only `ν'₀` and the degree-`p + r` part of `g m` contribute
  have hr : NN.gr.proj (p + q + r) (L'.tot (g m) a) =
      NN.act (ZGr.comp MM.gr NN.gr r g m) a := by
    rw [ZGr.comp_hom MM.gr NN.gr g hm]
    have hn0 : ∀ n : ℕ, 0 < n → NN.gr.proj (p + q + r) (L'.ν n (g m) a) = 0 := by
      intro n hn
      rw [NN.gr.sum (g m), map_sum, LinearMap.sum_apply, map_sum]
      refine Finset.sum_eq_zero fun d _ ↦ ?_
      by_cases hd : d < p + r
      · rw [hord p m hm d hd, map_zero, LinearMap.zero_apply, map_zero]
      · rw [NN.gr.proj_of_isHom (L'.deg n d q _ a (NN.gr.isHom_proj d (g m)) ha), if_neg (by omega)]
    simp only [ActFam.tot, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_eq_single 0 (fun n _ hn ↦ hn0 n (by omega))
      (fun h ↦ absurd (Finset.mem_range.2 (by omega)) h)]
    rw [L'.ν_zero, show p + q + r = p + r + q by ring, proj_act NN ha]
  rw [← hl, ← hr, hproj]

end TotalAction

end GExt

end MultiplicativeBasisDeformations
