import MultiplicativeBasisDeformations.Foundations.PositiveDeformation

/-!
# Normalized relative Hochschild cochains

For a length-graded algebra `Λ` with vertex idempotents `e_i` spanning
`S = Λ₀`: normalized `S`-relative one- and two-cochains of internal degree `q`,
the coboundary `df(a,b) = af(b) - f(ab) + f(a)b`
(`characteristic-two-construction.tex:46`) and the cocycle equation
`dμ(a,b,c) = aμ(b,c) - μ(ab,c) + μ(a,bc) - μ(a,b)c = 0`
(`binary-families.tex:48`). Classes in `HH²(Λ)_q` are cocycles of degree `q`
modulo coboundaries of degree-`q` one-cochains.

Also: a degree calculus for maps raising the length grading (`Raises₁`,
`Raises₂`) used by the normalization arguments.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  (V : Vertices G)

/-- A normalized `S`-relative one-cochain. -/
structure IsRel₁ (f : Λ →ₗ[k] Λ) : Prop where
  left : ∀ i a, f (V.e i * a) = V.e i * f a
  right : ∀ i a, f (a * V.e i) = f a * V.e i
  unit : ∀ i, f (V.e i) = 0

/-- A normalized `S`-relative two-cochain. -/
structure IsRel₂ (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Prop where
  left : ∀ i a b, μ (V.e i * a) b = V.e i * μ a b
  mid : ∀ i a b, μ (a * V.e i) b = μ a (V.e i * b)
  right : ∀ i a b, μ a (b * V.e i) = μ a b * V.e i
  unitL : ∀ i b, μ (V.e i) b = 0
  unitR : ∀ i a, μ a (V.e i) = 0

variable (G) in
/-- A one-cochain of internal degree `q`. -/
def HasDeg₁ (q : ℕ) (f : Λ →ₗ[k] Λ) : Prop := ∀ d a, G.IsHom d a → G.IsHom (d + q) (f a)

variable (G) in
/-- A two-cochain of internal degree `q`. -/
def HasDeg₂ (q : ℕ) (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Prop :=
  ∀ d e a b, G.IsHom d a → G.IsHom e b → G.IsHom (d + e + q) (μ a b)

/-- The Hochschild cocycle equation. -/
def IsCocycle₂ (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Prop :=
  ∀ a b c : Λ, a * μ b c - μ (a * b) c + μ a (b * c) - μ a b * c = 0

variable (k) in
/-- The coboundary `df(a,b) = a f(b) - f(ab) + f(a) b`. -/
def cobdry (f : Λ →ₗ[k] Λ) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  LinearMap.mk₂ k (fun a b ↦ a * f b - f (a * b) + f a * b)
    (fun a a' b ↦ by simp only [add_mul, map_add]; abel)
    (fun c a b ↦ by simp only [smul_mul_assoc, map_smul, smul_sub, smul_add])
    (fun a b b' ↦ by simp only [mul_add, map_add]; abel)
    (fun c a b ↦ by simp only [mul_smul_comm, map_smul, smul_sub, smul_add])

theorem cobdry_apply (f : Λ →ₗ[k] Λ) (a b : Λ) :
    cobdry k f a b = a * f b - f (a * b) + f a * b := rfl

/-! ### Degree calculus -/

variable (G) in
/-- A one-cochain raising degree by at least `q`. -/
def Raises₁ (q : ℕ) (f : Λ →ₗ[k] Λ) : Prop := ∀ d a, G.IsHom d a → G.Ge (d + q) (f a)

variable (G) in
/-- A two-cochain raising total degree by at least `q`. -/
def Raises₂ (q : ℕ) (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Prop :=
  ∀ d e a b, G.IsHom d a → G.IsHom e b → G.Ge (d + e + q) (μ a b)

theorem ge_sum {m : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Λ) (h : ∀ i ∈ s, G.Ge m (f i)) :
    G.Ge m (∑ i ∈ s, f i) := fun d hd ↦ by
  rw [map_sum]; exact Finset.sum_eq_zero fun i hi ↦ h i hi d hd

theorem ge_neg {m : ℕ} {a : Λ} (ha : G.Ge m a) : G.Ge m (-a) := fun d hd ↦ by
  rw [map_neg, ha d hd, neg_zero]

theorem ge_sub {m : ℕ} {a b : Λ} (ha : G.Ge m a) (hb : G.Ge m b) : G.Ge m (a - b) := by
  rw [sub_eq_add_neg]; exact G.ge_add ha (ge_neg hb)

theorem ge_zero' (m : ℕ) : G.Ge m (0 : Λ) := fun _ _ ↦ map_zero _

theorem Raises₁.ge {q : ℕ} {f : Λ →ₗ[k] Λ} (hf : Raises₁ G q f) {d : ℕ} {a : Λ} (ha : G.Ge d a) :
    G.Ge (d + q) (f a) := by
  rw [G.eq_sum_proj_of_ge ha, map_sum]
  exact ge_sum _ _ fun e he ↦ G.ge_mono (by have := (Finset.mem_Ico.1 he).1; omega)
    (hf e _ (G.isHom_proj e a))

theorem Raises₂.ge {q : ℕ} {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : Raises₂ G q μ) {d e : ℕ} {a b : Λ}
    (ha : G.Ge d a) (hb : G.Ge e b) : G.Ge (d + e + q) (μ a b) := by
  rw [G.eq_sum_proj_of_ge ha, G.eq_sum_proj_of_ge hb]
  simp only [map_sum, LinearMap.sum_apply]
  refine ge_sum _ _ fun d' hd' ↦ ge_sum _ _ fun e' he' ↦ ?_
  have h1 := (Finset.mem_Ico.1 hd').1
  have h2 := (Finset.mem_Ico.1 he').1
  exact G.ge_mono (by omega) (hμ _ _ _ _ (G.isHom_proj _ a) (G.isHom_proj _ b))

theorem HasDeg₁.raises {q : ℕ} {f : Λ →ₗ[k] Λ} (hf : HasDeg₁ G q f) : Raises₁ G q f :=
  fun d a ha ↦ G.ge_of_isHom (hf d a ha)

theorem HasDeg₂.raises {q : ℕ} {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : HasDeg₂ G q μ) : Raises₂ G q μ :=
  fun d e a b ha hb ↦ G.ge_of_isHom (hμ d e a b ha hb)

theorem Raises₂.mono {q q' : ℕ} {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : Raises₂ G q μ) (h : q' ≤ q) :
    Raises₂ G q' μ := fun d e a b ha hb ↦ G.ge_mono (by omega) (hμ d e a b ha hb)

theorem raises_mul : Raises₂ G 0 (LinearMap.mul k Λ) := fun d e a b ha hb ↦ by
  simpa using G.ge_of_isHom (G.isHom_mul ha hb)

/-- A bilinear map vanishing in degrees `< d + e + q` on homogeneous inputs of
large degree is zero. -/
theorem eq_zero_of_raises {q : ℕ} {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : Raises₂ G q μ) (hq : G.N ≤ q)
    (a b : Λ) : μ a b = 0 := by
  have := hμ.ge (G.ge_zero a) (G.ge_zero b)
  exact G.eq_zero_of_ge this (by omega)

/-- The degree-`(d+e+q)` component of `μ` on homogeneous inputs. -/
def degPart (q : ℕ) (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Λ →ₗ[k] Λ →ₗ[k] Λ :=
  ∑ d ∈ Finset.range G.N, ∑ e ∈ Finset.range G.N,
    (LinearMap.compr₂ μ (G.proj (d + e + q))).compl₁₂ (G.proj d) (G.proj e)

theorem degPart_hom {q d e : ℕ} (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) {a b : Λ} (ha : G.IsHom d a)
    (hb : G.IsHom e b) : degPart (G := G) q μ a b = G.proj (d + e + q) (μ a b) := by
  classical
  simp only [degPart, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply]
  by_cases hd : d < G.N
  · by_cases he : e < G.N
    · rw [Finset.sum_eq_single d, Finset.sum_eq_single e]
      · rw [ha, hb]
      · intro e' _ he'
        rw [G.proj_of_isHom hb, if_neg (Ne.symm he'), map_zero, map_zero]
      · intro h; exact absurd (Finset.mem_range.2 he) h
      · intro d' _ hd'
        refine Finset.sum_eq_zero fun e' _ ↦ ?_
        rw [G.proj_of_isHom ha, if_neg (Ne.symm hd'), map_zero, LinearMap.zero_apply, map_zero]
      · intro h; exact absurd (Finset.mem_range.2 hd) h
    · rw [G.isHom_zero_of_ge hb (by omega), map_zero, map_zero]
      simp
  · rw [G.isHom_zero_of_ge ha (by omega), map_zero, LinearMap.zero_apply, map_zero]
    simp

theorem degPart_hasDeg (q : ℕ) (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : HasDeg₂ G q (degPart (G := G) q μ) :=
  fun d e a b ha hb ↦ by rw [degPart_hom μ ha hb]; exact G.isHom_proj _ _

theorem sub_degPart {q : ℕ} {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : Raises₂ G q μ) :
    Raises₂ G (q + 1) (μ - degPart (G := G) q μ) := fun d e a b ha hb ↦ by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, degPart_hom μ ha hb]
  have := G.ge_sub_proj (hμ d e a b ha hb)
  rwa [show d + e + q + 1 = d + e + (q + 1) by omega] at this

end LenGrading

end MultiplicativeBasisDeformations
