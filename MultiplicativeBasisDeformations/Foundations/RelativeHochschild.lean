import MultiplicativeBasisDeformations.Foundations.FamilyNormalization

/-!
# Relative cochains compute ordinary Hochschild cohomology in degree two

`weights-and-parameters.tex:325–328`: "we use normalized cochains relative to the split vertex
algebra […] these relative cochains compute ordinary Hochschild cohomology." The formalization
works with normalized `S`-relative cochains (`IsRel₁`, `IsRel₂`). This file proves the claim for
`HH²(Λ)_q`, the only Hochschild group the paper uses:

* every Hochschild two-cocycle of internal degree `q` is cohomologous, by a degree-`q` coboundary,
  to a normalized `S`-relative one (`exists_rel_cohomologous`);
* a normalized `S`-relative two-cochain that is the coboundary of some degree-`q` one-cochain is
  the coboundary of a normalized `S`-relative one (`exists_rel_of_cobdry`).

So the relative classes are exactly the ordinary classes. In particular the spanning condition on
`HH²(Λ)_{>0}` (Theorem 7.7, Proposition 7.6) reads the same in both forms (`span_rel_iff`; the
hypotheses of Theorem 7.7 in the ordinary form give `FamilyHyp`, `familyHyp_of_ordinary`), and so
does the nonvanishing of a class (`rel_isCobdry_iff`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

universe u v

namespace LenGrading

variable {k : Type u} [Field k] {Λ : Type v} [Ring Λ] [Algebra k Λ] {G : LenGrading k Λ}
  (V : Vertices G)

/-! ### Small lemmas -/

theorem isHom_add' {d : ℕ} {a b : Λ} (ha : G.IsHom d a) (hb : G.IsHom d b) : G.IsHom d (a + b) := by
  unfold IsHom at *; rw [map_add, ha, hb]

theorem isHom_sub' {d : ℕ} {a b : Λ} (ha : G.IsHom d a) (hb : G.IsHom d b) : G.IsHom d (a - b) := by
  unfold IsHom at *; rw [map_sub, ha, hb]

theorem isHom_smul' {d : ℕ} (c : k) {a : Λ} (ha : G.IsHom d a) : G.IsHom d (c • a) := by
  unfold IsHom at *; rw [map_smul, ha]

theorem isCocycle_cobdry (f : Λ →ₗ[k] Λ) : IsCocycle₂ (cobdry k f) := by
  intro a b c
  simp only [cobdry_apply, mul_add, mul_sub, add_mul, sub_mul, mul_assoc]
  abel

theorem isCocycle_sub {μ ν : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsCocycle₂ μ) (hν : IsCocycle₂ ν) :
    IsCocycle₂ (μ - ν) := by
  intro a b c
  have h1 := hμ a b c
  have h2 := hν a b c
  simp only [LinearMap.sub_apply, mul_sub, sub_mul]
  rw [← sub_eq_zero.mpr (show a * μ b c - μ (a * b) c + μ a (b * c) - μ a b * c =
    a * ν b c - ν (a * b) c + ν a (b * c) - ν a b * c by rw [h1, h2])]
  abel

theorem cobdry_add' (f g : Λ →ₗ[k] Λ) : cobdry k (f + g) = cobdry k f + cobdry k g := by
  ext a b; simp only [cobdry_apply, LinearMap.add_apply, mul_add, add_mul]; abel

theorem cobdry_sub' (f g : Λ →ₗ[k] Λ) : cobdry k (f - g) = cobdry k f - cobdry k g := by
  ext a b; simp only [cobdry_apply, LinearMap.sub_apply, mul_sub, sub_mul]; abel

theorem hasDeg₂_cobdry {q : ℕ} {f : Λ →ₗ[k] Λ} (hf : HasDeg₁ G q f) : HasDeg₂ G q (cobdry k f) := by
  intro d e a b ha hb
  rw [cobdry_apply]
  refine isHom_add' (isHom_sub' ?_ ?_) ?_
  · have := G.isHom_mul ha (hf e b hb); rwa [← add_assoc] at this
  · exact hf _ _ (G.isHom_mul ha hb)
  · have := G.isHom_mul (hf d a ha) hb; rwa [add_right_comm] at this

theorem hasDeg₂_sub {q : ℕ} {μ ν : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : HasDeg₂ G q μ) (hν : HasDeg₂ G q ν) :
    HasDeg₂ G q (μ - ν) := fun d e a b ha hb ↦ isHom_sub' (hμ d e a b ha hb) (hν d e a b ha hb)

theorem hasDeg₁_add {q : ℕ} {f g : Λ →ₗ[k] Λ} (hf : HasDeg₁ G q f) (hg : HasDeg₁ G q g) :
    HasDeg₁ G q (f + g) := fun d a ha ↦ isHom_add' (hf d a ha) (hg d a ha)

theorem hasDeg₁_sub {q : ℕ} {f g : Λ →ₗ[k] Λ} (hf : HasDeg₁ G q f) (hg : HasDeg₁ G q g) :
    HasDeg₁ G q (f - g) := fun d a ha ↦ isHom_sub' (hf d a ha) (hg d a ha)

theorem ee (i j : Fin V.n) : V.e i * V.e j = if i = j then V.e i else 0 := by
  split_ifs with h
  · subst h; exact (V.complete.idem i).eq
  · exact V.complete.ortho h

theorem sum_e_mul (x : Λ) : ∑ i, V.e i * x = x := by
  rw [← Finset.sum_mul, V.complete.complete, one_mul]

theorem sum_mul_e (x : Λ) : ∑ i, x * V.e i = x := by
  rw [← Finset.mul_sum, V.complete.complete, mul_one]

/-- A cocycle vanishing when either argument is a vertex is normalized `S`-relative. -/
theorem isRel₂_of_unit {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsCocycle₂ μ) (hL : ∀ i b, μ (V.e i) b = 0)
    (hR : ∀ i a, μ a (V.e i) = 0) : IsRel₂ V μ where
  left i a b := by
    have := hμ (V.e i) a b
    rw [hL, hL, zero_mul] at this
    rw [eq_comm, ← sub_eq_zero, ← this]; abel
  mid i a b := by
    have := hμ a (V.e i) b
    rw [hL, hR, mul_zero, zero_mul] at this
    rw [eq_comm, ← sub_eq_zero, ← this]; abel
  right i a b := by
    have := hμ a b (V.e i)
    rw [hR, hR, mul_zero] at this
    rw [← sub_eq_zero, ← this]; abel
  unitL := hL
  unitR := hR

/-! ### Cocycles -/

/-- `f₁(a) = Σ_i e_i μ(e_i, a)`. -/
def f₁ (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Λ →ₗ[k] Λ := ∑ i, LinearMap.mulLeft k (V.e i) ∘ₗ μ (V.e i)

theorem f₁_apply (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) (a : Λ) : f₁ V μ a = ∑ i, V.e i * μ (V.e i) a := by
  simp [f₁, LinearMap.sum_apply]

/-- `f₂(a) = Σ_i μ(a, e_i) e_i`. -/
def f₂ (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) : Λ →ₗ[k] Λ := ∑ i, LinearMap.mulRight k (V.e i) ∘ₗ μ.flip (V.e i)

theorem f₂_apply (μ : Λ →ₗ[k] Λ →ₗ[k] Λ) (a : Λ) : f₂ V μ a = ∑ i, μ a (V.e i) * V.e i := by
  simp [f₂, LinearMap.sum_apply]

/-- After subtracting `d f₁`, a cocycle vanishes when its first argument is a vertex. -/
theorem left_unit {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsCocycle₂ μ) (j : Fin V.n) (b : Λ) :
    (μ - cobdry k (f₁ V μ)) (V.e j) b = 0 := by
  classical
  -- `Σ_i e_i · dμ(e_i, e_j, b) = 0`
  have hs : ∑ i, V.e i * (V.e i * μ (V.e j) b - μ (V.e i * V.e j) b + μ (V.e i) (V.e j * b) -
      μ (V.e i) (V.e j) * b) = 0 := Finset.sum_eq_zero fun i _ ↦ by rw [hμ, mul_zero]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
  have h1 : ∑ i, V.e i * (V.e i * μ (V.e j) b) = μ (V.e j) b := by
    simp only [← mul_assoc, (V.complete.idem _).eq]; exact sum_e_mul V _
  have h2 : ∑ i, V.e i * μ (V.e i * V.e j) b = V.e j * μ (V.e j) b := by
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [ee, if_neg hij, map_zero,
      LinearMap.zero_apply, mul_zero]) (by simp), ee, if_pos rfl]
  have h3 : ∑ i, V.e i * (μ (V.e i) (V.e j) * b) = f₁ V μ (V.e j) * b := by
    rw [f₁_apply, Finset.sum_mul]; simp only [mul_assoc]
  have h4 : V.e j * f₁ V μ b = V.e j * μ (V.e j) b := by
    rw [f₁_apply, Finset.mul_sum, Finset.sum_eq_single j (fun i _ hij ↦ by
      rw [← mul_assoc, ee, if_neg (Ne.symm hij), zero_mul]) (by simp), ← mul_assoc,
      (V.complete.idem j).eq]
  rw [h1, h2, h3, ← f₁_apply] at hs
  rw [LinearMap.sub_apply, LinearMap.sub_apply, cobdry_apply, h4]
  rw [← hs]; abel

/-- After subtracting `d f₂`, a cocycle that vanishes at a left vertex also vanishes at a right
vertex, and still at a left vertex. -/
theorem right_unit {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsCocycle₂ μ) (hL : ∀ i b, μ (V.e i) b = 0) :
    (∀ i b, (μ - cobdry k (f₂ V μ)) (V.e i) b = 0) ∧
      ∀ j a, (μ - cobdry k (f₂ V μ)) a (V.e j) = 0 := by
  classical
  have hf2e : ∀ j, f₂ V μ (V.e j) = 0 := fun j ↦ by
    rw [f₂_apply]; exact Finset.sum_eq_zero fun i _ ↦ by rw [hL, zero_mul]
  constructor
  · intro j b
    rw [LinearMap.sub_apply, LinearMap.sub_apply, cobdry_apply, hf2e, zero_mul, add_zero, hL,
      f₂_apply, f₂_apply, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_zero fun i _ ↦ ?_]
    · simp
    have := hμ (V.e j) b (V.e i)
    rw [hL, hL, zero_mul, sub_zero, add_zero, sub_eq_zero] at this
    rw [← mul_assoc, this, sub_self]
  · intro j a
    -- `Σ_i dμ(a, e_j, e_i) · e_i = 0`
    have hs : ∑ i, (a * μ (V.e j) (V.e i) - μ (a * V.e j) (V.e i) + μ a (V.e j * V.e i) -
        μ a (V.e j) * V.e i) * V.e i = 0 := Finset.sum_eq_zero fun i _ ↦ by rw [hμ, zero_mul]
    simp only [hL, mul_zero, zero_sub, add_mul, sub_mul, neg_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
    have h1 : ∑ i, μ (a * V.e j) (V.e i) * V.e i = f₂ V μ (a * V.e j) := (f₂_apply V μ _).symm
    have h2 : ∑ i, μ a (V.e j * V.e i) * V.e i = μ a (V.e j) * V.e j := by
      rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [ee, if_neg (Ne.symm hij), map_zero,
        zero_mul]) (by simp), ee, if_pos rfl]
    have h3 : ∑ i, μ a (V.e j) * V.e i * V.e i = μ a (V.e j) := by
      simp only [mul_assoc, (V.complete.idem _).eq]; exact sum_mul_e V _
    have h4 : f₂ V μ a * V.e j = μ a (V.e j) * V.e j := by
      rw [f₂_apply, Finset.sum_mul, Finset.sum_eq_single j (fun i _ hij ↦ by
        rw [mul_assoc, ee, if_neg hij, mul_zero]) (by simp), mul_assoc, (V.complete.idem j).eq]
    rw [h1, h2, h3] at hs
    rw [LinearMap.sub_apply, LinearMap.sub_apply, cobdry_apply, hf2e, mul_zero, h4]
    have hs' : μ a (V.e j) * V.e j - f₂ V μ (a * V.e j) - μ a (V.e j) = 0 := by
      rw [← hs]; abel
    rw [show ∀ X Y Z : Λ, X - (0 - Y + Z) = -(Z - Y - X) from fun X Y Z ↦ by abel, hs', neg_zero]

/-- **Every Hochschild two-cocycle of internal degree `q` is cohomologous to a normalized
`S`-relative one**, by the coboundary of a degree-`q` one-cochain. -/
theorem exists_rel_cohomologous {q : ℕ} {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsCocycle₂ μ)
    (hd : HasDeg₂ G q μ) :
    ∃ f : Λ →ₗ[k] Λ, HasDeg₁ G q f ∧ IsRel₂ V (μ - cobdry k f) := by
  set μ₁ := μ - cobdry k (f₁ V μ)
  have hc₁ : IsCocycle₂ μ₁ := isCocycle_sub hμ (isCocycle_cobdry _)
  have hL₁ : ∀ i b, μ₁ (V.e i) b = 0 := left_unit V hμ
  have hdf₁ : HasDeg₁ G q (f₁ V μ) := fun d a ha ↦ by
    rw [f₁_apply]
    refine G.isHom_sum _ _ fun i _ ↦ ?_
    have := G.isHom_mul (V.deg0 i) (hd 0 d _ _ (V.deg0 i) ha)
    simpa using this
  have hd₁ : HasDeg₂ G q μ₁ := hasDeg₂_sub hd (hasDeg₂_cobdry hdf₁)
  have hdf₂ : HasDeg₁ G q (f₂ V μ₁) := fun d a ha ↦ by
    rw [f₂_apply]
    refine G.isHom_sum _ _ fun i _ ↦ ?_
    have := G.isHom_mul (hd₁ d 0 _ _ ha (V.deg0 i)) (V.deg0 i)
    simpa using this
  obtain ⟨hL₂, hR₂⟩ := right_unit V hc₁ hL₁
  refine ⟨f₁ V μ + f₂ V μ₁, hasDeg₁_add hdf₁ hdf₂, ?_⟩
  have e : μ - cobdry k (f₁ V μ + f₂ V μ₁) = μ₁ - cobdry k (f₂ V μ₁) := by
    show μ - cobdry k (f₁ V μ + f₂ V μ₁) = (μ - cobdry k (f₁ V μ)) - cobdry k (f₂ V μ₁)
    rw [cobdry_add']; abel
  rw [e]
  exact isRel₂_of_unit V (isCocycle_sub hc₁ (isCocycle_cobdry _)) hL₂ hR₂

/-! ### Coboundaries -/

/-- **A normalized `S`-relative coboundary is the coboundary of a normalized `S`-relative
one-cochain** of the same degree. -/
theorem exists_rel_of_cobdry {q : ℕ} {ν : Λ →ₗ[k] Λ →ₗ[k] Λ} (hν : IsRel₂ V ν)
    {f : Λ →ₗ[k] Λ} (hf : HasDeg₁ G q f) (hνf : ν = cobdry k f) :
    ∃ f' : Λ →ₗ[k] Λ, IsRel₁ V f' ∧ HasDeg₁ G q f' ∧ ν = cobdry k f' := by
  classical
  set x := ∑ j, V.e j * f (V.e j)
  -- the inner derivation `D(a) = a x - x a`
  set D : Λ →ₗ[k] Λ := LinearMap.mulRight k x - LinearMap.mulLeft k x
  have hD : ∀ a, D a = a * x - x * a := fun a ↦ rfl
  have hdD : cobdry k D = 0 := by
    ext a b; simp only [cobdry_apply, hD, LinearMap.zero_apply, mul_sub, sub_mul, mul_assoc]; abel
  -- `D(e_i) = f(e_i)`
  have hDe : ∀ i, D (V.e i) = f (V.e i) := by
    intro i
    have hs : ∑ j, V.e j * (V.e j * f (V.e i) - f (V.e j * V.e i) + f (V.e j) * V.e i) = 0 :=
      Finset.sum_eq_zero fun j _ ↦ by
        have := hν.unitL j (V.e i)
        rw [hνf, cobdry_apply] at this
        rw [this, mul_zero]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hs
    have h1 : ∑ j, V.e j * (V.e j * f (V.e i)) = f (V.e i) := by
      simp only [← mul_assoc, (V.complete.idem _).eq]; exact sum_e_mul V _
    have h2 : ∑ j, V.e j * f (V.e j * V.e i) = V.e i * f (V.e i) := by
      rw [Finset.sum_eq_single i (fun j _ hji ↦ by rw [ee, if_neg hji, map_zero, mul_zero])
        (by simp), ee, if_pos rfl]
    have h3 : ∑ j, V.e j * (f (V.e j) * V.e i) = x * V.e i := by
      rw [Finset.sum_mul]; simp only [mul_assoc]
    have h4 : V.e i * x = V.e i * f (V.e i) := by
      rw [Finset.mul_sum, Finset.sum_eq_single i (fun j _ hji ↦ by
        rw [← mul_assoc, ee, if_neg (Ne.symm hji), zero_mul]) (by simp), ← mul_assoc,
        (V.complete.idem i).eq]
    rw [h1, h2, h3] at hs
    rw [hD, h4]
    have hx : x * V.e i = V.e i * f (V.e i) - f (V.e i) :=
      eq_of_sub_eq_zero (by rw [← hs]; abel)
    rw [hx]; abel
  set f' := f - D
  have hf'e : ∀ i, f' (V.e i) = 0 := fun i ↦ by
    simp only [f', LinearMap.sub_apply, hDe, sub_self]
  have hνf' : ν = cobdry k f' := by rw [hνf, cobdry_sub', hdD]; exact (sub_zero (cobdry k f)).symm
  refine ⟨f', ⟨fun i a ↦ ?_, fun i a ↦ ?_, hf'e⟩, hasDeg₁_sub hf (fun d a ha ↦ ?_), hνf'⟩
  · have := hν.unitL i a
    rw [hνf', cobdry_apply, hf'e, zero_mul, add_zero, sub_eq_zero] at this
    exact this.symm
  · have := hν.unitR i a
    rw [hνf', cobdry_apply, hf'e, mul_zero, zero_sub, neg_add_eq_sub, sub_eq_zero] at this
    exact this.symm
  · have hx : G.IsHom q x := G.isHom_sum _ _ fun j _ ↦ by
      have := G.isHom_mul (V.deg0 j) (hf 0 _ (V.deg0 j)); simpa using this
    rw [hD]
    refine isHom_sub' (G.isHom_mul ha hx) ?_
    have := G.isHom_mul hx ha; rwa [add_comm] at this

/-! ### Consequences -/

theorem IsRel₂.sub' {μ ν : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsRel₂ V μ) (hν : IsRel₂ V ν) :
    IsRel₂ V (μ - ν) where
  left i a b := by simp [hμ.left, hν.left, mul_sub]
  mid i a b := by simp [hμ.mid, hν.mid]
  right i a b := by simp [hμ.right, hν.right, sub_mul]
  unitL i b := by simp [hμ.unitL, hν.unitL]
  unitR i a := by simp [hμ.unitR, hν.unitR]

theorem IsRel₂.zero' : IsRel₂ V (0 : Λ →ₗ[k] Λ →ₗ[k] Λ) where
  left i a b := by simp
  mid i a b := by simp
  right i a b := by simp
  unitL i b := by simp
  unitR i a := by simp

theorem IsRel₂.add' {μ ν : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsRel₂ V μ) (hν : IsRel₂ V ν) :
    IsRel₂ V (μ + ν) where
  left i a b := by simp [hμ.left, hν.left, mul_add]
  mid i a b := by simp [hμ.mid, hν.mid]
  right i a b := by simp [hμ.right, hν.right, add_mul]
  unitL i b := by simp [hμ.unitL, hν.unitL]
  unitR i a := by simp [hμ.unitR, hν.unitR]

theorem IsRel₂.smul' (c : k) {μ : Λ →ₗ[k] Λ →ₗ[k] Λ} (hμ : IsRel₂ V μ) : IsRel₂ V (c • μ) where
  left i a b := by simp [hμ.left]
  mid i a b := by simp [hμ.mid]
  right i a b := by simp [hμ.right]
  unitL i b := by simp [hμ.unitL]
  unitR i a := by simp [hμ.unitR]

theorem IsRel₂.sum' {ι : Type*} (s : Finset ι) (μ : ι → Λ →ₗ[k] Λ →ₗ[k] Λ)
    (h : ∀ i ∈ s, IsRel₂ V (μ i)) : IsRel₂ V (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsRel₂.zero' V
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add' V (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- **A normalized `S`-relative two-cochain is a relative coboundary iff it is an ordinary
coboundary** (in internal degree `q`): the nonvanishing of a class reads the same in both forms. -/
theorem rel_isCobdry_iff {q : ℕ} {ν : Λ →ₗ[k] Λ →ₗ[k] Λ} (hν : IsRel₂ V ν) :
    (∃ f, IsRel₁ V f ∧ HasDeg₁ G q f ∧ ν = cobdry k f) ↔ ∃ f, HasDeg₁ G q f ∧ ν = cobdry k f :=
  ⟨fun ⟨f, _, hf, h⟩ ↦ ⟨f, hf, h⟩, fun ⟨_, hf, h⟩ ↦ exists_rel_of_cobdry V hν hf h⟩

/-- **The spanning condition on `HH²(Λ)_q` reads the same with relative and with ordinary
cochains**, for normalized `S`-relative `μ_i`. -/
theorem span_rel_iff {n : ℕ} (μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ) (qd : Fin n → ℕ)
    (hμ : ∀ i, IsRel₂ V (μ i)) (q : ℕ) :
    (∀ φ, IsRel₂ V φ → HasDeg₂ G q φ → IsCocycle₂ φ →
      ∃ (c : Fin n → k) (f : Λ →ₗ[k] Λ), IsRel₁ V f ∧ HasDeg₁ G q f ∧
        φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i) + cobdry k f) ↔
    (∀ φ, HasDeg₂ G q φ → IsCocycle₂ φ →
      ∃ (c : Fin n → k) (f : Λ →ₗ[k] Λ), HasDeg₁ G q f ∧
        φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i) + cobdry k f) := by
  constructor
  · intro h φ hd hc
    obtain ⟨f₀, hf₀, hrel⟩ := exists_rel_cohomologous V hc hd
    obtain ⟨c, f, -, hf, he⟩ := h _ hrel (hasDeg₂_sub hd (hasDeg₂_cobdry hf₀))
      (isCocycle_sub hc (isCocycle_cobdry _))
    refine ⟨c, f₀ + f, hasDeg₁_add hf₀ hf, ?_⟩
    ext a b
    have h2 := LinearMap.congr_fun (LinearMap.congr_fun he a) b
    simp only [LinearMap.sub_apply, LinearMap.add_apply, cobdry_add'] at h2 ⊢
    rw [eq_add_of_sub_eq h2]; abel
  · intro h φ hrel hd hc
    obtain ⟨c, f, hf, he⟩ := h φ hd hc
    set S := ∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i
    have hS : IsRel₂ V S := IsRel₂.sum' V _ _ fun i _ ↦ (hμ i).smul' V (c i)
    obtain ⟨f', hf'r, hf', hν⟩ := exists_rel_of_cobdry V (hrel.sub' V hS) hf
      (by rw [he]; abel)
    exact ⟨c, f', hf'r, hf', by rw [← hν]; abel⟩

/-- **The hypotheses of Theorem 7.7 with `HH²` as ordinary Hochschild cohomology**: if the `μ_i`
are normalized `S`-relative of positive degrees, `m + Σ t_i μ_i` is associative, and their classes
span the ordinary `HH²(Λ)_q` for every `q > 0`, then `FamilyHyp` holds. -/
theorem familyHyp_of_ordinary {n : ℕ} {μ : Fin n → Λ →ₗ[k] Λ →ₗ[k] Λ} {qd : Fin n → ℕ}
    (pos : ∀ i, 0 < qd i) (rel : ∀ i, IsRel₂ V (μ i)) (deg : ∀ i, HasDeg₂ G (qd i) (μ i))
    (assoc : ∀ (lam : Fin n → k) (a b c : Λ),
      mLam μ lam (mLam μ lam a b) c = mLam μ lam a (mLam μ lam b c))
    (span : ∀ q, 0 < q → ∀ φ, HasDeg₂ G q φ → IsCocycle₂ φ →
      ∃ (c : Fin n → k) (f : Λ →ₗ[k] Λ), HasDeg₁ G q f ∧
        φ = (∑ i ∈ Finset.univ.filter (fun i ↦ qd i = q), c i • μ i) + cobdry k f) :
    FamilyHyp V μ qd :=
  ⟨pos, rel, deg, assoc, fun q hq ↦ (span_rel_iff V μ qd rel q).2 (span q hq)⟩

end LenGrading

end MultiplicativeBasisDeformations
