import MultiplicativeBasisDeformations.Foundations.SquareZero

/-!
# Lemma 6.6 for graded `Λ_μ`-modules

`lem:square-zero-selected-lifts`: "Put `Λ_μ = (Λ ⊗_R R[ε]/(ε²), m + εμ)`, with `deg ε = −q`.
Then each `M_i` has a graded lift to `Λ_μ` that is free over `R[ε]/(ε²)`, unique up to a graded
isomorphism reducing to the identity. Every homogeneous original map lifts."

`SquareZero.lean` records lifts by their first-order equations (`ActLift`, `IsLiftHom`). Here a
graded lift is a graded `Λ_μ`-module in the literal sense (`MuMod`): an `R`-module `L` with
`ε` of degree `−q`, `ε² = 0`, and an action of `Λ` (the elements `a + 0ε` of `Λ_μ`) commuting
with `ε`, with `(l a) b = l(ab) + ε l μ(a, b)` (the product of `Λ_μ`); free over `R[ε]/(ε²)`
(`ker ε = im ε`), with a graded `Λ`-linear identification `L/εL = M`. An `ActLift` gives the lift
`M ⊕ εM` (`ActLift.toMuMod`); conversely, a graded section of `L → M` identifies any such `L`
with the lift of an `ActLift` (`MuMod.exists_model`), which gives existence (`exists_muMod`),
uniqueness up to a graded isomorphism reducing to the identity (`muMod_unique`) and the lifting
of maps (`muMod_mapLift`) in this form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MultiplicativeBasisDeformations

namespace GExt

variable {R : Type*} [CommRing R] {Λ : Type*} [Ring Λ] [Algebra R Λ] {GΛ : GAlg (R := R) Λ}
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {μ : Λ →ₗ[R] Λ →ₗ[R] Λ} {q : ℤ} {MM : GMod GΛ M} {NN : GMod GΛ N}

/-! ### Lifted actions from bilinear maps -/

/-- **An `ActLift` from its bilinear correction** `ν(m, a)`, homogeneous of degree `q` and
satisfying `ν(ma, b) − ν(m, ab) + ν(m, a)b = mμ(a, b)`. -/
def ActLift.ofEq (ν : M →ₗ[R] Λ →ₗ[R] M)
    (hdeg : ∀ p d m a, MM.gr.IsHom p m → GΛ.gr.IsHom d a → MM.gr.IsHom (p + d + q) (ν m a))
    (heq : ∀ m a b, ν (MM.act m a) b - ν m (a * b) + MM.act (ν m a) b = MM.act m (μ a b)) :
    ActLift μ q MM where
  ν a := ν.flip (a 0)
  good := ⟨fun a ↦ by simp [Bar.tr], fun a i x y hi ↦ by
      obtain rfl : i = 0 := by omega
      ext m; simp,
    fun a i c x hi ↦ by
      obtain rfl : i = 0 := by omega
      ext m; simp,
    fun a ds p m ha hm ↦ by
      simpa using hdeg p (ds 0) m (a 0) hm (ha 0 (by norm_num))⟩
  eq := by
    funext a
    ext m
    simp only [Bar.d_one_apply, LinearMap.add_apply, LinearMap.sub_apply, homAct_l, homAct_r,
      muCochain_apply, LinearMap.flip_apply, LinearMap.comp_apply]
    simp only [Bar.sh, Bar.ct, Bar.tr]
    norm_num
    have := heq m (a 0) (a 1)
    rw [← this]

theorem ActLift.ofEq_act (ν : M →ₗ[R] Λ →ₗ[R] M) hdeg heq (m : M) (a : Λ) :
    (ActLift.ofEq (μ := μ) (q := q) (MM := MM) ν hdeg heq).act m a = ν m a := rfl

/-! ### Graded `Λ_μ`-modules -/

variable (μ q MM) in
/-- **A graded lift of `M` to `Λ_μ`, free over `R[ε]/(ε²)`**: `ε` of degree `−q` with `ε² = 0`,
an action of `Λ ⊂ Λ_μ` commuting with `ε` with `(l a) b = l(ab) + ε l μ(a, b)` (the product
`a ⋆ b = ab + εμ(a, b)` of `Λ_μ`), `ker ε = im ε`, and a graded `Λ`-linear surjection
`red : L → M` with kernel `εL`. -/
structure MuMod (L : Type*) [AddCommGroup L] [Module R L] where
  ε : L →ₗ[R] L
  ε_ε : ∀ l, ε (ε l) = 0
  act : L →ₗ[R] Λ →ₗ[R] L
  act_ε : ∀ l a, act (ε l) a = ε (act l a)
  act_one : ∀ l, act l 1 = l
  act_mul : ∀ l a b, act (act l a) b = act l (a * b) + ε (act l (μ a b))
  gr : ZGr (R := R) L
  ε_hom : ∀ p l, gr.IsHom p l → gr.IsHom (p - q) (ε l)
  act_hom : ∀ p d l a, gr.IsHom p l → GΛ.gr.IsHom d a → gr.IsHom (p + d) (act l a)
  free : ∀ l, ε l = 0 → ∃ l', l = ε l'
  red : L →ₗ[R] M
  red_surj : Function.Surjective red
  red_ker : ∀ l, red l = 0 ↔ ∃ l', l = ε l'
  red_hom : ∀ p l, gr.IsHom p l → MM.gr.IsHom p (red l)
  red_act : ∀ l a, red (act l a) = MM.act (red l) a

/-! ### The lift `M ⊕ εM` of an `ActLift` -/

/-- **The lift of an `ActLift`**: `M ⊕ εM` as `M × M` (first coordinate the `ε`-part, of degree
shifted by `q`), with `ε(n, m) = (m, 0)` and `(n, m) a = (na + ν(m, a), ma)`. -/
def ActLift.toMuMod (L₀ : ActLift μ q MM) (h11 : μ 1 1 = 0) : MuMod μ q MM (M × M) where
  ε := LinearMap.inl R M M ∘ₗ LinearMap.snd R M M
  ε_ε l := by simp
  act := LinearMap.mk₂ R (fun x a ↦ (MM.act x.1 a + L₀.act x.2 a, MM.act x.2 a))
    (fun x x' a ↦ by
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply, L₀.act_add]
      ext <;> simp; abel)
    (fun c x a ↦ by
      ext <;> simp [ActLift.act])
    (fun x a a' ↦ by ext <;> simp [L₀.act_add']; abel)
    (fun c x a ↦ by ext <;> simp [ActLift.act, L₀.good.single_smul])
  act_ε l a := by ext <;> simp
  act_one l := by
    have h := L₀.equation l.2 1 1
    rw [MM.act_one, mul_one, sub_self, zero_add, MM.act_one, h11, map_zero] at h
    ext <;> simp [h, MM.act_one]
  act_mul l a b := by
    have h := L₀.equation l.2 a b
    ext
    · simp only [LinearMap.mk₂_apply, map_add, LinearMap.add_apply, MM.act_mul,
        LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.inl_apply, Prod.fst_add]
      rw [← h]; abel
    · simp [MM.act_mul]
  gr := twistGr (MM := MM) (NN := MM) q
  ε_hom p l hl := by
    rw [twistGr_isHom (MM := MM) (NN := MM)] at hl ⊢
    simp only [LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.inl_apply]
    exact ⟨by rw [sub_add_cancel]; exact hl.2, MM.gr.isHom_zero _⟩
  act_hom p d l a hl ha := by
    rw [twistGr_isHom (MM := MM) (NN := MM)] at hl ⊢
    simp only [LinearMap.mk₂_apply]
    refine ⟨MM.gr.isHom_add ?_ ?_, MM.act_hom _ _ _ _ hl.2 ha⟩
    · have := MM.act_hom _ _ _ _ hl.1 ha
      rwa [show p + q + d = p + d + q by ring] at this
    · exact L₀.act_deg hl.2 ha
  free l hl := by
    have h2 : l.2 = 0 := by
      have := congrArg Prod.fst hl
      simpa using this
    exact ⟨(0, l.1), by ext <;> simp [h2]⟩
  red := LinearMap.snd R M M
  red_surj m := ⟨(0, m), rfl⟩
  red_ker l := by
    constructor
    · intro h
      have h' : l.2 = 0 := h
      exact ⟨(0, l.1), by ext <;> simp [h']⟩
    · rintro ⟨l', rfl⟩; simp
  red_hom p l hl := ((twistGr_isHom (MM := MM) (NN := MM)).1 hl).2
  red_act l a := rfl

/-! ### Graded sections and the model of a lift -/

theorem ZGr.map_proj {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (gX : ZGr (R := R) X) (gY : ZGr (R := R) Y) (f : X →ₗ[R] Y)
    (hf : ∀ p x, gX.IsHom p x → gY.IsHom p (f x)) (p : ℤ) (x : X) :
    f (gX.proj p x) = gY.proj p (f x) := by
  conv_rhs => rw [gX.sum x]
  rw [map_sum, map_sum, Finset.sum_eq_single p]
  · exact (hf p _ (gX.isHom_proj p x)).symm
  · intro e _ he; rw [gY.proj_of_isHom (hf e _ (gX.isHom_proj e x)), if_neg he]
  · intro hp; rw [gX.proj_out p hp]; simp

theorem ZGr.mem_range_proj {X : Type*} [AddCommGroup X] [Module R X] (g : ZGr (R := R) X)
    {p : ℤ} {x : X} : x ∈ LinearMap.range (g.proj p) ↔ g.IsHom p x :=
  ⟨fun ⟨y, hy⟩ ↦ hy ▸ g.isHom_proj p y, fun h ↦ ⟨x, h⟩⟩

namespace MuMod

variable {L : Type*} [AddCommGroup L] [Module R L] (X : MuMod μ q MM L)

theorem red_ε (l : L) : X.red (X.ε l) = 0 := (X.red_ker _).2 ⟨l, rfl⟩

theorem red_proj (p : ℤ) (l : L) : X.red (X.gr.proj p l) = MM.gr.proj p (X.red l) :=
  ZGr.map_proj X.gr MM.gr X.red X.red_hom p l

/-- **A graded section** of `red : L → M`, when the graded pieces of `M` are projective. -/
theorem exists_section (hproj : ∀ p, Module.Projective R (LinearMap.range (MM.gr.proj p))) :
    ∃ s : M →ₗ[R] L, (∀ m, X.red (s m) = m) ∧ ∀ p m, MM.gr.IsHom p m → X.gr.IsHom p (s m) := by
  classical
  have hp : ∀ p, ∃ h : LinearMap.range (MM.gr.proj p) →ₗ[R] LinearMap.range (X.gr.proj p),
      ∀ y, X.red (h y) = y := by
    intro p
    let f : LinearMap.range (X.gr.proj p) →ₗ[R] LinearMap.range (MM.gr.proj p) :=
      LinearMap.codRestrict _ (X.red ∘ₗ (LinearMap.range (X.gr.proj p)).subtype) fun l ↦
        (ZGr.mem_range_proj MM.gr).2 (X.red_hom p _ ((ZGr.mem_range_proj X.gr).1 l.2))
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨l, rfl⟩ := X.red_surj y
      refine ⟨⟨X.gr.proj p l, LinearMap.mem_range_self _ _⟩, Subtype.ext ?_⟩
      change X.red (X.gr.proj p l) = X.red l
      rw [X.red_proj]; exact (ZGr.mem_range_proj MM.gr).1 hy
    obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
    exact ⟨h, fun y ↦ congrArg Subtype.val (LinearMap.congr_fun hh y)⟩
  choose h hh using hp
  refine ⟨∑ p ∈ MM.gr.supp, (LinearMap.range (X.gr.proj p)).subtype ∘ₗ h p ∘ₗ
      (MM.gr.proj p).rangeRestrict, fun m ↦ ?_, fun p m hm ↦ ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Submodule.subtype_apply]
    conv_rhs => rw [MM.gr.sum m]
    exact Finset.sum_congr rfl fun p _ ↦ hh p _
  · simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    refine X.gr.isHom_sum _ _ fun e _ ↦ ?_
    by_cases he : e = p
    · subst he; exact (ZGr.mem_range_proj X.gr).1 (h e _).2
    · have : (MM.gr.proj e).rangeRestrict m = 0 :=
        Subtype.ext (by rw [LinearMap.codRestrict_apply, MM.gr.proj_of_isHom hm, if_neg (Ne.symm he)]; rfl)
      rw [this, map_zero]; exact X.gr.isHom_zero _

variable {s : M →ₗ[R] L} (hs : ∀ m, X.red (s m) = m)
  (hsh : ∀ p m, MM.gr.IsHom p m → X.gr.IsHom p (s m))

/-- `M ⊕ εM → L`, `(n, m) ↦ s m + ε s n`. -/
def Ψ (s : M →ₗ[R] L) : M × M →ₗ[R] L :=
  s ∘ₗ LinearMap.snd R M M + X.ε ∘ₗ s ∘ₗ LinearMap.fst R M M

theorem Ψ_apply (x : M × M) : X.Ψ s x = s x.2 + X.ε (s x.1) := rfl

include hs in
theorem red_Ψ (x : M × M) : X.red (X.Ψ s x) = x.2 := by
  rw [Ψ_apply, map_add, X.red_ε, add_zero, hs]

include hs in
theorem ε_eq (l : L) : X.ε l = X.ε (s (X.red l)) := by
  obtain ⟨l', hl'⟩ := (X.red_ker (l - s (X.red l))).1 (by rw [map_sub, hs, sub_self])
  rw [← sub_eq_zero, ← map_sub, hl', X.ε_ε]

include hs in
theorem Ψ_bijective : Function.Bijective (X.Ψ s) := by
  refine ⟨fun x y h ↦ ?_, fun l ↦ ?_⟩
  · rw [← sub_eq_zero, ← map_sub] at h
    set z := x - y
    have h2 : z.2 = 0 := by rw [← X.red_Ψ hs z, h, map_zero]
    have h1 : X.ε (s z.1) = 0 := by rw [← h, Ψ_apply, h2, map_zero, zero_add]
    obtain ⟨l', hl'⟩ := X.free _ h1
    have h1' : z.1 = 0 := by rw [← hs z.1, hl', X.red_ε]
    exact sub_eq_zero.1 (Prod.ext h1' h2)
  · obtain ⟨l₁, hl₁⟩ := (X.red_ker (l - s (X.red l))).1 (by rw [map_sub, hs, sub_self])
    refine ⟨(X.red l₁, X.red l), ?_⟩
    rw [Ψ_apply, ← X.ε_eq hs, ← hl₁, add_sub_cancel]

/-- `Ψ` as a linear isomorphism. -/
def Ψe : (M × M) ≃ₗ[R] L := LinearEquiv.ofBijective (X.Ψ s) (X.Ψ_bijective hs)

theorem Ψe_apply (x : M × M) : X.Ψe hs x = X.Ψ s x := rfl

include hsh in
theorem Ψ_hom {p : ℤ} {x : M × M} (hx : (twistGr (MM := MM) (NN := MM) q).IsHom p x) :
    X.gr.IsHom p (X.Ψ s x) := by
  rw [twistGr_isHom] at hx
  refine X.gr.isHom_add (hsh p _ hx.2) ?_
  have := X.ε_hom _ _ (hsh _ _ hx.1)
  rwa [add_sub_cancel_right] at this

include hsh in
theorem Ψ_symm_hom {p : ℤ} {l : L} (hl : X.gr.IsHom p l) :
    (twistGr (MM := MM) (NN := MM) q).IsHom p ((X.Ψe hs).symm l) := by
  set x := (X.Ψe hs).symm l
  have hx : X.Ψ s x = l := (X.Ψe hs).apply_symm_apply l
  have hmap := ZGr.map_proj (twistGr (MM := MM) (NN := MM) q) X.gr (X.Ψ s)
    (fun p x hx ↦ X.Ψ_hom hsh hx) p x
  rw [hx, hl, ← hx] at hmap
  exact (X.Ψe hs).injective hmap

/-- The correction `ν(m, a)` of the lift `L`, read off through `Ψ`. -/
def νb (s : M →ₗ[R] L) (hs : ∀ m, X.red (s m) = m) : M →ₗ[R] Λ →ₗ[R] M :=
  (X.act ∘ₗ s).compr₂ (LinearMap.fst R M M ∘ₗ (X.Ψe hs).symm.toLinearMap)

theorem Ψ_symm_act (m : M) (a : Λ) :
    (X.Ψe hs).symm (X.act (s m) a) = (X.νb s hs m a, MM.act m a) := by
  refine Prod.ext rfl ?_
  have := X.red_Ψ hs ((X.Ψe hs).symm (X.act (s m) a))
  rw [← X.Ψe_apply hs, LinearEquiv.apply_symm_apply, X.red_act, hs] at this
  exact this.symm

theorem Ψ_symm_ε (l : L) : (X.Ψe hs).symm (X.ε l) = (X.red l, 0) := by
  rw [LinearEquiv.symm_apply_eq, Ψe_apply, Ψ_apply, map_zero, zero_add, ← X.ε_eq hs]

theorem act_Ψ (x : M × M) (a : Λ) :
    X.act (X.Ψ s x) a = X.Ψ s (MM.act x.1 a + X.νb s hs x.2 a, MM.act x.2 a) := by
  have h1 : X.act (s x.2) a = X.Ψ s (X.νb s hs x.2 a, MM.act x.2 a) := by
    rw [← X.Ψe_apply hs, ← X.Ψ_symm_act hs, LinearEquiv.apply_symm_apply]
  have h2 : X.ε (X.act (s x.1) a) = X.Ψ s (MM.act x.1 a, 0) := by
    have := X.Ψ_symm_ε hs (X.act (s x.1) a)
    rw [X.red_act, hs] at this
    rw [← this, ← X.Ψe_apply hs, LinearEquiv.apply_symm_apply]
  rw [Ψ_apply, map_add, LinearMap.add_apply, X.act_ε, h1, h2, ← map_add]
  congr 1
  ext <;> simp [add_comm]

include hsh in
theorem νb_deg (p d : ℤ) (m : M) (a : Λ) (hm : MM.gr.IsHom p m) (ha : GΛ.gr.IsHom d a) :
    MM.gr.IsHom (p + d + q) (X.νb s hs m a) := by
  have h := X.Ψ_symm_hom (hs := hs) (hsh := hsh) (X.act_hom p d _ a (hsh p m hm) ha)
  rw [X.Ψ_symm_act hs, twistGr_isHom] at h
  exact h.1

theorem νb_eq (m : M) (a b : Λ) :
    X.νb s hs (MM.act m a) b - X.νb s hs m (a * b) + MM.act (X.νb s hs m a) b =
      MM.act m (μ a b) := by
  have h := X.act_mul (s m) a b
  have h1 : X.act (s m) a = X.Ψ s (X.νb s hs m a, MM.act m a) := by
    rw [← X.Ψe_apply hs, ← X.Ψ_symm_act hs, LinearEquiv.apply_symm_apply]
  have h2 : X.act (s m) (a * b) = X.Ψ s (X.νb s hs m (a * b), MM.act m (a * b)) := by
    rw [← X.Ψe_apply hs, ← X.Ψ_symm_act hs, LinearEquiv.apply_symm_apply]
  have h3 : X.ε (X.act (s m) (μ a b)) = X.Ψ s (MM.act m (μ a b), 0) := by
    have := X.Ψ_symm_ε hs (X.act (s m) (μ a b))
    rw [X.red_act, hs] at this
    rw [← this, ← X.Ψe_apply hs, LinearEquiv.apply_symm_apply]
  rw [h1, X.act_Ψ hs, h2, h3, ← map_add] at h
  have h' := congrArg Prod.fst ((X.Ψe hs).injective h)
  simp only [Prod.fst_add] at h'
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at h'
  rw [← h']
  abel

/-- **The `ActLift` of a lift**, through a graded section. -/
def toActLift : ActLift μ q MM :=
  ActLift.ofEq (X.νb s hs) (fun p d m a hm ha ↦ X.νb_deg hs hsh p d m a hm ha) (X.νb_eq hs)

/-- **Every graded `Λ_μ`-lift is the lift `M ⊕ εM` of an `ActLift`**: there is a graded linear
isomorphism `M × M ≅ L` carrying `ε(n, m) = (m, 0)` to `ε` and `(n, m) a = (na + ν(m,a), ma)` to
the action, and reducing to the identity. -/
theorem exists_model (hproj : ∀ p, Module.Projective R (LinearMap.range (MM.gr.proj p))) :
    ∃ (L₀ : ActLift μ q MM) (Φ : (M × M) ≃ₗ[R] L),
      (∀ x a, Φ (MM.act x.1 a + L₀.act x.2 a, MM.act x.2 a) = X.act (Φ x) a) ∧
      (∀ x : M × M, Φ (x.2, 0) = X.ε (Φ x)) ∧ (∀ x, X.red (Φ x) = x.2) ∧
      ∀ p x, (twistGr (MM := MM) (NN := MM) q).IsHom p x ↔ X.gr.IsHom p (Φ x) := by
  obtain ⟨s, hs, hsh⟩ := X.exists_section hproj
  refine ⟨X.toActLift hs hsh, X.Ψe hs, fun x a ↦ ?_, fun x ↦ ?_, X.red_Ψ hs, fun p x ↦ ⟨?_, ?_⟩⟩
  · rw [Ψe_apply, Ψe_apply, act_Ψ]; rfl
  · rw [Ψe_apply, Ψe_apply, Ψ_apply, Ψ_apply, map_zero, zero_add, map_add, X.ε_ε, add_zero]
  · exact X.Ψ_hom hsh
  · intro h
    have := X.Ψ_symm_hom (hs := hs) (hsh := hsh) h
    rwa [LinearEquiv.symm_apply_apply] at this

end MuMod

/-! ### Lemma 6.6 for graded `Λ_μ`-modules -/

/-- **Lemma 6.6, existence**: under `Ext²_Λ(M, M)_q = 0`, `M` has a graded lift to `Λ_μ`, free
over `R[ε]/(ε²)` (for a normalized cocycle: `μ(1, 1) = 0`). -/
theorem exists_muMod (hq : HDeg GΛ μ q) (hμ : IsHCocycle μ) (h11 : μ 1 1 = 0)
    (h : ExtVanish MM MM 1 q) : Nonempty (MuMod μ q MM (M × M)) := by
  obtain ⟨L₀⟩ := exists_actLift μ hq hμ MM h
  exact ⟨L₀.toMuMod h11⟩

/-- **Lemma 6.6, uniqueness**: under `Ext¹_Λ(M, M)_q = 0` (and graded pieces of `M` projective
over `R`, e.g. `M` free), two graded lifts of `M` to `Λ_μ` free over `R[ε]/(ε²)` are isomorphic by
a graded `Λ_μ`-linear isomorphism reducing to the identity. -/
theorem muMod_unique (hproj : ∀ p, Module.Projective R (LinearMap.range (MM.gr.proj p)))
    (h : ExtVanish MM MM 0 q) {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L']
    [Module R L'] (X : MuMod μ q MM L) (Y : MuMod μ q MM L') :
    ∃ Φ : L ≃ₗ[R] L', (∀ l a, Φ (X.act l a) = Y.act (Φ l) a) ∧ (∀ l, Φ (X.ε l) = Y.ε (Φ l)) ∧
      (∀ l, Y.red (Φ l) = X.red l) ∧ ∀ p l, X.gr.IsHom p l → Y.gr.IsHom p (Φ l) := by
  obtain ⟨L₀, Ψ, hΨa, hΨε, hΨr, hΨh⟩ := X.exists_model hproj
  obtain ⟨L₀', Ψ', hΨa', hΨε', hΨr', hΨh'⟩ := Y.exists_model hproj
  obtain ⟨φ, hφ, hφe⟩ := L₀.exists_iso L₀' h
  -- the coordinate change `(n, m) ↦ (n + φ m, m)`
  let Θ : (M × M) ≃ₗ[R] (M × M) :=
    { toFun := fun x ↦ (x.1 + φ x.2, x.2)
      invFun := fun x ↦ (x.1 - φ x.2, x.2)
      map_add' := fun x y ↦ by ext <;> simp; abel
      map_smul' := fun c x ↦ by ext <;> simp
      left_inv := fun x ↦ by ext <;> simp
      right_inv := fun x ↦ by ext <;> simp }
  have hΘ : ∀ x, Θ x = (x.1 + φ x.2, x.2) := fun x ↦ rfl
  refine ⟨Ψ.symm.trans (Θ.trans Ψ'), fun l a ↦ ?_, fun l ↦ ?_, fun l ↦ ?_, fun p l hl ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [← hΨa, LinearEquiv.symm_apply_apply, hΘ, hΘ, ← hΨa']
    congr 1
    have e : L₀'.act x.2 a = L₀.act x.2 a + φ (MM.act x.2 a) - MM.act (φ x.2) a := by
      have h := hφe x.2 a
      rw [sub_eq_iff_eq_add] at h
      rw [h]; abel
    ext
    · simp only [map_add, LinearMap.add_apply, e]
      abel
    · rfl
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearEquiv.trans_apply]
    rw [← hΨε, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, ← hΨε', map_zero,
      add_zero]
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rw [hΨr', hΘ, hΨr]
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    have hx := (hΨh p x).2 hl
    rw [twistGr_isHom] at hx
    refine (hΨh' p _).1 ?_
    rw [hΘ, twistGr_isHom]
    exact ⟨MM.gr.isHom_add hx.1 (hφ p _ hx.2), hx.2⟩

/-- **Lemma 6.6, maps lift**: under `Ext¹_Λ(M, N)_{r+q} = 0`, a `Λ`-linear map `f : M → N` of
degree `r` lifts to a graded `Λ_μ`-linear map `F : L → L'` of degree `r` between graded lifts,
reducing to `f`. -/
theorem muMod_mapLift {r : ℤ} (hprojM : ∀ p, Module.Projective R (LinearMap.range (MM.gr.proj p)))
    (hprojN : ∀ p, Module.Projective R (LinearMap.range (NN.gr.proj p)))
    {L L' : Type*} [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (X : MuMod μ q MM L) (Y : MuMod μ q NN L') (f : M →ₗ[R] N)
    (hf : ∀ m a, f (MM.act m a) = NN.act (f m) a)
    (hfdeg : ∀ p m, MM.gr.IsHom p m → NN.gr.IsHom (p + r) (f m))
    (h : ExtVanish MM NN 0 (r + q)) :
    ∃ F : L →ₗ[R] L', (∀ l a, F (X.act l a) = Y.act (F l) a) ∧ (∀ l, F (X.ε l) = Y.ε (F l)) ∧
      (∀ l, Y.red (F l) = f (X.red l)) ∧ ∀ p l, X.gr.IsHom p l → Y.gr.IsHom (p + r) (F l) := by
  obtain ⟨L₀, Ψ, hΨa, hΨε, hΨr, hΨh⟩ := X.exists_model hprojM
  obtain ⟨L₀', Ψ', hΨa', hΨε', hΨr', hΨh'⟩ := Y.exists_model hprojN
  obtain ⟨g, hg, hfg⟩ := exists_mapLift L₀ L₀' f hf hfdeg h
  let Fm : M × M →ₗ[R] N × N :=
    { toFun := fun x ↦ (f x.1 + g x.2, f x.2)
      map_add' := fun x y ↦ by ext <;> simp; abel
      map_smul' := fun c x ↦ by ext <;> simp }
  have hFm : ∀ x, Fm x = (f x.1 + g x.2, f x.2) := fun x ↦ rfl
  refine ⟨Ψ'.toLinearMap ∘ₗ Fm ∘ₗ Ψ.symm.toLinearMap, fun l a ↦ ?_, fun l ↦ ?_, fun l ↦ ?_,
    fun p l hl ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hΨa, LinearEquiv.symm_apply_apply, hFm, hFm, ← hΨa']
    congr 1
    have e : g (MM.act x.2 a) = NN.act (g x.2) a + L₀'.act (f x.2) a - f (L₀.act x.2 a) := by
      have h := hfg.2 x.2 a
      rw [sub_eq_iff_eq_add] at h
      rw [h]; abel
    ext
    · simp only [map_add, LinearMap.add_apply, hf, e]
      abel
    · exact hf x.2 a
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← hΨε, LinearEquiv.symm_apply_apply, ← hΨε']
    simp [hFm]
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hΨr', hFm, hΨr]
  · obtain ⟨x, rfl⟩ := Ψ.surjective l
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have hx := (hΨh p x).2 hl
    rw [twistGr_isHom] at hx
    refine (hΨh' (p + r) _).1 ?_
    rw [hFm, twistGr_isHom]
    refine ⟨NN.gr.isHom_add ?_ ?_, hfdeg p _ hx.2⟩
    · have := hfdeg _ _ hx.1
      rwa [show p + q + r = p + r + q by ring] at this
    · have := hg p _ hx.2
      rwa [show p + (r + q) = p + r + q by ring] at this

/-- **`Λ_μ`-linear maps between lifts `M ⊕ εM → N ⊕ εN`** are exactly `(n, m) ↦ (f n + g m, f m)`
with `f + εg` a lifted map (`IsLiftHom`): so the lifted Hom modules are the equation-form ones,
free over `R[ε]/(ε²)` on lifts of a basis (`liftHom_basis`). -/
theorem modelHom_iff (L₀ : ActLift μ q MM) (L₀' : ActLift μ q NN) (F : M × M →ₗ[R] N × N) :
    ((∀ x a, F (MM.act x.1 a + L₀.act x.2 a, MM.act x.2 a) =
        (NN.act (F x).1 a + L₀'.act (F x).2 a, NN.act (F x).2 a)) ∧
      ∀ x : M × M, F (x.2, 0) = ((F x).2, 0)) ↔
    ∃ f g : M →ₗ[R] N, IsLiftHom L₀ L₀' f g ∧ ∀ x, F x = (f x.1 + g x.2, f x.2) := by
  constructor
  · rintro ⟨hact, hε⟩
    let f : M →ₗ[R] N := LinearMap.snd R N N ∘ₗ F ∘ₗ LinearMap.inr R M M
    let g : M →ₗ[R] N := LinearMap.fst R N N ∘ₗ F ∘ₗ LinearMap.inr R M M
    have hf0 : ∀ m, F (m, 0) = (f m, 0) := fun m ↦ hε (0, m)
    have hF : ∀ x, F x = (f x.1 + g x.2, f x.2) := fun x ↦ by
      have : x = (x.1, 0) + (0, x.2) := by ext <;> simp
      rw [this, map_add, hf0]
      ext <;> simp [f, g]
    refine ⟨f, g, ⟨fun m a ↦ ?_, fun m a ↦ ?_⟩, hF⟩
    · have := congrArg Prod.snd (hact (0, m) a)
      rw [hF, hF] at this
      simpa using this
    · have := congrArg Prod.fst (hact (0, m) a)
      rw [hF, hF] at this
      simp only [map_zero, LinearMap.zero_apply, zero_add, map_add] at this
      rw [← sub_eq_zero] at this ⊢
      rw [← this]
      abel
  · rintro ⟨f, g, ⟨hf, hg⟩, hF⟩
    refine ⟨fun x a ↦ ?_, fun x ↦ ?_⟩
    · rw [hF, hF]
      have e : g (MM.act x.2 a) = NN.act (g x.2) a + L₀'.act (f x.2) a - f (L₀.act x.2 a) := by
        have h := hg x.2 a
        rw [sub_eq_iff_eq_add] at h
        rw [h]; abel
      ext
      · simp only [map_add, LinearMap.add_apply, hf, e]
        abel
      · exact hf x.2 a
    · rw [hF, hF]; simp

end GExt

end MultiplicativeBasisDeformations
