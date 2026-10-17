import MultiplicativeBasisDeformations.Foundations.PreprojectiveDimension
import MultiplicativeBasisDeformations.Foundations.PathGrading
import MultiplicativeBasisDeformations.Foundations.PreprojFunctionals
import MultiplicativeBasisDeformations.Foundations.UBound

/-!
# The graded first-arrow sequence of `Π(Δ)`

`periodic-mesh-calculations.tex` (proof of the bound by the `U_d`): "The
first-arrow presentation of each simple gives, as in (A.1), an exact sequence
`e_iΠ⟨2⟩ → ⊕_{j∼i} e_jΠ⟨1⟩ → e_iΠ → S_i → 0`. Exactness at the middle term is
proved as for (A.1)."

We fix the endpoint `j` and the degree. Write `h_i(d) = dim e_i Π_d e_j`. The
middle exactness (`exact_star`, proved for Proposition 4.1) and the grading of
the ideal give `∑_{l∼i} h_l(d+1) ≤ h_i(d+2) + h_i(d)` and
`∑_{l∼i} h_l(0) ≤ h_i(1)`; these are the inequalities `κ ≥ 0` of `UBound`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v

namespace OrientedTree

open RelSystem

variable {D : Type v} (T : OrientedTree D) [Fintype D] [DecidableEq D] [DecidableRel T.orient]
  (k : Type u) [Field k]

/-- The ideal of `Π(Δ)` between two vertices. -/
abbrev Id (x y : T.Dbl) := (T.preproj k).ideal (LinearPaths.obj (k := k) x) (LinearPaths.obj y)

variable {T k}

theorem ofStar_pre {i l j : T.Dbl} (a : i ⟶ l) (F : T.Sp k l) :
    ofStar j (pre a F) = LinearPaths.arrow a ≫ ofStar j F := by
  classical
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => rw [map_add, map_add, hF, hG, map_add, Preadditive.comp_add]
  | single e c =>
      obtain ⟨Y, p⟩ := e
      simp only [pre, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, ofStar,
        Finsupp.linearCombination_single, Linear.comp_smul]
      congr 1
      by_cases h : Y = j
      · subst h
        simp [LinearPaths.arrow, LinearPaths.path_comp_path]
      · simp [h]

theorem ofStar_mem_Id {i j : T.Dbl} {F : T.Sp k i} (hF : F ∈ T.Ist k i) : ofStar j F ∈ T.Id k i j := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨Y, f, hf, rfl⟩ := hF
      by_cases hY : Y = j
      · subst hY; rw [ofStar_toStar]; exact hf
      · rw [ofStar_toStar_ne hY]; exact zero_mem _
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem toStar_mem_Ist {i j : T.Dbl} {f : LinearPaths.obj (k := k) i ⟶ LinearPaths.obj j}
    (hf : f ∈ T.Id k i j) : toStar j f ∈ T.Ist k i :=
  Submodule.subset_span ⟨j, f, hf, rfl⟩

/-- **Middle exactness with a fixed endpoint.** -/
theorem exact_hom {i j : T.Dbl} (w : ∀ e : T.OutArrow i, LinearPaths.obj (k := k) e.1 ⟶ LinearPaths.obj j)
    (hw : ∑ e, LinearPaths.arrow e.2 ≫ w e ∈ T.Id k i j) :
    ∃ W : LinearPaths.obj (k := k) i ⟶ LinearPaths.obj j, ∀ e : T.OutArrow i,
      w e - ((T.sgn k i e.1 : kˣ) : k) • (LinearPaths.arrow (rev e) ≫ W) ∈ T.Id k e.1 j := by
  set H : ∀ e : T.OutArrow i, T.Sp k e.1 := fun e ↦ toStar j (w e)
  have hH : gmap i H ∈ T.Ist k i := by
    have : gmap i H = toStar j (∑ e, LinearPaths.arrow e.2 ≫ w e) := by
      simp only [gmap, H, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        pre_toStar, map_sum]
    rw [this]
    exact toStar_mem_Ist hw
  obtain ⟨W₀, R, hR, hHR⟩ := exact_star H hH
  refine ⟨ofStar j W₀, fun e ↦ ?_⟩
  have h1 : w e = ofStar j (H e) := (ofStar_toStar _).symm
  have h2 := congrFun hHR e
  rw [Pi.add_apply] at h2
  rw [h1, h2, map_add]
  simp only [fmap, LinearMap.pi_apply, LinearMap.smul_apply, map_smul, ofStar_pre]
  rw [add_sub_cancel_left]
  exact ofStar_mem_Id (hR e)

/-! ### Degree projections -/

theorem proj_arrow_comp {i l j : T.Dbl} (a : i ⟶ l) (d : ℕ)
    (F : LinearPaths.obj (k := k) l ⟶ LinearPaths.obj j) :
    LinearPaths.proj (d + 1) i j (LinearPaths.arrow a ≫ F) =
      LinearPaths.arrow a ≫ LinearPaths.proj d l j F := by
  induction F using LinearPaths.induction_on with
  | h0 => simp
  | hadd F G hF hG => rw [Preadditive.comp_add, map_add, hF, hG, map_add, Preadditive.comp_add]
  | hsingle p c =>
      rw [Linear.comp_smul, map_smul, map_smul, Linear.comp_smul, LinearPaths.arrow,
        LinearPaths.path_comp_path, LinearPaths.proj_path, LinearPaths.proj_path]
      simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath]
      split_ifs with h1 h2 h2
      · rw [← LinearPaths.path_comp_path]
      · omega
      · omega
      · simp

theorem proj_zero_arrow_comp {i l j : T.Dbl} (a : i ⟶ l)
    (F : LinearPaths.obj (k := k) l ⟶ LinearPaths.obj j) :
    LinearPaths.proj 0 i j (LinearPaths.arrow a ≫ F) = 0 := by
  induction F using LinearPaths.induction_on with
  | h0 => simp
  | hadd F G hF hG => rw [Preadditive.comp_add, map_add, hF, hG, add_zero]
  | hsingle p c =>
      rw [Linear.comp_smul, map_smul, LinearPaths.arrow, LinearPaths.path_comp_path,
        LinearPaths.proj_path, if_neg (by simp), smul_zero]

/-- The ideal of `Π(Δ)` is graded. -/
theorem proj_mem_Id {x y : T.Dbl} (d : ℕ) {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hf : f ∈ T.Id k x y) : LinearPaths.proj d x y f ∈ T.Id k x y := by
  refine LinearPaths.proj_mem_linearSpan (T.preproj k).rels ?_ d hf
  intro X Y r hr
  obtain ⟨i, hX, hY, rfl⟩ := hr
  change X = i at hX
  change Y = i at hY
  subst hX hY
  refine ⟨2, ?_⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  unfold preproj preprojRel
  refine Submodule.sum_mem _ fun e _ ↦ Submodule.smul_mem _ _ ?_
  have := LinearPaths.path_mem_degreePart (k := k)
    (e.2.toPath.comp (Quiver.Hom.toPath (show e.1 ⟶ Y from ⟨e.2.down.symm⟩)))
  rwa [Quiver.Path.length_comp, Quiver.Path.length_toPath, Quiver.Path.length_toPath] at this

/-! ### The graded pieces `e_i Π_d e_j` -/

variable (T k) in
/-- `e_i Π_d e_j`, inside `kQ(i, j)` modulo the ideal. -/
def Wsp (i j : T.Dbl) (d : ℕ) : Submodule k ((LinearPaths.obj (k := k) i ⟶ LinearPaths.obj j) ⧸ T.Id k i j) :=
  (LinearPaths.degreePart d i j).map (T.Id k i j).mkQ

instance fd_degreePart (i j : T.Dbl) (d : ℕ) :
    FiniteDimensional k (LinearPaths.degreePart (k := k) d i j) := by
  haveI := finite_short_paths (T := T) i (d + 1)
  have : Finite {p : Quiver.Path i j // p.length = d} := by
    refine Finite.of_injective (β := {e : Quiver.PathStar i // e.2.length < d + 1})
      (fun p ↦ ⟨⟨j, p.1⟩, by simp [p.2]⟩) ?_
    intro p q h
    simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact Subtype.ext h
  have hfin : Set.Finite {f | ∃ p : Quiver.Path i j, p.length = d ∧ f = LinearPaths.path (k := k) p} :=
    (Set.finite_range (fun p : {p : Quiver.Path i j // p.length = d} ↦
      LinearPaths.path (k := k) p.1)).subset (by rintro _ ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩)
  exact FiniteDimensional.span_of_finite k hfin

instance (i j : T.Dbl) (d : ℕ) : FiniteDimensional k (T.Wsp k i j d) := by
  unfold Wsp
  infer_instance

/-- Prefixing an arrow, on `kQ(·, j)`. -/
def lcomp {i l : T.Dbl} (a : i ⟶ l) (j : T.Dbl) :
    (LinearPaths.obj (k := k) l ⟶ LinearPaths.obj j) →ₗ[k] (LinearPaths.obj (k := k) i ⟶ LinearPaths.obj j) where
  toFun f := LinearPaths.arrow a ≫ f
  map_add' f g := Preadditive.comp_add _ _ _ _ _ _
  map_smul' c f := Linear.comp_smul _ _ _ _ _ _

/-- Prefixing an arrow, on `e_l Π e_j → e_i Π e_j`. -/
def lq {i l : T.Dbl} (a : i ⟶ l) (j : T.Dbl) :
    ((LinearPaths.obj (k := k) l ⟶ LinearPaths.obj j) ⧸ T.Id k l j) →ₗ[k]
      ((LinearPaths.obj (k := k) i ⟶ LinearPaths.obj j) ⧸ T.Id k i j) :=
  (T.Id k l j).mapQ (T.Id k i j) (lcomp a j) fun _ hf ↦ (T.preproj k).comp_mem_ideal _ hf

theorem lq_mkQ {i l j : T.Dbl} (a : i ⟶ l) (f : LinearPaths.obj (k := k) l ⟶ LinearPaths.obj j) :
    lq a j ((T.Id k l j).mkQ f) = (T.Id k i j).mkQ (LinearPaths.arrow a ≫ f) := rfl

theorem lq_mem {i l j : T.Dbl} (a : i ⟶ l) (d : ℕ) {x} (hx : x ∈ T.Wsp k l j d) :
    lq a j x ∈ T.Wsp k i j (d + 1) := by
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx
  rw [lq_mkQ]
  refine Submodule.mem_map_of_mem ?_
  have := LinearPaths.comp_mem_degreePart (LinearPaths.path_mem_degreePart (k := k) a.toPath) hf
  rwa [Quiver.Path.length_toPath, add_comm] at this

/-- `⊕_{l∼i} e_l Π_d e_j → e_i Π_{d+1} e_j`. -/
def G' (i j : T.Dbl) (d : ℕ) : (∀ e : T.OutArrow i, T.Wsp k e.1 j d) →ₗ[k] T.Wsp k i j (d + 1) :=
  LinearMap.codRestrict _ (∑ e : T.OutArrow i, (lq e.2 j).comp ((T.Wsp k e.1 j d).subtype.comp
    (LinearMap.proj e))) fun x ↦ by
      simp only [LinearMap.sum_apply, LinearMap.comp_apply]
      exact Submodule.sum_mem _ fun e _ ↦ lq_mem e.2 d (x e).2

/-- `e_i Π_d e_j → ⊕_{l∼i} e_l Π_{d+1} e_j`, with the signs of the relation. -/
def F' (i j : T.Dbl) (d : ℕ) : T.Wsp k i j d →ₗ[k] (∀ e : T.OutArrow i, T.Wsp k e.1 j (d + 1)) :=
  LinearMap.pi fun e ↦ LinearMap.codRestrict _
    (((T.sgn k i e.1 : kˣ) : k) • (lq (rev e) j).comp (T.Wsp k i j d).subtype) fun x ↦
      Submodule.smul_mem _ _ (lq_mem (rev e) d x.2)

theorem exists_rep {l j : T.Dbl} {d : ℕ} (x : T.Wsp k l j d) :
    ∃ w ∈ LinearPaths.degreePart (k := k) d l j, (T.Id k l j).mkQ w = x :=
  Submodule.mem_map.1 x.2

/-- **Middle exactness in each degree.** -/
theorem ker_G'_le (i j : T.Dbl) (d : ℕ) :
    LinearMap.ker (G' (T := T) (k := k) i j (d + 1)) ≤ LinearMap.range (F' (T := T) (k := k) i j d) := by
  intro x hx
  choose w hw hwx using fun e ↦ exists_rep (x e)
  have hsum : ∑ e, LinearPaths.arrow e.2 ≫ w e ∈ T.Id k i j := by
    rw [LinearMap.mem_ker] at hx
    have := congrArg Subtype.val hx
    simp only [G', LinearMap.codRestrict_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply,
      Submodule.coe_zero] at this
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    rw [← this]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [← hwx e]; rfl
  obtain ⟨W, hW⟩ := exact_hom w hsum
  refine ⟨⟨(T.Id k i j).mkQ (LinearPaths.proj d i j W),
    Submodule.mem_map_of_mem (LinearPaths.proj_mem W)⟩, ?_⟩
  funext e
  apply Subtype.ext
  simp only [F', LinearMap.pi_apply, LinearMap.codRestrict_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Submodule.subtype_apply]
  rw [← hwx e, lq_mkQ, ← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq]
  have h1 := proj_mem_Id (d + 1) (hW e)
  rw [map_sub, map_smul, proj_arrow_comp, LinearPaths.proj_of_mem (hw e), if_pos rfl] at h1
  have := Submodule.neg_mem _ h1
  rwa [neg_sub] at this

theorem G'_zero_injective (i j : T.Dbl) : Function.Injective (G' (T := T) (k := k) i j 0) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  choose w hw hwx using fun e ↦ exists_rep (x e)
  have hsum : ∑ e, LinearPaths.arrow e.2 ≫ w e ∈ T.Id k i j := by
    rw [LinearMap.mem_ker] at hx
    have := congrArg Subtype.val hx
    simp only [G', LinearMap.codRestrict_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply,
      Submodule.coe_zero] at this
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum]
    rw [← this]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [← hwx e]; rfl
  obtain ⟨W, hW⟩ := exact_hom w hsum
  rw [Submodule.mem_bot]
  funext e
  apply Subtype.ext
  rw [← hwx e]
  have h1 := proj_mem_Id 0 (hW e)
  rw [map_sub, map_smul, proj_zero_arrow_comp, smul_zero, sub_zero,
    LinearPaths.proj_of_mem (hw e), if_pos rfl] at h1
  simp only [Submodule.mkQ_apply, Pi.zero_apply, Submodule.coe_zero]
  exact (Submodule.Quotient.mk_eq_zero _).2 h1

/-- **The dimension inequalities** `∑_{l∼i} h_l(d+1) ≤ h_i(d+2) + h_i(d)`. -/
theorem sum_finrank_le (i j : T.Dbl) (d : ℕ) :
    ∑ e : T.OutArrow i, Module.finrank k (T.Wsp k e.1 j (d + 1)) ≤
      Module.finrank k (T.Wsp k i j (d + 2)) + Module.finrank k (T.Wsp k i j d) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (G' (T := T) (k := k) i j (d + 1))
  rw [Module.finrank_pi_fintype] at h1
  have h2 := Submodule.finrank_mono (ker_G'_le (T := T) (k := k) i j d)
  have h3 := LinearMap.finrank_range_le (F' (T := T) (k := k) i j d)
  have h4 : Module.finrank k (LinearMap.range (G' (T := T) (k := k) i j (d + 1))) ≤
      Module.finrank k (T.Wsp k i j (d + 2)) :=
    Submodule.finrank_le (LinearMap.range (G' (T := T) (k := k) i j (d + 1)))
  omega

theorem sum_finrank_le_zero (i j : T.Dbl) :
    ∑ e : T.OutArrow i, Module.finrank k (T.Wsp k e.1 j 0) ≤ Module.finrank k (T.Wsp k i j 1) := by
  have := LinearMap.finrank_le_finrank_of_injective (G'_zero_injective (T := T) (k := k) i j)
  rwa [Module.finrank_pi_fintype] at this

theorem one_le_finrank_nil (j : T.Dbl) : 1 ≤ Module.finrank k (T.Wsp k j j 0) := by
  rw [Nat.one_le_iff_ne_zero, ne_eq, Submodule.finrank_eq_zero]
  intro h
  have h0 : LinearPaths.path (k := k) (Quiver.Path.nil : Quiver.Path j j) ∈
      LinearPaths.degreePart (k := k) 0 j j := Submodule.subset_span ⟨Quiver.Path.nil, rfl, rfl⟩
  have hmem : (T.Id k j j).mkQ (LinearPaths.path (Quiver.Path.nil : Quiver.Path j j)) ∈ T.Wsp k j j 0 :=
    Submodule.mem_map_of_mem (f := (T.Id k j j).mkQ) h0
  rw [h, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
  exact T.nil_not_mem_del (k := k) ∅ (Set.notMem_empty j) ((T.preproj k).ideal_le_del ∅ hmem)

/-- A nonzero graded piece contains a path outside the ideal. -/
theorem exists_path_of_finrank {i j : T.Dbl} {d : ℕ} (h : 1 ≤ Module.finrank k (T.Wsp k i j d)) :
    ∃ p : Quiver.Path i j, p.length = d ∧ LinearPaths.path (k := k) p ∉ T.Id k i j := by
  by_contra hne
  push Not at hne
  have hle : LinearPaths.degreePart (k := k) d i j ≤ T.Id k i j :=
    Submodule.span_le.2 fun _ ⟨p, hp, hf⟩ ↦ hf ▸ hne p hp
  have : T.Wsp k i j d = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hx
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hle hf
  rw [this, finrank_bot] at h
  omega

open Classical in
variable (T) in
/-- The adjacency matrix of `Δ`. -/
def adjM : Matrix T.Dbl T.Dbl ℤ := Matrix.of fun i l ↦ if T.G.Adj (i : D) (l : D) then 1 else 0

open Classical in
theorem sum_outArrow (i : T.Dbl) (f : T.Dbl → ℤ) :
    ∑ e : T.OutArrow i, f e.1 = ∑ l, T.adjM i l * f l := by
  let eqv : T.OutArrow i ≃ {l : T.Dbl // T.G.Adj (i : D) (l : D)} :=
    { toFun := fun e ↦ ⟨e.1, e.2.down⟩
      invFun := fun l ↦ ⟨l.1, ⟨l.2⟩⟩
      left_inv := by rintro ⟨l, ⟨a⟩⟩; rfl
      right_inv := by rintro ⟨l, a⟩; rfl }
  rw [Fintype.sum_equiv eqv (fun e ↦ f e.1) (fun l ↦ f l.1) (fun _ ↦ rfl),
    ← Finset.sum_subtype (Finset.univ.filter fun l : T.Dbl ↦ T.G.Adj (i : D) (l : D))
      (by simp) f, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [adjM, Matrix.of_apply]
  split_ifs <;> simp

/-- **The lower bound** `(dim e_i Π_N e_j)_{ij} ≥ U_N` when `U_0, …, U_N ≥ 0`
(`periodic-mesh-calculations.tex`). -/
theorem U_le_finrank (j : T.Dbl) (N : ℕ) (hU : ∀ d ≤ N, ∀ a b, 0 ≤ UBound.U T.adjM d a b)
    (i : T.Dbl) : UBound.U T.adjM N i j ≤ (Module.finrank k (T.Wsp k i j N) : ℤ) := by
  set h : ℕ → T.Dbl → ℤ := fun d i ↦ (Module.finrank k (T.Wsp k i j d) : ℤ)
  have hM : ∀ (d : ℕ) (i : T.Dbl), T.adjM.mulVec (h d) i = ∑ e : T.OutArrow i, h d e.1 := by
    intro d i
    rw [sum_outArrow]
    rfl
  refine UBound.le_of_U T.adjM h j N hU (fun d hd _ i ↦ ?_) (fun i ↦ ?_) i
  · match d, hd with
    | 1, _ =>
        simp only [UBound.κ, Pi.sub_apply]
        rw [hM, sub_nonneg]
        have := sum_finrank_le_zero (T := T) (k := k) i j
        simp only [h]
        exact_mod_cast this
    | d + 2, _ =>
        simp only [UBound.κ, Pi.add_apply, Pi.sub_apply]
        rw [hM]
        have := sum_finrank_le (T := T) (k := k) i j d
        simp only [h]
        have h' : (∑ e : T.OutArrow i, (Module.finrank k (T.Wsp k e.1 j (d + 1)) : ℤ)) ≤
            (Module.finrank k (T.Wsp k i j (d + 2)) : ℤ) + Module.finrank k (T.Wsp k i j d) := by
          exact_mod_cast this
        linarith
  · split_ifs with hij
    · subst hij
      show (1 : ℤ) ≤ (Module.finrank k (T.Wsp k i i 0) : ℤ)
      exact_mod_cast one_le_finrank_nil (T := T) (k := k) i
    · exact Nat.cast_nonneg _

end OrientedTree

end MultiplicativeBasisDeformations
