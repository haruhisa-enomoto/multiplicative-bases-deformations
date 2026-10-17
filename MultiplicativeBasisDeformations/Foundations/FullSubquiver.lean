import MultiplicativeBasisDeformations.Foundations.PathMaps

/-!
# Full translation subquivers

`graded-category.tex` (`eq:mesh-object-quotient`). Let `S` be a set of
vertices closed under `τ` and `τ⁻¹` wherever defined, and `Q_S` the full
translation subquiver on `S`. In the path category, killing the identities
outside `S` kills exactly the paths through vertices outside `S`. A mesh
relation based in `S` retains the terms whose middle vertex lies in `S`; this
is the mesh relation of `Q_S`.

This file provides:

* `FullSub S`, the full subquiver on `S`, its inclusion `FullSub.incl`, and the
  lift `FullSub.liftPath` of a path all of whose vertices lie in `S`;
* the retraction `FullSub.restrict : kQ → kQ_S`, sending a path to its lift if
  it stays in `S` and to zero otherwise; it is multiplicative;
* `TranslationQuiver.restrict`, the translation quiver structure on `FullSub S`,
  and the restricted coefficients.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

universe u v w

variable {V : Type v} [Quiver.{w} V]

/-- The full subquiver on a set of vertices (a type synonym, to carry its own
quiver structure). -/
def FullSub (S : Set V) : Type v := S

namespace FullSub

variable {S : Set V}

instance : Quiver.{w} (FullSub S) where
  Hom a b := (a : S).1 ⟶ (b : S).1

/-- The underlying vertex. -/
abbrev val (a : FullSub S) : V := (a : S).1

theorem val_mem (a : FullSub S) : a.val ∈ S := (a : S).2

/-- The vertex of the subquiver. -/
abbrev mk (v : V) (hv : v ∈ S) : FullSub S := (⟨v, hv⟩ : S)

theorem ext {a b : FullSub S} (h : a.val = b.val) : a = b := Subtype.ext h

instance [DecidableEq V] : DecidableEq (FullSub S) := fun a b ↦
  decidable_of_iff (a.val = b.val) ⟨ext, fun h ↦ h ▸ rfl⟩

instance [Fintype V] [DecidablePred (· ∈ S)] : Fintype (FullSub S) :=
  inferInstanceAs (Fintype S)

instance [∀ x y : V, DecidableEq (x ⟶ y)] (a b : FullSub S) : DecidableEq (a ⟶ b) :=
  inferInstanceAs (DecidableEq (a.val ⟶ b.val))

instance [∀ x y : V, Fintype (x ⟶ y)] (a b : FullSub S) : Fintype (a ⟶ b) :=
  inferInstanceAs (Fintype (a.val ⟶ b.val))

/-- The inclusion of the full subquiver. -/
abbrev incl (S : Set V) : FullSub S ⥤q V where
  obj := val
  map a := a

/-- Lift a path all of whose vertices lie in `S` (auxiliary form). -/
def liftPathAux (a : FullSub S) : ∀ {b : V} (p : Quiver.Path a.val b)
    (hp : ∀ v ∈ p.vertices, v ∈ S),
    Quiver.Path a (mk b (hp b (Quiver.Path.end_mem_vertices p)))
  | _, Quiver.Path.nil, _ => Quiver.Path.nil
  | _, Quiver.Path.cons p e, hp =>
      Quiver.Path.cons (liftPathAux a p fun v hv ↦ hp v (by
        rw [Quiver.Path.vertices_cons, List.concat_eq_append]
        exact List.mem_append_left _ hv)) e

theorem incl_mapPath_liftPathAux (a : FullSub S) {b : V} (p : Quiver.Path a.val b)
    (hp : ∀ v ∈ p.vertices, v ∈ S) : (incl S).mapPath (liftPathAux a p hp) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change Quiver.Path.cons ((incl S).mapPath (liftPathAux a p _)) e = _
      rw [ih]

/-- Lift a path all of whose vertices lie in `S`. -/
def liftPath (a b : FullSub S) (p : Quiver.Path a.val b.val) (hp : ∀ v ∈ p.vertices, v ∈ S) :
    Quiver.Path a b :=
  liftPathAux a p hp

theorem incl_mapPath_liftPath {a b : FullSub S} (p : Quiver.Path a.val b.val)
    (hp : ∀ v ∈ p.vertices, v ∈ S) : (incl S).mapPath (liftPath a b p hp) = p :=
  incl_mapPath_liftPathAux a p hp

theorem vertices_incl_mapPath {a b : FullSub S} (p : Quiver.Path a b) :
    ∀ v ∈ ((incl S).mapPath p).vertices, v ∈ S := by
  intro v hv
  rw [LinearPaths.vertices_mapPath, List.mem_map] at hv
  obtain ⟨z, -, rfl⟩ := hv
  exact z.val_mem

theorem liftPath_incl_mapPath {a b : FullSub S} (p : Quiver.Path a b) :
    liftPath a b ((incl S).mapPath p) (vertices_incl_mapPath p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change Quiver.Path.cons (liftPath a _ ((incl S).mapPath p) _) e = _
      rw [ih]

theorem length_liftPath {a b : FullSub S} (p : Quiver.Path a.val b.val)
    (hp : ∀ v ∈ p.vertices, v ∈ S) : (liftPath a b p hp).length = p.length := by
  rw [← LinearPaths.length_mapPath (incl S), incl_mapPath_liftPath]

theorem incl_mapPath_injective {a b : FullSub S} {p q : Quiver.Path a b}
    (h : (incl S).mapPath p = (incl S).mapPath q) : p = q := by
  rw [← liftPath_incl_mapPath p, ← liftPath_incl_mapPath q]
  simp only [h]

theorem mem_vertices_comp_iff {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    (∀ v ∈ (p.comp q).vertices, v ∈ S) ↔
      (∀ v ∈ p.vertices, v ∈ S) ∧ ∀ v ∈ q.vertices, v ∈ S := by
  rw [Quiver.Path.vertices_comp]
  constructor
  · intro h
    refine ⟨fun v hv ↦ ?_, fun v hv ↦ h v (List.mem_append_right _ hv)⟩
    rw [← Quiver.Path.dropLast_append_end_eq p, List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact h v (List.mem_append_left _ hv)
    · exact h v (List.mem_append_right _ (Quiver.Path.start_mem_vertices q))
  · rintro ⟨hp, hq⟩ v hv
    rcases List.mem_append.1 hv with hv | hv
    · exact hp v (List.mem_of_mem_dropLast hv)
    · exact hq v hv

theorem liftPath_comp {a b c : FullSub S} (p : Quiver.Path a.val b.val)
    (q : Quiver.Path b.val c.val) (hp : ∀ v ∈ p.vertices, v ∈ S)
    (hq : ∀ v ∈ q.vertices, v ∈ S) (hpq : ∀ v ∈ (p.comp q).vertices, v ∈ S) :
    liftPath a c (p.comp q) hpq = (liftPath a b p hp).comp (liftPath b c q hq) := by
  apply incl_mapPath_injective
  rw [Prefunctor.mapPath_comp, incl_mapPath_liftPath, incl_mapPath_liftPath,
    incl_mapPath_liftPath]

variable (k : Type u) [CommRing k]

/-- The paths through some vertex outside `S`, spanned in `kQ`. -/
def outside (S : Set V) (x y : V) : Submodule k (LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y) :=
  Submodule.span k {f | ∃ p : Quiver.Path x y, (∃ v ∈ p.vertices, v ∉ S) ∧ f = LinearPaths.path p}

open Classical in
/-- A path of `Q` between vertices of `S`, restricted to `Q_S`: its lift if it
stays in `S`, and zero otherwise. -/
def restrictPath {a b : FullSub S} (p : Quiver.Path a.val b.val) :
    LinearPaths.obj (k := k) a ⟶ LinearPaths.obj (k := k) b :=
  if h : ∀ v ∈ p.vertices, v ∈ S then LinearPaths.path (liftPath a b p h) else 0

/-- The retraction `kQ → kQ_S` on Hom spaces between vertices of `S`. -/
def restrict (a b : FullSub S) :
    (LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj (k := k) b.val) →ₗ[k]
      (LinearPaths.obj (k := k) a ⟶ LinearPaths.obj (k := k) b) :=
  LinearPaths.extend (k := k) (restrictPath k)

theorem restrictPath_comp {a b c : FullSub S} (p : Quiver.Path a.val b.val)
    (q : Quiver.Path b.val c.val) :
    restrictPath k (p.comp q) = restrictPath k p ≫ restrictPath (b := c) k q := by
  classical
  unfold restrictPath
  by_cases hp : ∀ v ∈ p.vertices, v ∈ S
  · by_cases hq : ∀ v ∈ q.vertices, v ∈ S
    · have hpq := (mem_vertices_comp_iff p q).2 ⟨hp, hq⟩
      rw [dif_pos hpq, dif_pos hp, dif_pos hq, liftPath_comp p q hp hq hpq,
        LinearPaths.path_comp_path]
    · have hpq : ¬ ∀ v ∈ (p.comp q).vertices, v ∈ S :=
        fun h ↦ hq ((mem_vertices_comp_iff p q).1 h).2
      rw [dif_neg hpq, dif_neg hq, Limits.comp_zero]
  · have hpq : ¬ ∀ v ∈ (p.comp q).vertices, v ∈ S :=
      fun h ↦ hp ((mem_vertices_comp_iff p q).1 h).1
    rw [dif_neg hpq, dif_neg hp, Limits.zero_comp]

theorem restrict_comp {a b c : FullSub S}
    (f : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val)
    (g : LinearPaths.obj (k := k) b.val ⟶ LinearPaths.obj c.val) :
    restrict k a c (f ≫ g) = restrict k a b f ≫ restrict k b c g := by
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, map_add, h₁, h₂, Preadditive.add_comp]
  | hsingle p t =>
      induction g using LinearPaths.induction_on with
      | h0 => simp
      | hadd g₁ g₂ h₁ h₂ =>
          rw [Preadditive.comp_add, map_add, map_add, h₁, h₂, Preadditive.comp_add]
      | hsingle q t' =>
          rw [Linear.smul_comp, Linear.comp_smul, LinearPaths.path_comp_path, map_smul, map_smul,
            map_smul, map_smul]
          simp only [restrict, LinearPaths.extend_path, restrictPath_comp, Linear.smul_comp,
            Linear.comp_smul]
          rw [smul_comm]

/-- The inclusion `kQ_S → kQ` on Hom spaces. -/
abbrev inclL (a b : FullSub S) :=
  LinearPaths.mapPaths (k := k) (incl S) a b

theorem restrict_inclL {a b : FullSub S} (f : LinearPaths.obj (k := k) a ⟶ LinearPaths.obj b) :
    restrict k a b (inclL k a b f) = f := by
  classical
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | hsingle p t =>
      rw [map_smul, map_smul, LinearPaths.mapPaths_path]
      simp only [restrict, LinearPaths.extend_path, restrictPath,
        dif_pos (vertices_incl_mapPath p), liftPath_incl_mapPath]

theorem sub_inclL_restrict_mem {a b : FullSub S}
    (f : LinearPaths.obj (k := k) a.val ⟶ LinearPaths.obj b.val) :
    f - inclL k a b (restrict k a b f) ∈ outside k S a.val b.val := by
  classical
  induction f using LinearPaths.induction_on with
  | h0 => simp
  | hadd f₁ f₂ h₁ h₂ =>
      rw [map_add, map_add, add_sub_add_comm]; exact add_mem h₁ h₂
  | hsingle p t =>
      rw [map_smul, map_smul, ← smul_sub]
      refine Submodule.smul_mem _ t ?_
      simp only [restrict, LinearPaths.extend_path, restrictPath]
      split_ifs with h
      · rw [LinearPaths.mapPaths_path, incl_mapPath_liftPath, sub_self]; exact zero_mem _
      · rw [map_zero, sub_zero]
        push_neg at h
        exact Submodule.subset_span ⟨p, h, rfl⟩

theorem outside_comp_mem {x y z : V} {f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y}
    (hf : f ∈ outside k S x y) (g : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z) :
    f ≫ g ∈ outside k S x z := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨p, ⟨v, hv, hvS⟩, rfl⟩ := hf
      induction g using LinearPaths.induction_on with
      | h0 => simp
      | hadd g₁ g₂ h₁ h₂ => rw [Preadditive.comp_add]; exact add_mem h₁ h₂
      | hsingle q t =>
          rw [Linear.comp_smul, LinearPaths.path_comp_path]
          refine Submodule.smul_mem _ t (Submodule.subset_span ⟨p.comp q, ⟨v, ?_, hvS⟩, rfl⟩)
          rw [Quiver.Path.vertices_comp, List.mem_append]
          rw [← Quiver.Path.dropLast_append_end_eq p, List.mem_append, List.mem_singleton] at hv
          rcases hv with hv | rfl
          · exact Or.inl hv
          · exact Or.inr (Quiver.Path.start_mem_vertices q)
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.add_comp]; exact add_mem ha hb
  | smul t a _ ha => rw [Linear.smul_comp]; exact Submodule.smul_mem _ t ha

theorem comp_outside_mem {x y z : V} (f : LinearPaths.obj (k := k) x ⟶ LinearPaths.obj y)
    {g : LinearPaths.obj (k := k) y ⟶ LinearPaths.obj z} (hg : g ∈ outside k S y z) :
    f ≫ g ∈ outside k S x z := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨q, ⟨v, hv, hvS⟩, rfl⟩ := hg
      induction f using LinearPaths.induction_on with
      | h0 => simp
      | hadd f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp]; exact add_mem h₁ h₂
      | hsingle p t =>
          rw [Linear.smul_comp, LinearPaths.path_comp_path]
          refine Submodule.smul_mem _ t (Submodule.subset_span ⟨p.comp q, ⟨v, ?_, hvS⟩, rfl⟩)
          rw [Quiver.Path.vertices_comp, List.mem_append]
          by_cases hvy : v = y
          · subst hvy
            exact Or.inr (Quiver.Path.start_mem_vertices q)
          · exact Or.inr hv
  | zero => simp
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact add_mem ha hb
  | smul t a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ t ha

end FullSub


end MultiplicativeBasisDeformations

namespace MultiplicativeBasisDeformations

universe u v w

namespace TranslationQuiver

variable {V : Type v} [Quiver.{w} V] (Q : TranslationQuiver V)

/-- A set of vertices closed under `τ` and `τ⁻¹` wherever they are defined. -/
def IsTauClosed (S : Set V) : Prop :=
  ∀ (x : V) (hx : x ∈ Q.nonprojective), x ∈ S ↔ (Q.tau ⟨x, hx⟩).1 ∈ S

variable {Q} {S : Set V} (hS : Q.IsTauClosed S)

/-- The full translation subquiver `Q_S` on a `τ`-closed set `S`. -/
abbrev restrict : TranslationQuiver (FullSub S) where
  nonprojective := {a | a.val ∈ Q.nonprojective}
  noninjective := {a | a.val ∈ Q.noninjective}
  tau :=
    { toFun := fun a ↦ ⟨FullSub.mk (Q.tau ⟨a.1.val, a.2⟩).1 ((hS _ a.2).1 a.1.val_mem),
        (Q.tau ⟨a.1.val, a.2⟩).2⟩
      invFun := fun b ↦ ⟨FullSub.mk (Q.tau.symm ⟨b.1.val, b.2⟩).1
        ((hS _ (Q.tau.symm ⟨b.1.val, b.2⟩).2).2 (by
          simp only [Subtype.coe_eta, Equiv.apply_symm_apply]; exact b.1.val_mem)),
        (Q.tau.symm ⟨b.1.val, b.2⟩).2⟩
      left_inv := fun a ↦ by
        apply Subtype.ext; apply FullSub.ext
        simp only [FullSub.mk, Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun b ↦ by
        apply Subtype.ext; apply FullSub.ext
        simp only [FullSub.mk, Subtype.coe_eta, Equiv.apply_symm_apply] }
  mate x y := Q.mate ⟨x.1.val, x.2⟩ y.val

/-- The vertex of `Q`, from a nonprojective vertex of `Q_S`. -/
abbrev restrictNonproj (x : (restrict hS).nonprojective) : Q.nonprojective := ⟨x.1.val, x.2⟩

theorem restrict_tau_val (x : (restrict hS).nonprojective) :
    ((restrict hS).tau x).1.val = (Q.tau (restrictNonproj hS x)).1 := rfl

end TranslationQuiver

variable {k : Type u} [CommRing k] {V : Type v} [Quiver.{w} V] {Q : TranslationQuiver V}
  {S : Set V} (hS : Q.IsTauClosed S)

/-- The coefficients of `Q`, restricted to `Q_S`. -/
def MeshCoefficients.restrict (c : MeshCoefficients k Q) :
    MeshCoefficients k (TranslationQuiver.restrict hS) :=
  fun x y a ↦ c (TranslationQuiver.restrictNonproj hS x) y.val a

noncomputable instance FullSub.instFintypeStar [∀ x : V, Fintype (Σ y : V, y ⟶ x)]
    (x : FullSub S) : Fintype (Σ y : FullSub S, y ⟶ x) :=
  Fintype.ofInjective (fun b ↦ (⟨b.1.val, b.2⟩ : Σ y : V, y ⟶ x.val)) (by
    rintro ⟨y, a⟩ ⟨y', a'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : y = y' := FullSub.ext h1
    subst this
    simp only [heq_eq_eq] at h2
    subst h2
    rfl)

end MultiplicativeBasisDeformations
