import MultiplicativeBasisDeformations.Foundations.RayWeightsIso
import MultiplicativeBasisDeformations.Foundations.MeshWeightsConn

/-!
# The deck group of Proposition 7.2 is `π₁(K)`

`prop:integral-ray-weights`: "let `G` be the free deck group of Subsection 4.2", the fundamental
group of the mesh complex `K` acting on the universal cover. The formalization's deck group is
the fundamental group of `K` with a cone of edges `s_X : v₀ → X` adjoined (`DeckGrading.lean`),
and Proposition 7.2 is proved for the stabilizer `H` of the component `𝓛₀` of a base object of
the lifted projective category (`RayWeightsIso.lean`). For a connected quiver whose meshes have
nonempty middle terms (the Auslander–Reiten quiver of a connected algebra), this file identifies
`H` with `π₁(K, b)`, `b` the base vertex, and `𝓛₀` with the lifted projectives of the universal
cover of `K`:
* the inclusion `K ⊂ K ∪ cone` (`incl`) has a retraction (`retr`, sending `s_X` to a walk from
  `v₀` to `X`), so `w ↦ s_b w s_b⁻¹` is injective on `π₁(K, b)` (`φ`, `φ_injective`);
* the degree of a nonzero piece of `A₀` is the class of a path (`exists_path_of_nz`), so the
  objects of `𝓛₀` are `(x, s_b w s_x⁻¹)` with `w` a walk class `b → x` (`conn_δ`), and `H` lies in
  the image of `φ`;
* conversely every walk class is realized by a zigzag of arrows in the lifted quiver (translation
  edges by the two arrows of a mesh, `aconn_δ`), whose lifted projectives lie in `𝓛₀` by the support
  lemma (`conn_of_aconn`); so the image of `φ` is `H` (`range_φ`, `piOneEquiv`).
The connectedness of the quiver follows from that of `A₀` (`qConn_of_A0Conn`: every vertex
receives a nonzero map from a projective, and nonzero maps are combinations of paths); for
`Γ_A` the meshes have nonempty middle terms (`IndSkeleton.ar_hmid`) and `A₀` is connected for
connected `A` (`IndSkeleton.a0Conn_ar`). Hence Proposition 7.2(1) holds with `G = π₁(K, b)`:
`W(P) ≅ ℤ^{n−1} ⊕ π₁(K, b)_ab` (`WPequivFreePi1`, `theta_summand_pi1`), and `𝓛₀` is the lifted
projective category of the universal cover, equivariantly (`liftEquiv`, `liftEquiv_act`), so the
coinvariants `(I_𝓛₀)_H` of `coinvEquiv` are `(I_𝓛)_G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open CategoryTheory

namespace MultiplicativeBasisDeformations

namespace Morse

variable {V Ed : Type} {src tgt : Ed → V} (S : Tris src tgt)

/-- **Functors out of the fundamental groupoid agree if they agree on the edges** (with equal
objects). -/
theorem Pi_ext {D : Type*} [Groupoid D] (F G : Pi S ⥤ D)
    (hobj : ∀ X : V, F.obj ((Qf (S := S)).obj (ob src tgt X)) = G.obj ((Qf (S := S)).obj (ob src tgt X)))
    (hmap : ∀ e : Ed, HEq (F.map ((Qf (S := S)).map (ofE src tgt e)))
      (G.map ((Qf (S := S)).map (ofE src tgt e)))) :
    F = G := by
  have key : Qf (S := S) ⋙ F = Qf (S := S) ⋙ G := by
    have e1 : Qf (S := S) ⋙ F = Quiver.FreeGroupoid.lift
        (Quiver.FreeGroupoid.of (EQ src tgt) ⋙q (Qf (S := S) ⋙ G).toPrefunctor) := by
      apply Quiver.FreeGroupoid.lift_unique
      refine Prefunctor.ext (fun X ↦ hobj X) fun X Y a ↦ ?_
      obtain ⟨e, hs, ht⟩ := a
      subst hs ht
      apply eq_of_heq
      refine (hmap e).trans ?_
      symm
      simp only [Eq.recOn, eqRec_heq_iff_heq]
      rfl
    have e2 : Qf (S := S) ⋙ G = Quiver.FreeGroupoid.lift
        (Quiver.FreeGroupoid.of (EQ src tgt) ⋙q (Qf (S := S) ⋙ G).toPrefunctor) := by
      apply Quiver.FreeGroupoid.lift_unique
      rfl
    rw [e1, ← e2]
  have h1 := CategoryTheory.Quotient.lift_unique (TriRel S) (Qf (S := S) ⋙ F)
    (fun X Y f₁ f₂ h ↦ by
      simp only [Functor.comp_map]
      rw [CategoryTheory.Quotient.sound _ h]) F rfl
  have h2 := CategoryTheory.Quotient.lift_unique (TriRel S) (Qf (S := S) ⋙ G)
    (fun X Y f₁ f₂ h ↦ by
      simp only [Functor.comp_map]
      rw [CategoryTheory.Quotient.sound _ h]) G rfl
  rw [h1, h2]
  congr 1

end Morse

namespace MeshWalk

variable {V : Type} [Quiver.{0} V] [Fintype V] [DecidableEq V] (Q : TranslationQuiver V)
  [∀ x : V, Fintype (Σ y : V, y ⟶ x)] [hone : ∀ x y : V, Subsingleton (x ⟶ y)]
  [∀ x y : V, Fintype (x ⟶ y)] (v₀ : V)

/-- The class of an edge of `K`. -/
def edgeK (e : Ed Q) : obK Q (src Q e) ⟶ obK Q (tgt Q e) :=
  (Morse.Qf (S := meshTris Q)).map (Morse.ofE (src Q) (tgt Q) e)

/-- **The inclusion `K ⊂ K ∪ cone`** on fundamental groupoids. -/
def incl : PiK Q ⥤ PiC Q v₀ :=
  Morse.liftEdges (meshTris Q) (obC Q v₀) (fun e ↦ edgeC Q v₀ (Sum.inl e))
    (fun t ↦ Morse.Q_rel (S := coneTris Q v₀) t)

theorem incl_edge (e : Ed Q) : (incl Q v₀).map (edgeK Q e) = edgeC Q v₀ (Sum.inl e) :=
  Morse.liftEdges_edge _ _ _ _ e

/-- **The retraction**, sending the cone edge `s_X` to a walk class `v₀ → X` of `K`. -/
def retr (w : ∀ X : V, obK Q v₀ ⟶ obK Q X) : PiC Q v₀ ⥤ PiK Q :=
  Morse.liftEdges (coneTris Q v₀) (obK Q)
    (fun e ↦ match e with
      | Sum.inl e => edgeK Q e
      | Sum.inr X => w X)
    (fun t ↦ Morse.Q_rel (S := meshTris Q) t)

theorem retr_edge (w : ∀ X : V, obK Q v₀ ⟶ obK Q X) (e : Ed Q) :
    (retr Q v₀ w).map (edgeC Q v₀ (Sum.inl e)) = edgeK Q e :=
  Morse.liftEdges_edge _ _ _ _ (Sum.inl e)

theorem incl_retr (w : ∀ X : V, obK Q v₀ ⟶ obK Q X) : incl Q v₀ ⋙ retr Q v₀ w = 𝟭 (PiK Q) := by
  refine Morse.Pi_ext _ _ _ (fun X ↦ rfl) fun e ↦ heq_of_eq ?_
  change (retr Q v₀ w).map ((incl Q v₀).map (edgeK Q e)) = edgeK Q e
  rw [incl_edge]
  exact retr_edge Q v₀ w e

theorem incl_map_injective (w : ∀ X : V, obK Q v₀ ⟶ obK Q X) {X Y : V}
    {f f' : obK Q X ⟶ obK Q Y} (h : (incl Q v₀).map f = (incl Q v₀).map f') : f = f' := by
  have h' := congrArg (retr Q v₀ w).map h
  have e := incl_retr Q v₀ w
  have hf := Functor.congr_hom e f
  have hf' := Functor.congr_hom e f'
  have e1 : ∀ p : (incl Q v₀ ⋙ retr Q v₀ w).obj (obK Q X) = (𝟭 (PiK Q)).obj (obK Q X),
      eqToHom p = 𝟙 _ := fun p ↦ eqToHom_refl _ p
  have e2 : ∀ p : (𝟭 (PiK Q)).obj (obK Q Y) = (incl Q v₀ ⋙ retr Q v₀ w).obj (obK Q Y),
      eqToHom p = 𝟙 _ := fun p ↦ eqToHom_refl _ p
  rw [e1, e2] at hf hf'
  simp only [Functor.comp_map, Functor.id_map] at hf hf'
  erw [Category.id_comp, Category.comp_id] at hf hf'
  rw [← hf, ← hf', h']

/-! ### The conjugated walk class `δ(w) = s_X w s_Y⁻¹` -/

section Delta

variable {Q v₀}

/-- The inclusion on morphisms, with the objects of `PiC`. -/
def inclMap {X Y : V} (w : obK Q X ⟶ obK Q Y) : obC Q v₀ X ⟶ obC Q v₀ Y := (incl Q v₀).map w

theorem inclMap_comp {X Y Z : V} (w : obK Q X ⟶ obK Q Y) (w' : obK Q Y ⟶ obK Q Z) :
    inclMap (v₀ := v₀) (w ≫ w') = inclMap w ≫ inclMap w' := (incl Q v₀).map_comp w w'

theorem inclMap_id (X : V) : inclMap (v₀ := v₀) (𝟙 (obK Q X)) = 𝟙 _ := (incl Q v₀).map_id _


/-- `δ(w) = s_X w s_Y⁻¹` in the deck group. -/
def δ {X Y : V} (w : obK Q X ⟶ obK Q Y) : Deck Q v₀ :=
  MulOpposite.op (coneC Q v₀ X ≫ inclMap w ≫ Groupoid.inv (coneC Q v₀ Y))

theorem δ_comp {X Y Z : V} (w : obK Q X ⟶ obK Q Y) (w' : obK Q Y ⟶ obK Q Z) :
    δ (v₀ := v₀) (w ≫ w') = δ w * δ w' := by
  apply MulOpposite.unop_injective
  simp only [δ, MulOpposite.unop_mul, MulOpposite.unop_op, End.mul_def, inclMap_comp,
    Category.assoc]
  simp

theorem δ_id (X : V) : δ (v₀ := v₀) (𝟙 (obK Q X)) = 1 := by
  apply MulOpposite.unop_injective
  simp only [δ, inclMap_id, Category.id_comp, MulOpposite.unop_op, MulOpposite.unop_one,
    End.one_def]
  simp

theorem δ_inv {X Y : V} (w : obK Q X ⟶ obK Q Y) :
    δ (v₀ := v₀) (Groupoid.inv w) = (δ w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right (a := δ w) (b := δ (Groupoid.inv w)) ?_
  rw [← δ_comp, Groupoid.comp_inv, δ_id]

theorem δ_injective (w : ∀ X : V, obK Q v₀ ⟶ obK Q X) {X Y : V} {f f' : obK Q X ⟶ obK Q Y}
    (h : δ (v₀ := v₀) f = δ f') : f = f' := by
  apply incl_map_injective Q v₀ w
  have h' := congrArg MulOpposite.unop h
  simp only [δ, MulOpposite.unop_op] at h'
  have h'' := congrArg (fun g ↦ Groupoid.inv (coneC Q v₀ X) ≫ g ≫ coneC Q v₀ Y) h'
  simp at h''
  exact h''

variable (Q) in
/-- The class of an arrow in `π₁(K)`. -/
def arrK {y x : V} (a : y ⟶ x) : obK Q y ⟶ obK Q x := edgeK Q (Sum.inl ⟨y, x, a⟩)

theorem inclMap_arrK {y x : V} (a : y ⟶ x) : inclMap (v₀ := v₀) (arrK Q a) = arrC Q v₀ a :=
  incl_edge Q v₀ (Sum.inl ⟨y, x, a⟩)

variable (Q) in
/-- The class of a path in `π₁(K)`. -/
def pathK : ∀ {x y : V}, Quiver.Path x y → (obK Q x ⟶ obK Q y)
  | _, _, Quiver.Path.nil => 𝟙 _
  | _, _, Quiver.Path.cons p a => pathK p ≫ arrK Q a

theorem inclMap_pathK {x y : V} (p : Quiver.Path x y) :
    inclMap (v₀ := v₀) (pathK Q p) = pathC Q v₀ p := by
  induction p with
  | nil => simp only [pathK, pathC]; exact inclMap_id _
  | cons p a ih =>
      simp only [pathK, pathC]
      rw [inclMap_comp, ih, inclMap_arrK]

theorem δ_pathK {x y : V} (p : Quiver.Path x y) : δ (v₀ := v₀) (pathK Q p) = (degW Q v₀).deg p := by
  rw [δ, inclMap_pathK]; rfl

theorem δ_arrK {y x : V} (a : y ⟶ x) : δ (v₀ := v₀) (arrK Q a) = dg Q v₀ a := by
  have := δ_pathK (Q := Q) (v₀ := v₀) a.toPath
  simp only [Quiver.Hom.toPath, pathK, Category.id_comp] at this
  exact this

/-- The class of a translation edge in `π₁(K)`. -/
def tK (x : Q.nonprojective) : obK Q (Q.tau x).1 ⟶ obK Q x.1 := edgeK Q (Sum.inr x)

theorem triK (x : Q.nonprojective) {y : V} (b : y ⟶ x.1) :
    arrK Q (Q.mate x y b) ≫ arrK Q b = tK x := by
  have h := Morse.Q_rel (S := meshTris Q) (⟨x, y, b⟩ : Tri Q)
  have h' : arrK Q (Q.mate x y b) ≫ 𝟙 _ ≫ arrK Q b = 𝟙 _ ≫ tK x ≫ 𝟙 _ := h
  simpa using h'

end Delta

/-! ### Zigzags of arrows realize walk classes -/

section Zigzag

variable {Q v₀}

/-- Vertices of `K`, with morphisms the deck elements realized by arrow zigzags. -/
@[nolint unusedArguments]
structure Tg (_Q : TranslationQuiver V) (_v₀ : V) where
  v : V

variable (Q v₀) in
/-- A deck element realized by arrow zigzags from every sheet. -/
@[ext]
structure TgHom (X Y : V) where
  d : Deck Q v₀
  h : ∀ g, aconn Q v₀ (X, g) (Y, g * d)

instance : Groupoid (Tg Q v₀) where
  Hom X Y := TgHom Q v₀ X.v Y.v
  id X := ⟨1, fun g ↦ by rw [mul_one]; exact Relation.EqvGen.refl _⟩
  comp f g := ⟨f.d * g.d, fun h ↦ by
    rw [← mul_assoc]; exact Relation.EqvGen.trans _ _ _ (f.h h) (g.h (h * f.d))⟩
  id_comp f := TgHom.ext (one_mul _)
  comp_id f := TgHom.ext (mul_one _)
  assoc f g h := TgHom.ext (mul_assoc _ _ _)
  inv {X Y} f := ⟨f.d⁻¹, fun h ↦ by
    have := f.h (h * f.d⁻¹)
    have e : h * f.d⁻¹ * f.d = h := inv_mul_cancel_right h f.d
    rw [e] at this
    exact Relation.EqvGen.symm _ _ this⟩
  inv_comp f := TgHom.ext (inv_mul_cancel f.d)
  comp_inv f := TgHom.ext (mul_inv_cancel f.d)

/-- The deck element of a morphism of `Tg`. -/
def tgd {X Y : Tg Q v₀} (f : X ⟶ Y) : Deck Q v₀ := (f : TgHom Q v₀ X.v Y.v).d

theorem tgd_h {X Y : Tg Q v₀} (f : X ⟶ Y) (g : Deck Q v₀) :
    aconn Q v₀ (X.v, g) (Y.v, g * tgd f) := (f : TgHom Q v₀ X.v Y.v).h g

theorem tgd_ext {X Y : Tg Q v₀} {f g : X ⟶ Y} (h : tgd f = tgd g) : f = g :=
  TgHom.ext (x := (f : TgHom Q v₀ X.v Y.v)) (y := (g : TgHom Q v₀ X.v Y.v)) h

theorem Tg_comp_d {X Y Z : Tg Q v₀} (f : X ⟶ Y) (g : Y ⟶ Z) : tgd (f ≫ g) = tgd f * tgd g := rfl

theorem Tg_eqToHom_d {X Y : Tg Q v₀} (p : X = Y) : tgd (eqToHom p) = 1 := by
  cases p; rfl

variable (hmid : ∀ x : Q.nonprojective, Nonempty (Σ y : V, y ⟶ x.1))

include hmid in
theorem edge_aconn (e : Ed Q) (h : Deck Q v₀) :
    aconn Q v₀ (src Q e, h) (tgt Q e, h * δ (edgeK Q e)) := by
  rcases e with ⟨y, x, a⟩ | x
  · change aconn Q v₀ (y, h) (x, h * δ (arrK Q a))
    rw [δ_arrK]; exact aconn_arrow (y, h) a
  · obtain ⟨⟨y, b⟩⟩ := hmid x
    change aconn Q v₀ ((Q.tau x).1, h) (x.1, h * δ (tK x))
    rw [← triK x b, δ_comp, ← mul_assoc, δ_arrK, δ_arrK]
    exact Relation.EqvGen.trans _ _ _ (aconn_arrow ((Q.tau x).1, h) (Q.mate x y b))
      (aconn_arrow (y, h * dg Q v₀ (Q.mate x y b)) b)

/-- The walk classes as arrow zigzags. -/
def Fa : PiK Q ⥤ Tg Q v₀ :=
  Morse.liftEdges (meshTris Q) (fun X : V ↦ (⟨X⟩ : Tg Q v₀))
    (fun e ↦ show (⟨src Q e⟩ : Tg Q v₀) ⟶ ⟨tgt Q e⟩ from
      (⟨δ (edgeK Q e), edge_aconn hmid e⟩ : TgHom Q v₀ (src Q e) (tgt Q e)))
    (fun t ↦ by
      apply tgd_ext
      simp only [Tg_comp_d, Tg_eqToHom_d, mul_one, one_mul]
      change δ (arrK Q (Q.mate t.1 t.2.1 t.2.2)) * δ (arrK Q t.2.2) = δ (tK t.1)
      rw [← δ_comp, triK])

/-- Undo the conjugation by the cone edges. -/
def Eu : Tg Q v₀ ⥤ PiC Q v₀ where
  obj X := obC Q v₀ X.v
  map {X Y} f := Groupoid.inv (coneC Q v₀ X.v) ≫ (tgd f).unop ≫ coneC Q v₀ Y.v
  map_id X := by
    change Groupoid.inv (coneC Q v₀ X.v) ≫ (1 : Deck Q v₀).unop ≫ coneC Q v₀ X.v = 𝟙 _
    simp [End.one_def]
  map_comp {X Y Z} f g := by
    change Groupoid.inv (coneC Q v₀ X.v) ≫ (tgd f * tgd g).unop ≫ coneC Q v₀ Z.v =
      (Groupoid.inv (coneC Q v₀ X.v) ≫ (tgd f).unop ≫ coneC Q v₀ Y.v) ≫
        (Groupoid.inv (coneC Q v₀ Y.v) ≫ (tgd g).unop ≫ coneC Q v₀ Z.v)
    simp only [MulOpposite.unop_mul, End.mul_def, Category.assoc]
    simp

theorem Fa_Eu : Fa hmid ⋙ Eu = incl Q v₀ := by
  refine Morse.Pi_ext _ _ _ (fun X ↦ rfl) fun e ↦ heq_of_eq ?_
  change Eu.map ((Fa hmid).map (edgeK Q e)) = inclMap (v₀ := v₀) (edgeK Q e)
  unfold Fa
  rw [edgeK, Morse.liftEdges_edge]
  change Groupoid.inv (coneC Q v₀ (src Q e)) ≫ (δ (edgeK Q e)).unop ≫ coneC Q v₀ (tgt Q e) = _
  simp [δ]
  rfl

theorem Fa_d {X Y : V} (w : obK Q X ⟶ obK Q Y) : tgd ((Fa hmid).map w) = δ (v₀ := v₀) w := by
  have h := Functor.congr_hom (Fa_Eu (v₀ := v₀) hmid) w
  have e1 : ∀ p : (Fa hmid ⋙ Eu).obj (obK Q X) = (incl Q v₀).obj (obK Q X), eqToHom p = 𝟙 _ :=
    fun p ↦ eqToHom_refl _ p
  have e2 : ∀ p : (incl Q v₀).obj (obK Q Y) = (Fa hmid ⋙ Eu).obj (obK Q Y), eqToHom p = 𝟙 _ :=
    fun p ↦ eqToHom_refl _ p
  rw [e1, e2] at h
  erw [Category.id_comp, Category.comp_id] at h
  change Groupoid.inv (coneC Q v₀ X) ≫ (tgd ((Fa hmid).map w)).unop ≫ coneC Q v₀ Y =
    inclMap (v₀ := v₀) w at h
  apply MulOpposite.unop_injective
  rw [δ, MulOpposite.unop_op, ← h]
  simp

include hmid in
/-- **Every walk class is realized by a zigzag of arrows in the lifted quiver.** -/
theorem aconn_δ {X Y : V} (w : obK Q X ⟶ obK Q Y) (h : Deck Q v₀) :
    aconn Q v₀ (X, h) (Y, h * δ w) := by
  rw [← Fa_d hmid w]
  exact tgd_h ((Fa hmid).map w) h

end Zigzag

/-! ### `H ≅ π₁(K, b)` -/

section Main

open ScalarMeshCategory CatAlg CatAlg.MeshData

attribute [local instance] Classical.decEq

variable {Q v₀} {k : Type*} [Field k] [IsAlgClosed k] [Infinite k] {c : MeshCoefficients k Q}
  {L : LocalFamily (k := k) (meshFam Q c)} {D : MeshData (meshFam Q c) L}
  [hfd : ∀ x y : V, FiniteDimensional k (meshFam Q c x ⟶ meshFam Q c y)]

/-- **The lifted projectives connected in `L`** differ by conjugated walk classes. -/
theorem conn_δ {o o' : LObj Q c v₀ D} (h : conn Q c v₀ D o o') :
    ∃ w : obK Q o.1.1 ⟶ obK Q o'.1.1, o'.2 = o.2 * δ w := by
  induction h with
  | rel o o' hl =>
    obtain ⟨f, hf⟩ := hl
    have hnz : NZ Q c v₀ D (o.1, o'.1, o.2⁻¹ * o'.2) := by
      intro hbot
      apply hf
      apply Subtype.ext
      have hm : f.1 ∈ (D0 Q c v₀ D).part (o.2⁻¹ * o'.2) o.1 o'.1 := f.2
      rw [hbot, Submodule.mem_bot] at hm
      exact hm
    obtain ⟨p, hp⟩ := exists_path_of_nz hnz
    exact ⟨pathK Q p, by rw [δ_pathK, hp]; exact (mul_inv_cancel_left o.2 o'.2).symm⟩
  | refl o => exact ⟨𝟙 _, by rw [δ_id]; exact (mul_one _).symm⟩
  | symm o o' _ ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨Groupoid.inv w, by rw [δ_inv, hw]; exact (mul_inv_cancel_right o.2 (δ w)).symm⟩
  | trans o o' o'' _ _ ih ih' =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨w', hw'⟩ := ih'
    exact ⟨w ≫ w', by rw [δ_comp, hw', hw]; exact mul_assoc _ _ _⟩

omit [Fintype V] [DecidableEq V] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] hone
  [∀ x y : V, Fintype (x ⟶ y)] in
theorem exists_walk (hQ : QConn V) (X Y : V) : Nonempty (obK Q X ⟶ obK Q Y) := by
  have h := hQ X Y
  induction h with
  | rel X Y h => obtain ⟨a⟩ := h; exact ⟨arrK Q a⟩
  | refl X => exact ⟨𝟙 _⟩
  | symm X Y _ ih => obtain ⟨w⟩ := ih; exact ⟨Groupoid.inv w⟩
  | trans X Y Z _ _ ih ih' => obtain ⟨w⟩ := ih; obtain ⟨w'⟩ := ih'; exact ⟨w ≫ w'⟩

/-- A nonzero homogeneous morphism of the mesh category is a combination of paths of its degree;
in particular there is a path. -/
theorem exists_path_of_part {x y : V} {g : Deck Q v₀} {m : meshFam Q c x ⟶ meshFam Q c y}
    (hm : m ∈ (deckGrading Q c v₀).part g x y) (hm0 : m ≠ 0) : Nonempty (Quiver.Path x y) := by
  by_contra hne
  apply hm0
  have hf' : m ∈ wPart c (degW Q v₀) g x y := by
    have : (deckGrading Q c v₀).IsHom g m := (HomGrading.mem_part_iff _).1 hm
    exact (isHom_iff (Q := Q) (c := c) (v₀ := v₀)).1 this
  have := wPart_le_span (Q := Q) (c := c) (v₀ := v₀) g x y hf'
  have hempty : {f | ∃ p : Quiver.Path x y, (degW Q v₀).deg p = g ∧ pathMor c p = f} = ∅ := by
    ext f; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, -, -⟩; exact hne ⟨p⟩
  rw [hempty, Submodule.span_empty] at this
  exact this

omit [DecidableEq V] [Fintype V] [∀ x : V, Fintype (Σ y : V, y ⟶ x)] hone
  [∀ x y : V, Fintype (x ⟶ y)] in
theorem eqvGen_of_path {x y : V} (p : Quiver.Path x y) :
    Relation.EqvGen (fun X Y : V ↦ Nonempty (X ⟶ Y)) x y := by
  induction p with
  | nil => exact Relation.EqvGen.refl _
  | cons p a ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ ⟨a⟩)

/-- **The quiver is connected when `A₀` is**: every vertex receives a nonzero map from a
projective (the support lemma), and nonzero maps are combinations of paths. -/
theorem qConn_of_A0Conn {x₀ : D.PV} (hconn : A0Conn Q c v₀ D x₀) : QConn V := by
  have hproj : ∀ x : D.PV, Relation.EqvGen (fun X Y : V ↦ Nonempty (X ⟶ Y)) x₀.1 x.1 := by
    intro x
    have h := hconn x
    clear hconn
    induction h with
    | rel x y hxy =>
      obtain ⟨g, hg⟩ := hxy
      obtain ⟨p, -⟩ := exists_path_of_nz hg
      exact eqvGen_of_path p
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  have hvert : ∀ X : V, Relation.EqvGen (fun X Y : V ↦ Nonempty (X ⟶ Y)) x₀.1 X := by
    intro X
    obtain ⟨z, m, hm, hm0⟩ := exists_supp (D := D) (X, (1 : Deck Q v₀))
    obtain ⟨p⟩ := exists_path_of_part hm hm0
    exact Relation.EqvGen.trans _ _ _ (hproj z.1) (eqvGen_of_path p)
  intro X Y
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hvert X)) (hvert Y)

variable (Q) in
/-- **`π₁(K, b)`**, with the multiplication convention of the deck group. -/
abbrev PiOne (b : V) := (End (obK Q b))ᵐᵒᵖ

variable (v₀) in
/-- `g ↦ s_b g s_b⁻¹`. -/
def φ (b : V) : PiOne Q b →* Deck Q v₀ where
  toFun g := δ g.unop
  map_one' := δ_id b
  map_mul' g g' := by
    change δ (g'.unop * g.unop) = δ g.unop * δ g'.unop
    rw [End.mul_def]; exact δ_comp _ _

theorem φ_injective (hQ : QConn V) (b : V) : Function.Injective (φ (Q := Q) v₀ b) := by
  intro g g' h
  exact MulOpposite.unop_injective
    (δ_injective (fun X ↦ (exists_walk hQ v₀ X).some) h)

variable (hmid : ∀ x : Q.nonprojective, Nonempty (Σ y : V, y ⟶ x.1))

include hmid in
theorem conn_of_walk (x₀ x : D.PV) (w : obK Q x₀.1 ⟶ obK Q x.1) :
    conn Q c v₀ D (o₀ Q c v₀ D x₀) (x, δ w) := by
  have h := aconn_δ hmid w (1 : Deck Q v₀)
  rw [show (1 : Deck Q v₀) * δ w = δ w from one_mul _] at h
  exact conn_of_aconn (D := D) (p := x₀) (q := x) (a := 1) (b := δ w) h

include hmid in
/-- **The image of `π₁(K, b)` is the stabilizer `H`** of the base component. -/
theorem range_φ (hQ : QConn V) (x₀ : D.PV) :
    MonoidHom.range (G := PiOne Q x₀.1) (φ (Q := Q) v₀ x₀.1) = Hs Q c v₀ D x₀ := by
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    exact conn_of_walk hmid x₀ x₀ w.unop
  · intro hg
    obtain ⟨w, hw⟩ := conn_δ (o := o₀ Q c v₀ D x₀) (o' := (x₀, g)) hg
    refine ⟨MulOpposite.op w, ?_⟩
    change δ w = g
    have hw' : g = 1 * δ w := hw
    rw [hw']
    exact (one_mul _).symm

/-- **`H ≅ π₁(K, b)`**: the deck group of the base component is the fundamental group of `K`. -/
def piOneEquiv (hQ : QConn V) (x₀ : D.PV) : PiOne Q x₀.1 ≃* Hs Q c v₀ D x₀ :=
  (MonoidHom.ofInjective (G := PiOne Q x₀.1) (φ_injective (Q := Q) (v₀ := v₀) hQ x₀.1)).trans
    (MulEquiv.subgroupCongr (range_φ hmid hQ x₀))

theorem piOneEquiv_apply (hQ : QConn V) (x₀ : D.PV) (g : PiOne Q x₀.1) :
    ((piOneEquiv (v₀ := v₀) hmid hQ x₀ g : Hs Q c v₀ D x₀) : Deck Q v₀) =
      φ (Q := Q) v₀ x₀.1 g := rfl

/-- **The lifted projectives of the universal cover of `K`**, `(x, w)` with `w` a walk class
`b → x`, are the objects of the base component `𝓛₀`. -/
def liftEquiv (hQ : QConn V) (x₀ : D.PV) :
    (Σ x : D.PV, obK Q x₀.1 ⟶ obK Q x.1) ≃
      {o : LObj Q c v₀ D // conn Q c v₀ D (o₀ Q c v₀ D x₀) o} :=
  Equiv.ofBijective (fun xw : (Σ x : D.PV, obK Q x₀.1 ⟶ obK Q x.1) ↦
      (⟨(xw.1, δ xw.2), conn_of_walk hmid x₀ xw.1 xw.2⟩ :
        {o : LObj Q c v₀ D // conn Q c v₀ D (o₀ Q c v₀ D x₀) o})) (by
    constructor
    · rintro ⟨x, w⟩ ⟨x', w'⟩ h
      have h1 : x = x' := congrArg (fun o : {o : LObj Q c v₀ D // _} ↦ o.1.1) h
      subst h1
      have h2 : δ (v₀ := v₀) w = δ w' := congrArg (fun o : {o : LObj Q c v₀ D // _} ↦ o.1.2) h
      rw [δ_injective (fun X ↦ (exists_walk hQ v₀ X).some) h2]
    · rintro ⟨o, ho⟩
      obtain ⟨w, hw⟩ := conn_δ ho
      refine ⟨⟨o.1, w⟩, Subtype.ext ?_⟩
      change ((o.1, δ w) : LObj Q c v₀ D) = o
      rw [show δ (v₀ := v₀) w = o.2 by rw [hw]; exact (one_mul (δ (v₀ := v₀) w)).symm]
      rfl)

/-- The deck action corresponds to the action of `π₁(K, b)` on walk classes. -/
theorem liftEquiv_act (hQ : QConn V) (x₀ : D.PV) (g : PiOne Q x₀.1)
    (xw : Σ x : D.PV, obK Q x₀.1 ⟶ obK Q x.1) :
    ((liftEquiv hmid hQ x₀ ⟨xw.1, g.unop ≫ xw.2⟩).1 : LObj Q c v₀ D) =
      gL Q c v₀ D (φ (Q := Q) v₀ x₀.1 g) (liftEquiv hmid hQ x₀ xw).1 := by
  change ((xw.1, δ (g.unop ≫ xw.2)) : LObj Q c v₀ D) = (xw.1, δ g.unop * δ xw.2)
  rw [δ_comp]

variable {x₀ : D.PV} (hconn : A0Conn Q c v₀ D x₀) {ζ : LObj Q c v₀ D → WP Q c v₀ D}
  (hζ : ∀ o o', Thin.Line o o' → wtL Q c v₀ D o o' = ζ o' - ζ o)

/-- **Proposition 7.2(1) with `G = π₁(K, b)`**: `W(P) ≅ ℤ^{n−1} ⊕ π₁(K, b)_ab`. -/
def WPequivFreePi1 : WP Q c v₀ D ≃+
    ({x : D.PV // x ≠ x₀} → ℤ) × Additive (Abelianization (PiOne Q x₀.1)) :=
  (WPequivFree hconn hζ).trans (AddEquiv.prodCongr (AddEquiv.refl _)
    (MulEquiv.toAdditive (MulEquiv.abelianizationCongr (G := Hs Q c v₀ D x₀) (H := PiOne Q x₀.1)
      (piOneEquiv (v₀ := v₀) hmid (qConn_of_A0Conn hconn) x₀).symm)))

/-- **`θ_g` is the `π₁(K, b)_ab` summand** under `WPequivFreePi1`, for `g ∈ π₁(K, b)` acting by
`s_b g s_b⁻¹`. -/
theorem theta_summand_pi1 (g : PiOne Q x₀.1) (o : LObj Q c v₀ D)
    (ho : conn Q c v₀ D (o₀ Q c v₀ D x₀) o) :
    WPequivFreePi1 hmid hconn hζ (ζ (gL Q c v₀ D (φ (Q := Q) v₀ x₀.1 g) o) - ζ o) =
      (0, Additive.ofMul (Abelianization.of g)) := by
  have h := theta_summand hconn hζ (piOneEquiv (v₀ := v₀) hmid (qConn_of_A0Conn hconn) x₀ g) o ho
  rw [piOneEquiv_apply] at h
  simp only [WPequivFreePi1, AddEquiv.trans_apply, h]
  refine Prod.ext rfl ?_
  change Additive.ofMul (MulEquiv.abelianizationCongr (G := Hs Q c v₀ D x₀) (H := PiOne Q x₀.1)
    (piOneEquiv (v₀ := v₀) hmid (qConn_of_A0Conn hconn) x₀).symm
    (Abelianization.of (piOneEquiv (v₀ := v₀) hmid (qConn_of_A0Conn hconn) x₀ g))) = _
  rw [_root_.abelianizationCongr_of, MulEquiv.symm_apply_apply]

end Main

end MeshWalk

end MultiplicativeBasisDeformations
