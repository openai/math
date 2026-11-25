import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.UniformDecorations

/-!
# Decorations on isomorphism classes of rooted maps

A presentation can carry a decoration of its vertices, or a choice of one
list index per certified patch. Transport along numbered rooted isomorphisms
makes either kind of choice into a family over maps. Rigidity identifies
isomorphism classes of decorated presentations with actual choices on one
representative of each underlying class.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace DecoratedMaps

open PortGraph
open scoped Classical BigOperators

universe u v

/-- Decorations and their transport under a change of names of the map. -/
structure Family (N : ℕ) where
  Label : MapRep N → Type u
  move : {A B : MapRep N} → A.map.Iso B.map → Label A ≃ Label B
  move_refl : ∀ (A) (a : Label A), move (.refl A.map) a = a
  move_trans : ∀ {A B C : MapRep N} (f : A.map.Iso B.map) (g : B.map.Iso C.map) (a : Label A),
    move (f.trans g) a = move g (move f a)

namespace Family

variable {N : ℕ} (L : Family.{u} N)

/-- A fully decorated named map. -/
abbrev Rep := (A : MapRep N) × L.Label A

/-- A decoration on the chosen representative of a bare map class. -/
abbrev Choices := (c : MapClass N) × L.Label c.out

/-- A map isomorphism also has to carry the decoration to the other one. -/
def IsIso (a b : L.Rep) : Prop := ∃ f : a.1.map.Iso b.1.map, L.move f a.2 = b.2

protected theorem IsIso.refl (a : L.Rep) : L.IsIso a a :=
  ⟨.refl a.1.map, L.move_refl a.1 a.2⟩

protected theorem IsIso.symm {a b : L.Rep} : L.IsIso a b → L.IsIso b a := by
  rintro ⟨f, he⟩
  refine ⟨f.symm, ?_⟩
  rw [← he, ← L.move_trans, Subsingleton.elim (f.trans f.symm) (.refl _)]
  exact L.move_refl _ _

protected theorem IsIso.trans {a b c : L.Rep} : L.IsIso a b → L.IsIso b c → L.IsIso a c := by
  rintro ⟨f,hf⟩ ⟨g,hg⟩
  exact ⟨f.trans g, (L.move_trans f g _).trans ((congrArg _ hf).trans hg)⟩

def isoSetoid : Setoid L.Rep where
  r := L.IsIso
  iseqv := ⟨IsIso.refl L, IsIso.symm L, IsIso.trans L⟩

abbrev Class := Quotient L.isoSetoid

def classOf (a : L.Rep) : L.Class := Quotient.mk L.isoSetoid a

private def forget : L.Class → MapClass N := Quotient.lift
  (fun a : L.Rep => Quotient.mk (MapRep.isoSetoid N) a.1)
  (fun _ _ ⟨f,_⟩ => Quotient.sound ⟨f⟩)

private def ofChoices (x : L.Choices) : L.Class := L.classOf ⟨x.1.out,x.2⟩

private theorem ofChoices_injective : Function.Injective L.ofChoices := by
  rintro ⟨c,a⟩ ⟨d,b⟩ he
  have hc : c = d := by
    have := congrArg L.forget he
    change Quotient.mk (MapRep.isoSetoid N) c.out = Quotient.mk _ d.out at this
    simpa only [Quotient.out_eq] using this
  subst d
  obtain ⟨f,hf⟩ := (Quotient.exact he : L.IsIso ⟨c.out,a⟩ ⟨c.out,b⟩)
  have ef : f = .refl _ := Subsingleton.elim _ _
  rw [ef, L.move_refl] at hf
  exact congrArg (Sigma.mk c) hf

private theorem ofChoices_surjective : Function.Surjective L.ofChoices := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    let c := Quotient.mk (MapRep.isoSetoid N) x.1
    obtain ⟨f⟩ := (MapClass.eq_iff_iso c.out x.1).mp c.out_eq
    refine ⟨⟨c,L.move f.symm x.2⟩, Quotient.sound ⟨f,?_⟩⟩
    rw [← L.move_trans, Subsingleton.elim (f.symm.trans f) (.refl _)]
    exact L.move_refl _ _

/-- Rigidity leaves one separate summand for every possible decoration of the
chosen representative. Different list indices are distinct choices. -/
def choicesEquivClass : L.Choices ≃ L.Class :=
  Equiv.ofBijective L.ofChoices ⟨L.ofChoices_injective,L.ofChoices_surjective⟩

@[simp] theorem choicesEquivClass_apply (x : L.Choices) :
    L.choicesEquivClass x = L.classOf ⟨x.1.out,x.2⟩ := rfl

instance [∀ A, Fintype (L.Label A)] : Fintype L.Class :=
  Fintype.ofEquiv _ L.choicesEquivClass

/-- Summation over decorated isomorphism classes counts the labels of each
bare representative with multiplicity one. -/
theorem sum_valid_classes {K : Type*} [AddCommMonoid K] [∀ A, Fintype (L.Label A)]
    (weight : L.Class → K) :
    (∑ c : MapClass N, ∑ a : L.Label c.out, weight (L.classOf ⟨c.out,a⟩)) =
      ∑ x : L.Class, weight x := by
  rw [← Fintype.sum_sigma']
  exact L.choicesEquivClass.sum_comp weight

variable {N' : ℕ} (T : Family.{v} N')

/-- Inverse constructions on named presentations descend as soon as they
respect isomorphisms and their two composites have the required
decoration-preserving isomorphisms. -/
def equivOfIsoForwardInverse (forward : L.Rep → T.Rep) (reverse : T.Rep → L.Rep)
    (hf : ∀ a b, L.IsIso a b → T.IsIso (forward a) (forward b))
    (hr : ∀ a b, T.IsIso a b → L.IsIso (reverse a) (reverse b))
    (left : ∀ a, L.IsIso (reverse (forward a)) a)
    (right : ∀ b, T.IsIso (forward (reverse b)) b) :
    L.Class ≃ T.Class where
  toFun := Quotient.map forward hf
  invFun := Quotient.map reverse hr
  left_inv x := Quotient.inductionOn x (fun a => Quotient.sound (left a))
  right_inv y := Quotient.inductionOn y (fun b => Quotient.sound (right b))

/-- Reindex the actual finite sums over map classes and choices, using
pointwise contraction preservation on named presentations. -/
theorem sum_forward_reverse {K : Type*} [AddCommMonoid K]
    [∀ A, Fintype (L.Label A)] [∀ B, Fintype (T.Label B)]
    (forward : L.Rep → T.Rep) (reverse : T.Rep → L.Rep)
    (hf : ∀ a b, L.IsIso a b → T.IsIso (forward a) (forward b))
    (hr : ∀ a b, T.IsIso a b → L.IsIso (reverse a) (reverse b))
    (left : ∀ a, L.IsIso (reverse (forward a)) a)
    (right : ∀ b, T.IsIso (forward (reverse b)) b)
    (u : L.Class → K) (v : T.Class → K)
    (preserve : ∀ a, u (L.classOf a) = v (T.classOf (forward a))) :
    (∑ c : MapClass N, ∑ a : L.Label c.out, u (L.classOf ⟨c.out,a⟩)) =
    ∑ c : MapClass N', ∑ b : T.Label c.out, v (T.classOf ⟨c.out,b⟩) := by
  rw [L.sum_valid_classes, T.sum_valid_classes]
  apply Fintype.sum_equiv (L.equivOfIsoForwardInverse T forward reverse hf hr left right)
  intro x
  induction x using Quotient.inductionOn with
  | _ a => exact preserve a

end Family

open UniformDecorations

variable {K : Type*} {s h : ℕ}

/-- The concrete family of vertex decorations that pass the local tests.
The vertex numbering is transported along the map isomorphism. -/
def validFamily (S : Spec K s h) (N : ℕ) : Family N where
  Label A := {d : Fin A.vertexCount.val → Bits h // S.Valid (view A.map) d}
  move {A B} f :=
    { toFun d := ⟨d.val ∘ f.vertex.symm, (S.valid_iso f d.val _ (by simp)).mp d.property⟩
      invFun d := ⟨d.val ∘ f.vertex, (S.valid_iso f _ d.val (fun _ => rfl)).mpr d.property⟩
      left_inv := fun d => Subtype.ext (by funext v; simp)
      right_inv := fun d => Subtype.ext (by funext v; simp) }
  move_refl _ _ := rfl
  move_trans _ _ _ := rfl

instance (S : Spec K s h) (N : ℕ) (A : MapRep N) :
    Fintype ((validFamily S N).Label A) :=
  inferInstanceAs (Fintype {d : Fin A.vertexCount.val → Bits h // S.Valid (view A.map) d})

variable [CommSemiring K] (S : Spec K s h)

/-- The scalar attached to a decorated isomorphism class. -/
def weight {N : ℕ} : (validFamily S N).Class → K :=
  Quotient.lift (fun x : (validFamily S N).Rep =>
    S.decoratedContraction (view x.1.map) x.2.val) (by
      rintro a b ⟨f,hf⟩
      apply S.decoratedContraction_iso f
      intro v
      have := congrFun (congrArg Subtype.val hf) (f.vertex v)
      change (a.2.val ∘ f.vertex.symm) (f.vertex v) = b.2.val (f.vertex v) at this
      simpa using this.symm)

/-- The encoded table functional is exactly the sum over decorated map classes. -/
theorem Z_eq_sum_valid_classes (N : ℕ) :
    Z N (width s h) S.compiled = ∑ q : (validFamily S N).Class, weight S q := by
  rw [S.Z_compiled, ← Family.sum_valid_classes]
  apply Finset.sum_congr rfl
  intro c _
  symm
  let incl : (validFamily S N).Label c.out → (Fin c.out.vertexCount.val → Bits h) := Subtype.val
  apply Fintype.sum_of_injective incl Subtype.val_injective
  · intro d hd
    apply ite_eq_right
    exact fun hv => hd ⟨⟨d,hv⟩,rfl⟩
  · intro d
    change S.decoratedContraction (view c.out.map) d.val = _
    simp only [incl, d.property, ite_true]

end DecoratedMaps

end

end SpectralBooks
end LinearAlgebra
end OAI
