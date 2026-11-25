import OAI.LinearAlgebra.TensorSpectrum.Additive.Catalyst
import Mathlib.Data.Quot

/-!
# The stable additive group of a commutative semiring

Pairs represent formal differences. Two pairs agree if their cross sums become
equal after adding one common catalyst. This relation works without cancellation
in the original semiring.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

variable {S : Type*} [CommSemiring S]

private def stablePairRel (p q : S × S) : Prop :=
  ∃ c : S, p.1 + q.2 + c = q.1 + p.2 + c

private theorem stablePairRel_refl (p : S × S) : stablePairRel p p :=
  ⟨0, rfl⟩

private theorem stablePairRel_symm {p q : S × S}
    (h : stablePairRel p q) : stablePairRel q p := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.symm⟩

private theorem stablePairRel_trans {p q r : S × S}
    (hpq : stablePairRel p q) (hqr : stablePairRel q r) :
    stablePairRel p r := by
  obtain ⟨c, hc⟩ := hpq
  obtain ⟨d, hd⟩ := hqr
  refine ⟨q.2 + c + d, ?_⟩
  calc
    p.1 + r.2 + (q.2 + c + d) = (p.1 + q.2 + c) + (r.2 + d) := by ring
    _ = (q.1 + p.2 + c) + (r.2 + d) := by rw [hc]
    _ = (q.1 + r.2 + d) + (p.2 + c) := by ring
    _ = (r.1 + q.2 + d) + (p.2 + c) := by rw [hd]
    _ = r.1 + p.2 + (q.2 + c + d) := by ring

private def stablePairSetoid (S : Type*) [CommSemiring S] : Setoid (S × S) where
  r := stablePairRel
  iseqv := ⟨stablePairRel_refl, stablePairRel_symm, stablePairRel_trans⟩

/-- The additive group obtained by identifying formal differences whose cross
sums agree after adjoining one common catalyst. -/
def StableGroup (S : Type*) [CommSemiring S] := Quotient (stablePairSetoid S)

namespace StableGroup

/-- The formal difference represented by `(a, b)`. -/
def mk (a b : S) : StableGroup S := Quotient.mk _ (a, b)

@[simp]
theorem mk_eq_mk_iff (a b c d : S) :
    mk a b = mk c d ↔ ∃ u : S, a + d + u = c + b + u :=
  Quotient.eq

private theorem stablePairRel_add {p p' q q' : S × S}
    (hp : stablePairRel p p') (hq : stablePairRel q q') :
    stablePairRel (p.1 + q.1, p.2 + q.2) (p'.1 + q'.1, p'.2 + q'.2) := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨d, hd⟩ := hq
  refine ⟨c + d, ?_⟩
  change (p.1 + q.1) + (p'.2 + q'.2) + (c + d) =
    (p'.1 + q'.1) + (p.2 + q.2) + (c + d)
  calc
    (p.1 + q.1) + (p'.2 + q'.2) + (c + d) =
        (p.1 + p'.2 + c) + (q.1 + q'.2 + d) := by ring
    _ = (p'.1 + p.2 + c) + (q'.1 + q.2 + d) := by rw [hc, hd]
    _ = (p'.1 + q'.1) + (p.2 + q.2) + (c + d) := by ring

private theorem stablePairRel_swap {p q : S × S}
    (h : stablePairRel p q) : stablePairRel (p.2, p.1) (q.2, q.1) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  change p.2 + q.1 + c = q.2 + p.1 + c
  simpa only [add_comm] using hc.symm

instance : Zero (StableGroup S) := ⟨mk 0 0⟩

instance : Add (StableGroup S) :=
  ⟨Quotient.map₂ (fun p q : S × S => (p.1 + q.1, p.2 + q.2))
    (fun _ _ hp _ _ hq => stablePairRel_add hp hq)⟩

instance : Neg (StableGroup S) :=
  ⟨Quotient.map (fun p : S × S => (p.2, p.1))
    (fun _ _ h => stablePairRel_swap h)⟩

@[simp]
theorem mk_zero_zero : mk (0 : S) 0 = 0 := rfl

@[simp]
theorem mk_add (a b c d : S) : mk a b + mk c d = mk (a + c) (b + d) := rfl

@[simp]
theorem mk_neg (a b : S) : -mk a b = mk b a := rfl

instance : AddCommGroup (StableGroup S) where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  add_assoc x y z := by
    refine Quotient.inductionOn₃ x y z ?_
    intro p q r
    change mk ((p.1 + q.1) + r.1) ((p.2 + q.2) + r.2) =
      mk (p.1 + (q.1 + r.1)) (p.2 + (q.2 + r.2))
    simp only [add_assoc]
  zero_add x := by
    refine Quotient.inductionOn x ?_
    intro p
    change mk (0 + p.1) (0 + p.2) = mk p.1 p.2
    simp only [zero_add]
  add_zero x := by
    refine Quotient.inductionOn x ?_
    intro p
    change mk (p.1 + 0) (p.2 + 0) = mk p.1 p.2
    simp only [add_zero]
  add_comm x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro p q
    change mk (p.1 + q.1) (p.2 + q.2) = mk (q.1 + p.1) (q.2 + p.2)
    simp only [add_comm]
  neg_add_cancel x := by
    refine Quotient.inductionOn x ?_
    intro p
    change mk (p.2 + p.1) (p.1 + p.2) = mk 0 0
    apply Quotient.sound
    exact ⟨0, by change (p.2 + p.1) + 0 + 0 = 0 + (p.1 + p.2) + 0; ring⟩
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Every stable group element is represented by one pair. -/
theorem exists_mk (x : StableGroup S) : ∃ a b : S, x = mk a b := by
  refine Quotient.inductionOn x ?_
  intro p
  exact ⟨p.1, p.2, rfl⟩

/-- The canonical additive map into the stable group. -/
def embed : S →+ StableGroup S where
  toFun a := mk a 0
  map_zero' := rfl
  map_add' a b := by
    change mk (a + b) 0 = mk (a + b) (0 + 0)
    rw [zero_add]

@[simp]
theorem embed_apply (a : S) : embed a = mk a 0 := rfl

/-- Equality of embedded semiring elements is exactly stable equality. -/
theorem embed_eq_embed_iff (a b : S) :
    embed a = embed b ↔ StableEquality a b := by
  change mk a 0 = mk b 0 ↔ ∃ c : S, a + c = b + c
  rw [mk_eq_mk_iff]
  simp only [add_zero]

/-- A pair is zero exactly when its two entries are stably equal. -/
theorem mk_eq_zero_iff (a b : S) : mk a b = 0 ↔ StableEquality a b := by
  change mk a b = mk 0 0 ↔ ∃ c : S, a + c = b + c
  rw [mk_eq_mk_iff]
  simp only [zero_add, add_zero]

/-- Formal pairs are differences of canonical embedded elements. -/
theorem mk_eq_sub_embed (a b : S) : mk a b = embed a - embed b := by
  rw [sub_eq_add_neg]
  change mk a b = mk (a + 0) (0 + b)
  simp only [add_zero, zero_add]

end StableGroup

end OAI.LinearAlgebra.TensorSpectrum
