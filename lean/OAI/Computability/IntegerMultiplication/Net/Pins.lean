import OAI.Computability.IntegerMultiplication.Net.Complete
import OAI.Computability.IntegerMultiplication.Net.Pulse

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Tensor
open Finset Matrix Chart
/-- up to two specified line projectors match chart rays. Provide a code identifying
their chart indices (needed below). Other lines unconstrained. -/
structure License (T J R : Type) [DecidableEq T] [Fintype J] [DecidableEq J] [CommRing R]
    (cond : Chart J R → Prop) (project : T → Mat J R) (t u : T) where
  board : Chart J R
  safe : cond board
  identify : T → J
  distinct : t ≠ u → identify t ≠ identify u
  pin : ∀ a, a=t ∨ a=u → project a = board.ray (identify a)

namespace License
variable {T J R : Type} [DecidableEq T] [Fintype J] [DecidableEq J] [CommRing R]

variable (v w : T → Vec J R) {t u : T}
variable (hb : ∀ a, a=t ∨ a=u → ∀ b, b=t ∨ b=u → w a ⬝ᵥ v b = if a=b then 1 else 0)
variable (atA : T → J) (diff : t ≠ u → atA t ≠ atA u)
-- encoding for the two lines
def ids (atA : T → J) (t u : T) : Finset J := {atA t, atA u}
def decode (t u : T) (i : J) : T := if i=atA u then u else t
include diff in
omit [Fintype J] in
theorem decode_at (a) (e : a=t ∨ a=u) : decode atA t u (atA a) = a := by
  by_cases h : t=u
  · rcases e with rfl|rfl <;> simp [decode, h]
  rcases e with rfl|rfl
  · rw [decode, ite_eq_right (diff h)]
  rw [decode, ite_eq_left rfl]
include diff in
omit [Fintype J] in
theorem roundtrip (i) (hi : i∈ids atA t u) : atA (decode atA t u i)=i := by
  rcases (show i=atA t ∨ i=atA u by simpa [ids] using hi) with c|c
  · rw [c, decode_at atA diff _ (Or.inl rfl)]
  rw [c, decode_at atA diff _ (Or.inr rfl)]
omit [DecidableEq T] [Fintype J] in
theorem decode_bound (i : J) : decode atA t u i = t ∨ decode atA t u i = u := by
  unfold decode; split <;> simp

include hb diff in
theorem vec_ortho (i) (hi : i∈ids atA t u) (j) (hj : j∈ids atA t u) :
    (w ∘ decode atA t u) i ⬝ᵥ (v ∘ decode atA t u) j = if i=j then 1 else 0 := by
  rw [Function.comp_apply, Function.comp_apply, hb _ (decode_bound ..) _ (decode_bound ..)]
  by_cases c : i=j
  · simp [c]
  have : decode atA t u i ≠ decode atA t u j := by
    intro e; apply c
    rw [← roundtrip atA diff _ hi, ← roundtrip atA diff _ hj, e]
  simp [c, this]

include diff hb in
theorem byNotch (pivot : ∀ a, a=t ∨ a=u → ∀ b, b=t ∨ b=u →
    v b (atA a) = if a=b then 1 else 0) :
    Nonempty (License T J R (fun _ => True) (fun a => vecMulVec (v a) (w a)) t u) := by
  let P := ids atA t u
  let X := decode atA t u
  have oo := vec_ortho v w hb atA diff
  have ex : ∀ i ∈ P, ∀ j ∈ P,
      (v ∘ X) j i = if i=j then 1 else 0 := by
    intro i hi j hj
    have va := pivot (X i) (decode_bound ..) (X j) (decode_bound ..)
    change v (X j) i = _
    have r : atA (X i) = i := roundtrip atA diff _ hi
    rw [← r, va]
    simp only [r]
    by_cases c : i=j
    · simp [c]
    have : X i ≠ X j := fun o => c (by rw [← r,o, roundtrip atA diff _ hj])
    simp [this,c]
  refine ⟨⟨Notch.mint P (v ∘ X) (w ∘ X) oo ex, trivial, atA, diff, ?_⟩⟩
  intro a h
  have ha : atA a ∈ P := by rcases h with rfl|rfl <;> simp [P, ids]
  rw [Notch.pins P _ _ oo ex _ ha]
  simp only [Function.comp_apply, decode_at atA diff a h]

include diff in
theorem byKick (z : ∀ x : R, x+x=0)
    (hb : ∀ a, a=t ∨ a=u → ∀ b, b=t ∨ b=u → v a ⬝ᵥ v b = if a=b then 1 else 0)
    (zero : ∀ a, a=t ∨ a=u → ∀ b, b=t ∨ b=u → v b (atA a) = 0) :
    Nonempty (License T J R (fun c => c.pull = c.push.transpose)
      (fun a => vecMulVec (v a) (v a)) t u) := by
  let P := ids atA t u
  let X := decode atA t u
  have oo := vec_ortho v v hb atA diff
  have ex : ∀ i ∈ P, ∀ j ∈ P, (v ∘ X) j i = 0 := by
    intro i hi j _
    have va := zero (X i) (decode_bound ..) (X j) (decode_bound ..)
    simpa [roundtrip atA diff i hi, Function.comp_apply, X] using va
  refine ⟨⟨Kick.mint P (v ∘ X) z ex oo, rfl, atA, diff, ?_⟩⟩
  intro a h
  have ha : atA a ∈ P := by rcases h with rfl|rfl <;> simp [P, ids]
  rw [Kick.pins P _ z ex oo _ ha]
  simp only [X, Function.comp_apply, decode_at atA diff a h]

end License
end Net.Tensor

end IntegerMultiplication
end Computability
end OAI
