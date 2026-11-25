import OAI.Hierarchy.TaggedPinGuard

namespace OAI
/-! # A fixed trivalent signed site for the finite native mode menu -/

noncomputable section
namespace Hierarchy.Tagged.Guard
open ThreeFlat Routing
open scoped Classical BigOperators

variable {F V : Type*} [Fintype V]

/-- Require the indicated bits of a genuine native mode word. Its width
is fixed by the finite public local catalogue. The disabled signed
network has exactly one assignment to its internal wires. -/
def mode [Zero F] [One F] (N : BitNetwork F (Fintype.card V)) :
    {b : ℕ}→(Fin b→V)→(Fin b→Bool)→BitNetwork F (Fintype.card V)
  | 0,_,_=>N
  | _b+1,pin,word=>onPin (pin 0) (word 0) (mode N (pin ∘ Fin.succ) (word ∘ Fin.succ))

theorem mode_value [CommSemiring F] (N : BitNetwork F (Fintype.card V)) {b : ℕ}
    (pin : Fin b→V) (word : Fin b→Bool) (x : V→Bool) :
    TypedWiring.value (mode N pin word) x =
      if x ∘ pin=word then TypedWiring.value N x else 1 := by
  induction b with
  | zero => simp [mode,Subsingleton.elim (x ∘ pin) word]
  | succ b ih =>
    rw [mode,onPin_eval,ih]
    have decomp : x ∘ pin=word ↔ x (pin 0)=word 0 ∧ x ∘ (pin ∘ Fin.succ)=word ∘ Fin.succ := by
      constructor
      · rintro eqn
        exact ⟨congrFun eqn 0,funext fun j=>congrFun eqn j.succ⟩
      · rintro ⟨head,tail⟩
        exact funext (Fin.cases head (fun j=>congrFun tail j))
    by_cases hd : x (pin 0)=word 0 <;> simp [decomp,hd]

theorem mode_fee [Zero F] [One F] (N : BitNetwork F (Fintype.card V)) {b : ℕ}
    (pin : Fin b→V) (word : Fin b→Bool) :
    (mode N pin word).cells+(mode N pin word).internal≤177^b*(N.cells+N.internal) := by
  induction b with
  | zero=>simp [mode]
  | succ b ih=>
    calc
      _ ≤ 177*((mode N (pin ∘ Fin.succ) (word ∘ Fin.succ)).cells+
          (mode N (pin ∘ Fin.succ) (word ∘ Fin.succ)).internal) := onPin_size ..
      _ ≤ 177*(177^b*(N.cells+N.internal)) := Nat.mul_le_mul_left _ (ih _ _)
      _ = _ := by rw [pow_succ];ring

/-- Every public alternative is present, and the single value read
from the concrete post-memory selects the original signed local factor. -/
theorem modes_value [CommSemiring F] {I : Type*} [Fintype I] {b : ℕ}
    (N : I→BitNetwork F (Fintype.card V)) (pin : Fin b→V) (word : I ↪ (Fin b→Bool))
    (i : I) (x : V→Bool) (read : x ∘ pin=word i) :
    (∏ j,TypedWiring.value (mode (N j) pin (word j)) x) = TypedWiring.value (N i) x := by
  simp only [mode_value,read,word.injective.eq_iff]
  classical
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ ne
    simp [Ne.symm ne]
  · simp

end Hierarchy.Tagged.Guard

end
end OAI
