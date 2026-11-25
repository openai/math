import OAI.Hierarchy.DescentNativeInput
import OAI.Hierarchy.DescentSeedRawBallot

namespace OAI
/-! # Bit selectors of the physical initial-group choice and their exact inverse -/
namespace Hierarchy.DescentSeedRoot
open Hierarchy.DescentInitialHost DescentSixParty Computability.BorderVNP.Crossing
open ThreeFlat Routing Catalyst Diagonal
open Computability.VPVNP.BurstRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p) {R s w : ℕ}

def selected (c : (initialGroup X R s).Choice)
    (key : Fin R × (Σ v : Old X,LocalPattern X v)) : ℕ :=
  (c key.1 (.inl key.2.1) key.2.2).val

def selectBit (w : ℕ) (c : (initialGroup X R s).Choice) (q : Select X R s) : Bool :=
  ((selected X c q.1 : Word w).val).testBit q.2.val

theorem selected_bound (c : (initialGroup X R s).Choice) (key : CountKey X R) :
    selected X c key≤ s := Nat.le_of_lt_succ (c key.1 (.inl key.2.1) key.2.2).isLt

theorem raw_select (room : s<2^w) (c : (initialGroup X R s).Choice) (key : CountKey X R) :
    (rawCount X (selectBit X w c) key).val=selected X c key := by
  let n := selected X c key
  have hn : n < 2^(digitsNeeded s) := (selected_bound X c key).trans_lt (Nat.lt_log2_self (n:=s))
  have hw : n < 2^w := (selected_bound X c key).trans_lt room
  have eq : rawCount X (selectBit X w c) key=(n : Word (digitsNeeded s)) := by
    apply (bitWord _).injective
    funext b
    change _=(n%(2^(digitsNeeded s))).testBit b.val
    rw [Nat.mod_eq_of_lt hn]
    change (rawCount X (selectBit X w c) key).val.testBit b.val=_
    rw [raw_digits]
    change (n%(2^w)).testBit b.val=n.testBit b.val
    rw [Nat.mod_eq_of_lt hw]
  exact (congrArg Fin.val eq).trans (Nat.mod_eq_of_lt hn)

theorem valid_select (room : s<2^w) (c : (initialGroup X R s).Choice) :
    valid X (selectBit X w c) := fun key=>(raw_select X room c key).le.trans (selected_bound X c key)

/-- Ordinary input sites carry census choices. Exterior hub sites have their unique unit choice. -/
def choices (z : Select X R s→Bool) (ok : valid X z) : (initialGroup X R s).Choice :=
  fun j u=>match u with
  | .inl v=>fun pat=>⟨(rawCount X z (j,⟨v,pat⟩)).val,Nat.lt_succ_of_le (ok _)⟩
  | .inr _=>()

theorem choices_select (room : s<2^w) (c : (initialGroup X R s).Choice) :
    choices X (selectBit X w c) (valid_select X room c)=c := by
  funext j u
  cases u with
  | inl v=>
    funext pat
    apply Fin.ext
    exact raw_select X room c (j,⟨v,pat⟩)
  | inr _ => exact Subsingleton.elim (α := PUnit) _ _

theorem select_choices (room : s<2^w) (z : Select X R s→Bool) (ok : valid X z) :
    selectBit X w (choices X z ok)=z := by
  funext a
  rcases a with ⟨key,b⟩
  change ((rawCount X z key).val%2^w).testBit b.val=_
  rw [Nat.mod_eq_of_lt ((ok key).trans_lt room),raw_digits]

def decode (z : Select X R s→Bool) : Option (initialGroup X R s).Choice :=
  if ok : valid X z then some (choices X z ok) else none

theorem decode_iff (room : s<2^w) (z : Select X R s→Bool) (c : (initialGroup X R s).Choice) :
    decode X z=some c ↔ z=selectBit X w c := by
  constructor
  · intro h
    unfold decode at h
    split at h
    · rename_i ok
      cases Option.some.inj h
      exact (select_choices X room z ok).symm
    · contradiction
  · rintro rfl
    simp [decode,valid_select X room c,choices_select X room c]

theorem invalid_iff (z : Select X R s→Bool) :
    decode X z=none ↔ ∃key,s<(rawCount X z key).val := by
  rw [show decode X z=none ↔ ¬valid X z from by by_cases ok : valid X z <;> simp [decode,ok]]
  simp [valid]

end
end Hierarchy.DescentSeedRoot

end OAI
