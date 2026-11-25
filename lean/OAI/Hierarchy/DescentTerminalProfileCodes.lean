import OAI.Hierarchy.DescentSixPartyProfiles
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Raw profile ordinals and unique zero-padded decks -/
namespace Hierarchy.DescentTerminalEpochFlags
open DescentSixParty
open scoped Classical BigOperators
noncomputable section
variable {n C : ℕ}

def alphabet (C : ℕ) := (C+2)^8

def encode (p : Profile C) : ℕ := (finFunctionFinEquiv p.val).val

def decode (C x : ℕ) : Option (Profile C) :=
  if h : x < alphabet C then
    let fields : Fin 8 → Fin (C+2) := finFunctionFinEquiv.symm ⟨x,h⟩
    if pay : (∑i,(fields i).val) ≤ C+8 then some ⟨fields,pay⟩ else none
  else none

@[simp] theorem decode_encode (p : Profile C) : decode C (encode p) = some p := by
  have hr : encode p < alphabet C := (finFunctionFinEquiv p.val).isLt
  have inv : (finFunctionFinEquiv.symm ⟨encode p,hr⟩ : Fin 8→Fin (C+2))=p.val :=
    Equiv.symm_apply_apply finFunctionFinEquiv p.val
  simp only [decode,dite_eq_left hr,inv,dite_eq_left p.property]

theorem encode_of_decode {x : ℕ} {p : Profile C} (hit : decode C x = some p) : encode p=x := by
  unfold decode at hit
  split at hit
  · rename_i h
    dsimp only at hit
    split at hit
    · cases hit
      change (finFunctionFinEquiv (finFunctionFinEquiv.symm ⟨x,h⟩)).val=x
      rw [Equiv.apply_symm_apply]
    · contradiction
  · contradiction

def SeatValid (C count : ℕ) (raw : ℕ) (row : ℕ) : Prop :=
  if row < count then (decode C raw).isSome else raw=0

/-- For the dense number of the actual matched pairs, every accepted string consists of
exactly their eight-field profiles followed by zero words. -/
theorem valid_iff {I : Type*} {count : ℕ} (number : I ≃ Fin count) (bound : count ≤ n)
    (raw : Fin n → ℕ) :
    (∀i,SeatValid C count (raw i) i.val) ↔
    ∃ choice : I → Profile C, ∀i : Fin n,
      raw i = if h : i.val < count then encode (choice (number.symm ⟨i.val,h⟩)) else 0 := by
  constructor
  · intro good
    have found (j : I) :
        (decode C (raw ⟨(number j).val,(number j).isLt.trans_le bound⟩)).isSome := by
      simpa [SeatValid,(number j).isLt] using good ⟨(number j).val,(number j).isLt.trans_le bound⟩
    let choice (j : I) := (decode C (raw ⟨(number j).val,(number j).isLt.trans_le bound⟩)).get (found j)
    have faithful (j : I) : encode (choice j)=raw ⟨(number j).val,(number j).isLt.trans_le bound⟩ :=
      encode_of_decode (Option.some_get (found j)).symm
    refine ⟨choice,fun i => ?_⟩
    by_cases h : i.val < count
    · rw [dite_eq_left h]
      simpa only [Equiv.apply_symm_apply] using (faithful (number.symm ⟨i.val,h⟩)).symm
    · simpa [SeatValid,h] using good i
  · rintro ⟨choice,code⟩ i
    by_cases h : i.val < count <;> simp [SeatValid,code i,h]

theorem valid_unique {I : Type*} {count : ℕ} (number : I ≃ Fin count) (bound : count ≤ n)
    (raw : Fin n → ℕ) (good : ∀i,SeatValid C count (raw i) i.val) :
    ∃! choice : I → Profile C, ∀i : Fin n,
      raw i = if h : i.val < count then encode (choice (number.symm ⟨i.val,h⟩)) else 0 := by
  obtain ⟨p,hp⟩ := (valid_iff number bound raw).mp good
  refine ⟨p,hp,?_⟩
  intro q hq
  funext t
  let i : Fin n := ⟨(number t).val,(number t).isLt.trans_le bound⟩
  have hi : i.val < count := (number t).isLt
  have e : encode (q t) = encode (p t) := by
    simpa [i,hi,(number t).isLt] using (hq i).symm.trans (hp i)
  have d := congrArg (decode C) e
  simpa using d

end
end Hierarchy.DescentTerminalEpochFlags

end OAI
