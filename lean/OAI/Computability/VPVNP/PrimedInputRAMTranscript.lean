import OAI.Computability.VPVNP.RAMSharedFields
import Mathlib.Tactic.FinCases

/-!
# Addressing internal transcript bits for the paired-group counter

Section 11 of *VP and VNP differ over every field* chooses each internal
directed-message bit at its sending endpoint. The second pass reads this
bit at either endpoint, while the two absent successor ports return zero.
The scratch location is the sender site and the sender's local input offset.
This address calculation uses only public indices.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open RAMLayout

variable {d H w : ℕ}

/-- Compute the designated sending endpoint, using only the slot indices. -/
def sourcePort : Endpoint d H w → Option (Endpoint d H w)
  | (v, .inl (dir, j)) =>
    if dir = 0 then
      if v.val + 1 < 2 ^ d then some (v, .inl (0, j)) else none
    else
      if 0 < v.val then some (⟨v.val - 1, by omega⟩, .inl (0, j)) else none
  | (v, .inr (l, dir, j)) =>
    some (if dir = 0 then v else l.partner v, .inr (l, 0, j))

theorem sourcePort_eq_source (x : Endpoint d H w) : sourcePort x = source x := by
  rcases x with ⟨v, ⟨dir, j⟩ | ⟨l, dir, j⟩⟩ <;> fin_cases dir
  · by_cases hv : v.val + 1 < 2 ^ d <;> simp [sourcePort, source, peer, direction, hv]
  · by_cases hv : 0 < v.val <;> simp [sourcePort, source, peer, direction, hv]
  · rfl
  · rfl

/-- The first pass chooses one bit at each actual successor or sorting send. -/
def designated : Endpoint d H w → Bool
  | (v, .inl (dir, _)) => decide (dir = 0 ∧ v.val + 1 < 2 ^ d)
  | (_, .inr (_, dir, _)) => decide (dir = 0)

theorem designated_iff (x : Endpoint d H w) : designated x = true ↔ IsSend x := by
  rcases x with ⟨v, ⟨dir, j⟩ | ⟨l, dir, j⟩⟩ <;> fin_cases dir
  · by_cases hv : v.val + 1 < 2 ^ d <;> simp [designated, IsSend, direction, peer, hv]
  · simp [designated, IsSend, direction]
  · simp [designated, IsSend, direction, peer]
  · simp [designated, IsSend, direction]

/-- The bit-choice domain of the first pass is exactly the primed transcript's
shared-bit domain. -/
def designatedEquiv (d H w : ℕ) : {x : Endpoint d H w // designated x = true} ≃ SharedBit d H w :=
  Equiv.subtypeEquivRight designated_iff

theorem sourcePort_eq_self_iff (x : Endpoint d H w) :
    sourcePort x = some x ↔ designated x = true := by
  rw [sourcePort_eq_source, designated_iff]
  refine ⟨source_shared, ?_⟩
  rintro ⟨hd, hp⟩
  cases h : peer x.1 x.2 with
  | none => simp [h] at hp
  | some y => simp [source, h, hd]

/-- Every lookup that finds a sender terminates there. -/
theorem sourcePort_idempotent {x y : Endpoint d H w} (h : sourcePort x = some y) :
    sourcePort y = some y :=
  (sourcePort_eq_self_iff y).mpr ((designated_iff y).mpr
    (source_shared ((sourcePort_eq_source x).symm.trans h)))

/-- Rectangular scratch coordinates within one of the two groups. -/
abbrev Address (d H w : ℕ) := Fin (2 ^ d) × Fin (width d H w)

/-- Identify a transcript endpoint with its site index and its local bit offset in the
rectangular scratch array. -/
def portAddress (d H w : ℕ) : Endpoint d H w ≃ Address d H w :=
  (Equiv.refl _).prodCongr (offset d H w)

/-- In the first pass only designated cells are assigned a choice bit. -/
def scratchBits (bits : SharedBit d H w → Bool) (a : Address d H w) : Bool :=
  let x := (portAddress d H w).symm a
  if h : designated x = true then bits ((designatedEquiv d H w) ⟨x, h⟩) else false

/-- In the second pass every connected port makes one scratch read.
A missing connection returns zero without reading the scratch array. -/
def readPort (bits : SharedBit d H w → Bool) (x : Endpoint d H w) : Bool :=
  ((sourcePort x).map (fun y ↦ scratchBits bits (portAddress d H w y))).getD false

theorem scratchBits_designated (bits : SharedBit d H w → Bool) (x : SharedBit d H w) :
    scratchBits bits (portAddress d H w x.val) = bits x := by
  simp [scratchBits, (designated_iff x.val).mpr x.property, designatedEquiv]
  rfl

/-- Reading a primed endpoint supplies exactly the bit obtained by identifying
its transcript ports, for every assignment of sends. -/
theorem readPort_eq_assignment (bits : SharedBit d H w → Bool) (x : Endpoint d H w) :
    readPort bits x = ((assignmentEquiv d H w) bits).val x := by
  unfold readPort
  rw [sourcePort_eq_source]
  change _ = ((source x).map _).getD false
  cases h : source x with
  | none => rfl
  | some y =>
    have hy := source_shared h
    exact (scratchBits_designated bits ⟨y, hy⟩).trans (by
      change bits ⟨y, hy⟩ = if h' : IsSend y then bits ⟨y, h'⟩ else false
      rw [dite_eq_left hy])

/-- Correctness at a linear incident-input offset. No message parser
participates in this read. -/
theorem readPort_eq_incident (bits : SharedBit d H w → Bool) (v : Fin (2 ^ d))
    (k : Fin (width d H w)) :
    readPort bits (v, (offset d H w).symm k) =
      incidentBits (sendArraysEquiv d H w bits) v k := by
  rw [readPort_eq_assignment]
  simp [incidentBits, incidentEquiv]

end PrimedInputRAM

end VPVNP
end Computability
end OAI
