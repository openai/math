import OAI.Computability.VPVNP.LiveHeaderScanRows
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-!
# Processor-site preservation during arbitrary scheduled scans

Even a malformed count or offset cannot redirect a write into the processor
sites. The public cursor guard bounds the destination within its allocated
buffer on every successful copy call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram.ScanRows

open BurstRAM BurstRAM.PrivateRAM LiveHeaderSchedule LiveHeaderDescriptors LiveHeader
open scoped Fin.CommRing

variable {w : ℕ}

private theorem payload_address (s : Sizes) (base : ℕ) (side : Side) (f : Field)
    (fit : limit s base ≤ 2^w) (hf : f ≠ .padding) (st : Word w) (cursor : st < (s.capacity f : Word w)) :
    base ≤ (Allocated.destination scanSlots (scalarPub w s base (.scan side f)) st).val := by
  let pub := scalarPub w s base (.scan side f)
  obtain ⟨zero, _, _, destWord⟩ := scan_public fit side f
  obtain ⟨lo, hi⟩ := dest_bounds s base side f hf
  have capFit := field_capacity_lt fit f
  have hcursor : st.val < s.capacity f := by
    change st.val < (s.capacity f : Word w).val at cursor
    rwa [Fin.val_cast_of_lt capFit] at cursor
  have destFit : dest s base side f < 2^w := by omega
  have destVal : (pub scanSlots.destinationBase).val = dest s base side f := by
    rw [show pub scanSlots.destinationBase = _ from destWord]
    exact Nat.mod_eq_of_lt destFit
  change base ≤ (pub scanSlots.destinationBase + (st - pub scanSlots.firstCursor)).val
  rw [show pub scanSlots.firstCursor = _ from zero, sub_zero, Fin.val_add, destVal,
    Nat.mod_eq_of_lt (by omega)]
  dsimp [adviceBase, rightIndexBase, leftIndexBase, populationAddr, highAddr, indexBase] at lo
  omega

/-- Any successful scheduled scan preserves every address below the scratch base,
even with arbitrary descriptor words, branch input and initial cursor. -/
theorem call_preserves_below (s : Sizes) (base : ℕ) (side : Side) (f : Field)
    (fit : limit s base ≤ 2^w) (fuel : ℕ) (st : Word w) (m : Memory w) (bits : List Bool)
    {rep : Report w}
    (run : let P := ((stageTemplate (.scan side f)).2.instantiate w (rowData w s base (.scan side f))).program
      execute P fuel (P.start st) m bits = some rep) (a : ℕ) (ha : a < base) :
    after m rep.events a = m a := by
  let pub := scalarPub w s base (.scan side f)
  let pad := decide (f = .padding)
  let addr : Word w := Fin.ofNat _ a
  have addrVal : addr.val = a := Nat.mod_eq_of_lt (by rw [limit_eq] at fit; omega)
  have bounded := (execute_scan s base side f fuel st m bits).symm.trans run
  apply LiveHeaderBounded.frame_any (Allocated.table scanSlots (cutSlot side) pad) pub
    (s.capacity f : Word w) fuel st m bits rep bounded a
  intro inner raw cursor source
  rw [← addrVal]
  apply Allocated.report_frame scanSlots (cutSlot side) pad pub st m bits inner source addr _ m
  intro _
  by_cases hf : f = .padding
  · exact Or.inl (decide_eq_true hf)
  · apply Or.inr
    intro eq
    have lo := payload_address s base side f fit hf st cursor
    change base ≤ (Allocated.destination scanSlots pub st).val at lo
    rw [← eq, addrVal] at lo
    omega

end LiveHeaderProgram.ScanRows

end VPVNP
end Computability
end OAI
