import OAI.Optimization.LinearProgramming.PrimalDual.CallSegmentsRoute

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace CallSegments

open RAM RAM.Call RAM.Tape RAM.Block Polynomial Bridge

/-- The returned physical memory for the recorded original call contains the
same canonical result and saved input used by the ordinary optimizer. -/
theorem first_parts (p : Program) (C E : ℕ) {m d H G k tag : ℕ}
    (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ) (c : Fin d → ℚ)
    (zero : 3 ≤ H) (wide : H ≤ G) (safe : Within H (start [m,d] (lpInput A b++List.ofFn c)).memory)
    (tr : Fin (k+1) → State ℚ) (guestRun : Trace p (start [m,d] (lpInput A b)) k tr)
    (counted : k ≤ polyBound C E (m+d)) (bounds : ∀ i, scalarBound H (tr i))
    (valid : FeasibilityOutput A b (tr (Fin.last k))) (tagged : (tr (Fin.last k)).output = some tag) :
    ∃ n ≤ firstCost p C E m d+2*k, ∃ after,
      Joined (program p C E) p G (firstParts p C E A b tag) (start [m,d] (lpInput A b++List.ofFn c)) n
        (after.atPC (firstReturn (firstReturnBase p C E) tag)) ∧ Within H after ∧
      AfterFirst p C E m d (lpInput A b) (List.ofFn c) (tr (Fin.last k)) after := by
  let xs := lpInput A b
  let obj := List.ofFn c
  have hx : xs.length = primalLength m d := lpInput_length A b
  have hy : obj.length = d := List.length_ofFn
  have hz : ratBits (0:ℚ) ≤ H := zero
  have layout := withFirstCall_locations p C E firstReturn (endingCode p)
  obtain ⟨v,r,prep,hr,ready⟩ := firstPrelude_correct (P:=fun x : ℚ => ratBits x ≤ H) p C E m d xs obj hx hy hz safe
  obtain ⟨l,hl,after,call,frame⟩ := record (valid:=FeasibilityOutput A b) v layout.2.1 ready.data ready.index
    prep.safe_end tr guestRun bounds valid tagged
  have startPart : Realizes (program p C E) p G (.fixed 0 (firstPrelude p C E))
      (start [m,d] (xs++obj)) r (v.atPC (firstPrelude p C E).size) := by
    have entry : (start [m,d] (xs++obj)).memory.atPC 0 = start [m,d] (xs++obj) := rfl
    simpa only [program,entry,Nat.zero_add] using Realizes.fixed (guest:=p) layout.1 (widenBlock prep wide)
  have whole := Joined.cons startPart (Joined.single (Realizes.embedded (record_widen call wide)))
  -- The previously established virtual footprint is independent of the saved odd bank.
  obtain ⟨_,_,old,_,oldFrame⟩ := normal_first_call (P:=fun x : ℚ => ratBits x ≤ H) p C E m d xs obj hx hy hz safe
    layout.1 layout.2.1 tr guestRun counted bounds tagged
  refine ⟨r+l,Nat.add_le_add hr hl,after,whole,call.physical.safe_end,frame.data,frame.index,?_,
    (frame.callerIndex 4).trans ready.savedRows,(frame.callerIndex 5).trans ready.savedCols,
    (frame.callerIndex 10).trans ready.savedLimit,?_⟩
  · intro i hi
    rw [show 3+2*i = 2*(i+1)+1 by omega,frame.callerData]
    simpa only [show 2*(i+1)+1 = 3+2*i by omega] using ready.saved i hi
  · intro q hq
    by_cases even : q%2 = 0
    · have eq : q = 2*(q/2) := by omega
      rw [eq]
      have vacant := oldFrame.vacant (2*(q/2)) (by omega)
      exact ⟨(frame.data _).trans ((oldFrame.result _).symm.trans vacant.1),
        (frame.index _).trans ((oldFrame.addresses _).symm.trans vacant.2)⟩
    · have eq : q = 2*(q/2)+1 := by omega
      rw [eq,frame.callerData,frame.callerIndex]
      exact ⟨ready.oddDataTail _ (by omega),ready.oddIndexTail _ (by omega)⟩

end CallSegments
end PrimalDual
end LinearProgramming
end Optimization
end OAI
