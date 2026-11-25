import OAI.Hierarchy.ProtocolRAMCalendarModeLaw
import OAI.Hierarchy.ProtocolRAMCalendarArena
import OAI.Hierarchy.ProtocolRAMBelow

namespace OAI
/-! # The adaptive gate consults strictly earlier chronological mode receipts -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {w q goods : ℕ}

/-- At a mounted actual trial, the stored stop byte depends only on those
earlier mode cells. Neither current nor subsequent selector registers
enter the comparison, including saturated and disabled slots. -/
theorem prepared_stop_equal (C : Chart w q goods) (a : Attempt) (left right : Memory w)
    (readyL : ready C (.attempt a) left) (readyR : ready C (.attempt a) right)
    (room : stopRoom C a) (wide : 4≤2^w)
    (seen : ∀b,position C.mesh (.attempt b)<position C.mesh (.attempt a)→left (C.modeAt b)=right (C.modeAt b)) :
    AttemptGate.bit (repair C a).tests.stop (prepared C a left)=
      AttemptGate.bit (repair C a).tests.stop (prepared C a right) := by
  have h:=agrees_earlier C.mesh (archive C.modeAt left) (archive C.modeAt right) a
    (fun b hb=>congrArg Fin.val (seen b hb))
  have vote := disabled_congr C.mesh _ _ a h
  have atStop (m : Memory w) (fit : ready C (.attempt a) m) :
      prepared C a m (C.stopAt a) =
        (if disabled C.mesh (archive C.modeAt m) a then (1 : Word w) else 0) := by
    calc
      _ = (guard C a).apply m (C.stopAt a) := (C.frozen a).frame _ _ fit.2.1 room.1
      _ = _ := by
        change image (C.stopAt a) 1 (stop C.mesh C.modeAt a) m (C.stopAt a) = _
        simp [image, fillSegment, stop_snapshot _ _ _ _ _ wide]
  change decide (prepared C a left (C.stopAt a) ≠ 0) =
    decide (prepared C a right (C.stopAt a) ≠ 0)
  rw [atStop left readyL, atStop right readyR]
  by_cases cut : disabled C.mesh (archive C.modeAt left) a
  · rw [ite_eq_left cut, ite_eq_left (vote.mp cut)]
  · rw [ite_eq_right cut, ite_eq_right (fun h => cut (vote.mpr h))]

end Hierarchy.ProtocolRAM.Calendar

end OAI
