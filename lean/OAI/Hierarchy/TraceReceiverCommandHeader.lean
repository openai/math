import OAI.Hierarchy.TraceReceiverPreparation
import OAI.Hierarchy.TraceReceiverIssuedCommands

namespace OAI
/-! # The actual interval header used by the seven-column terminal writer -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Issued
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open PhysicalProcedure DescriptorScan
open scoped Fin.CommRing

theorem header_words {W : ℕ} (current count commands n : ℕ) (m : Memory W)
    (fits : current+7<2^W) (small : count<2^W) (read : m count=(n:Word W)) :
    let r:=TraceReceiverTasks.rangeImage current count commands 0 7 m
    r (r (current:Word W).val+0).val=(commands:Word W) ∧
    r (r (current:Word W).val+1).val=((7*n:ℕ):Word W) := by
  intro r
  have field (j : Fin 7) := TraceReceiverTasks.range_at current count commands 0 7 m j
  have dir : r current=((current+1:ℕ):Word W):=by simpa [r] using field 0
  have lo : r (current+1)=(commands:Word W):=field 1
  have size : r (current+2)=((7*n:ℕ):Word W):=by
    have f := field 2
    change r (current+2)=(7:Word W)*m (count:Word W).val at f
    simpa [Fin.val_cast_of_lt small,read,Nat.cast_mul] using f
  have c : (current:Word W).val=current:=Fin.val_cast_of_lt (by omega)
  have next : (((current+1:ℕ):Word W)+1).val=current+2:=by
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  rw [c,dir,add_zero,Fin.val_cast_of_lt (by omega : current+1<2^W),next]
  exact ⟨lo,size⟩

theorem header_frame {W : ℕ} (current count commands : ℕ) (m : Memory W) {z : ℕ}
    (away : z<current ∨ current+7≤z) :
    TraceReceiverTasks.rangeImage current count commands 0 7 m z=m z := by
  simp [TraceReceiverTasks.rangeImage,fillSegment,show ¬(current≤z ∧ z<current+7) by omega]

/-- The header and both writer loops issue the complete true command
table before the gather starts. `m` is the actual memory returned by the
selected terminal map pass. -/
theorem tail_run {W : ℕ} (current cursor commands tasks count n : ℕ) (m : Memory W)
    (room : current+7<2^W) (cursorFit : cursor+2<2^W) (countFit : count<2^W)
    (off : count<current ∨ current+7≤count) (countCursor : count<cursor ∨ cursor+2≤count)
    (countCommands : count<commands ∨ commands+7*n≤count) (word : m count=(n:Word W))
    (limit : commands+7*n<2^W)
    (safe : Commands.Separate tasks commands n (TraceReceiverTasks.rangeImage current count commands 0 7 m)) :
    ((TraceReceiverTasks.rangeSeed W current count commands 0 7).seq
      ((Commands.procedure W current commands tasks).seq (Cursor.program W cursor commands count))).Spec
      (·=m) (fun _ z=>z=image cursor commands tasks n (TraceReceiverTasks.rangeImage current count commands 0 7 m))
      (4096+((13+7224*n)+(4+2*(2*(Cursor.term W cursor commands count).binds+4)))) := by
  let seed:=TraceReceiverTasks.rangeImage current count commands 0 7 m
  obtain ⟨lo,len⟩:=header_words current count commands n m room countFit word
  intro pp rr kk M
  exact followed _ _ m seed _ _ _
    (TraceReceiverTasks.range_bounded current count commands 0 7 m room (by simpa [Fin.val_cast_of_lt countFit] using off))
    (run current cursor commands tasks count n seed limit lo len safe
      ((header_frame current count commands m off).trans word) cursorFit countFit countCursor countCommands) M

end Hierarchy.TraceFactorReceiver.Issued
end

end OAI
