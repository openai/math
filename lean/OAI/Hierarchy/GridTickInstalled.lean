import OAI.Hierarchy.GridProgrammed
import OAI.Hierarchy.GridReceiverHeader

namespace OAI
/-! # Executing a selected fiber in the tick chosen before its program -/

namespace Hierarchy.TickSelection
open ThreeFlat Diagonal RAM Computability.VPVNP.BurstRAM PrivateRAM
variable {F : Type*} [Field F] [Fintype F] {Q : ℕ→ℕ} {D : ℕ→ℝ} {k A w : ℕ}
variable (T : TickSelection F k A w Q D)
local notation "arch" => GridDescription.capacity w
local notation "size" => GridScale.pins w (GridScale.overhead Q D w)
local notation "chosen" => UniversalTick.tick T.fieldRoom T.tickFit.width T.tickFit.labels
  0 0 T.tickFit.header T.tickFit.time arch arch

include T

/-- Every later receiver with the prescribed padded architecture has exactly
the same clock, circuit and input arity as the selected approximation. -/
theorem receiverFits (M : Machine (64*w) arch arch arch) :
    NativeTrace.Fits M size 0 (UniversalTick.depth w UniversalTick.saving)
      (UniversalTick.clock w UniversalTick.saving) :=
  ⟨T.tickFit.width,T.tickFit.labels,T.active,T.tickFit.header,T.tickFit.time,
    T.tickFit.grid,T.tickFit.text,T.tickFit.mount⟩

omit [Field F] [Fintype F] T in
/-- Replacing the initial tape by the installation primitive in the trace
definition is extensionally the identity on an honestly prefixed local tape. -/
theorem pin_eq (M : Machine (64*w) arch arch arch) (input : ℕ→Bool)
    (bits : ∀ i,input i.val=NativeTrace.executable M i) :
    TraceBitHeader.advicePins (S:=size) 0 (NativeTrace.executable M) input=
      fun j=>input j.val := by
  funext j
  unfold TraceBitHeader.advicePins
  split
  next h => exact (bits ⟨_,h.2⟩).symm
  next => rfl

/-- Transfers the native result of the physical receiver, on the very same
local pin bits, into the preselected universal tick. -/
theorem receiver_value (M : Machine (64*w) arch arch arch) (input : ℕ→Bool) (y : F)
    (bits : ∀ i,input i.val=NativeTrace.executable M i)
    (actual : (NativeTrace.network M (T.receiverFits M) T.fieldRoom 0).eval
      (TraceBitHeader.advicePins 0 (NativeTrace.executable M) input)=y) :
    (chosen).eval (fun j=>input j.val)=y := by
  rw [pin_eq (Q := Q) (D := D) M input bits] at actual
  exact actual


end Hierarchy.TickSelection

end OAI
