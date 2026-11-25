import OAI.Hierarchy.TraceReceiverInput
import OAI.Hierarchy.GridReceiverHeader

namespace OAI
/-! # The selector of the receiver's independent navigation archive

The phase address points at the selector tag on the shifted local tape. Both
histogram source addresses point to the following bit. The native input mount
therefore prepares the original selector without a second copying loop. -/

noncomputable section
namespace Hierarchy.TraceFactorReceiver.Selector

open ThreeFlat Diagonal RAM Computability.VPVNP.BurstRAM PrivateRAM
open PhysicalProcedure
open scoped Fin.CommRing

variable {w n cap p : ℕ}

def first (w n text : ℕ) := text+((n+1)*(64*w)+GridReceiverHeader.count w*(64*w))
def phase (w n text : ℕ) := 2+first w n text

def body (sel : Fin (cap+1) → Bool) (i : ℕ) :=
  if h : i<cap then sel (Fin.succ ⟨i,h⟩) else false

variable (text : ℕ) (textRoom : text≤w^2) (self : Fin (w^2)→Bool)
variable (index : Word (64*w)) (params : Fin n→Word (64*w)) (sel : Fin (cap+1)→Bool)
local notation "head" => GridReceiverHeader.header text textRoom self index params sel

/-- The header prefix of the assigned pins; the following pinned data and
padding play no role in any selector read. -/
def headerReads (input : ℕ→Bool) :=
  ∀ i : Fin (head).length,input i.val=(head)[i.val]

theorem word_at (input : ℕ→Bool) (room : (head).length≤p)
    (stored : headerReads text textRoom self index params sel input) (i : Fin (cap+1)) :
    TickMountedPins.memory (w:=64*w) (fun j : Fin p => input j.val)
      (phase w n text+i.val)=((sel i).toNat : Word (64*w)) := by
  let a:=first w n text+i.val
  have hi : a<(head).length := by rw [GridReceiverHeader.length]; dsimp [a,first]; have := i.isLt; omega
  let b : Fin p:=⟨a,hi.trans_le room⟩
  have bit : input a=sel i :=
    (stored ⟨a,hi⟩).trans (GridReceiverHeader.selector_at text textRoom self index params sel i)
  have addr : phase w n text+i.val=2+b.val := by dsimp [phase,b,a]; omega
  rw [addr,TickMountedPins.memory_at]
  change BitLayout.bitWord (64*w) (input a)=_
  rw [bit]
  cases sel i <;> rfl

/-- The first fixed native instructions prepare every authentic selector bit
in place. The whole low input frame remains available to the other phases. -/
theorem native {pc regs slots : ℕ} (M : Machine (64*w) pc regs slots)
    (input : ℕ→Bool) (room : (head).length≤p)
    (stored : headerReads text textRoom self index params sel input)
    (capacity : (1+6*pc+slots)*(64*w)≤p) (authentic : ∀ i, input i.val=NativeTrace.executable M i)
    (space : 2+p+p<2^(64*w)) :
    (TickHeaderShift.procedure (64*w) p).Spec (fun m=>m=inputMemory M p input)
      (fun _ o=>o=TickMountedPins.memory (w:=64*w) (fun j : Fin p=>input j.val) ∧
        ∀ i : Fin (cap+1),o (phase w n text+i.val)=((sel i).toNat : Word (64*w))) (28+16*p) :=
  Procedure.Spec.mono (A:=TickHeaderShift.procedure (64*w) p)
    (mount_input M input capacity authentic space) (fun _ h=>h)
    (by rintro _ _ rfl; exact ⟨rfl,word_at text textRoom self index params sel input room stored⟩) le_rfl

end Hierarchy.TraceFactorReceiver.Selector
end

end OAI
