import OAI.Hierarchy.TaggedWideProgramSyntax
import OAI.Hierarchy.TaggedWideControlDense
import OAI.Hierarchy.TaggedWideControlHeight

namespace OAI
/-! # The actual first admission and paid trace gates of a fixed installed calendar -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage Tagged Tagged.WideControlJoin
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ) {m : ℕ} (l : WideCPU.Layout m)
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "programs" => v.widePrograms h width bits l
local notation "times" => v.wideProgramTicks h width bits l
local notation "flag" => (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh
local notation "keepCell" => l.pruneScratch+l.pruneRows
local notation "U" => keepCell+1

structure GateRoom (size : ℕ) : Prop where
  word : 3≤W+1
  initial : size≤2^W
  upper : U≤2^W
  smallFirst : (programs).1.labels+3≤2^(W+1)
  smallPaid : (programs).2.labels+3≤2^(W+1)
  firstClock : (times).1+3+1≤2^(W+1)
  paidClock : (times).2+3+U≤2^(W+1)

def wideGates (size : ℕ) (lim : v.GateRoom h width bits l size) : Gate × Gate :=
  (Gate.ofProcedure (S:=size) (f:=(times).1+3) (programs).1 (flag:Word W) 0 (fun _ : Fin 1=>(flag:Word W))
     (Tagged.controlHeight h (size+((times).1+3+1))) lim.word lim.smallFirst lim.initial lim.firstClock,
   Gate.denseProcedure (S:=size) (f:=(times).2+3) (programs).2 (keepCell:Word W) 0 lim.upper
     (Tagged.controlHeight h (size+((times).2+3+U))) lim.word lim.smallPaid lim.initial lim.paidClock)

theorem first_addr (size : ℕ) (lim : v.GateRoom h width bits l size) :
    (v.wideGates h width bits l size lim).1.addr (0 : Fin 1)=(flag:Word W) := rfl

theorem paid_addr (size : ℕ) (lim : v.GateRoom h width bits l size) (i : Fin U) :
    (v.wideGates h width bits l size lim).2.addr i=⟨i.val,i.isLt.trans_le lim.upper⟩ := rfl


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
