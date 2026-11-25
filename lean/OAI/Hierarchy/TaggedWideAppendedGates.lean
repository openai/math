import OAI.Hierarchy.TaggedWideInstalledGates

namespace OAI
/-! # Dense native observation after a second physically installed reporting phase -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProbeStage Tagged WideControlJoin
open ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Diagonal
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ) {m : ℕ} (l : WideCPU.Layout m)
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "old" => v.widePrograms h width bits l
local notation "times" => v.wideProgramTicks h width bits l
local notation "keep" => l.pruneScratch+l.pruneRows
local notation "U" => keep+1
variable (suffix : Procedure (Native.wordBits h (2^v.W) Native.copies)) (bill stop size : ℕ)

def appendedPrograms : Procedure W × Procedure W := ((old).1,(old).2.seq suffix)
def appendedTimes := ((times).1,(times).2+bill)
def appendedEnd := max U stop

structure AppendedRoom : Prop where
  original : v.GateRoom h width bits l size
  upper : max U stop≤2^W
  labels : ((old).2.seq suffix).labels+3≤2^(W+1)
  clock : ((times).2+bill+3)+max U stop≤2^(W+1)

variable (lim : v.AppendedRoom h width bits l suffix bill stop size)
local notation "U'" => max U stop
local notation "spent" => (times).2+bill

def appendedGates : Gate × Gate :=
  ((v.wideGates h width bits l size lim.original).1,
   Gate.denseProcedure (S:=size) (f:=spent+3) ((old).2.seq suffix) (keep:Word W) 0 lim.upper
     (Tagged.controlHeight h (size+(spent+3+U'))) lim.original.word lim.labels lim.original.initial lim.clock)

local notation "newGate" => v.appendedGates h width bits l suffix bill stop size lim

theorem appended_first :
    (newGate).1=(v.wideGates h width bits l size lim.original).1 := rfl
theorem appended_end : (newGate).2.u=U' := rfl
theorem appended_address (i : Fin U') : ((newGate).2.addr i).val=i.val := rfl

/-- The original paid gate's deterministic execution followed by the physical after-pass.
The enlarged dense list uses the original prune flag as its return cell. -/
theorem appended_paid_run (header : ℕ→Word W) (mid out : Memory W)
    (started : (old).2.Exec (initialMemory size header) mid (times).2) (finished : suffix.Exec mid out bill) :
    (newGate).2.Ran header out :=
  Gate.ofProcedure_run (S:=size) (f:=spent+3) ((old).2.seq suffix)
    (keep:Word W) 0 (Gate.denseAddr lim.upper) (Tagged.controlHeight h (size+(spent+3+U')))
    lim.original.word lim.labels lim.original.initial lim.clock header out spent
    (Nat.lt_succ_self (spent+2)) (Procedure.Exec.then (A:=(old).2) (B:=suffix) started finished)

theorem appended_prior_word (mid out : Memory W) (frame : ∀a,a<U→ out a=mid a)
    (a : ℕ) (inside : a<U) (j : Fin W) :
    (newGate).2.terminal out (Gate.denseSeen a (inside.trans_le (le_max_left U stop)) j.castSucc)=
      TraceWords.bits (mid a) j := by
  change TraceWords.bits (out a) j=_
  rw [frame a inside]

theorem appended_prior_high (out : Memory W) (a : ℕ) (inside : a<U) :
    (newGate).2.terminal out (Gate.denseSeen a (inside.trans_le (le_max_left U stop)) (Fin.last W))=false :=
  by
    exact Nat.testBit_eq_false_of_lt (out a).isLt

theorem appended_prior_flag (mid out : Memory W) (frame : ∀a,a<U→ out a=mid a)
    (a : ℕ) (inside : a<U) (b : Bool) (flagged : (mid a).val=b.toNat) :
    (newGate).2.terminal out (Gate.denseSeen a (inside.trans_le (le_max_left U stop)) 0)=b := by
  change (out a).val.testBit 0=b
  rw [frame a inside, flagged]
  cases b <;> decide

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
