import OAI.Hierarchy.GridPinReceiverIntervals
import OAI.Hierarchy.GridPinScheduledOffsets
import OAI.Hierarchy.GridPinStateFrames

namespace OAI
/-! # Receiver-local recovery of genuine in-tick interval starts -/

namespace Hierarchy.GridPinPublisher
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM FactorBucketRAM GridPinNativeLoops
open GridThrough
open scoped Fin.CommRing
namespace Plan

variable {W : ℕ} (P : Plan)

def intervalProgram (W intervalBase : ℕ) : Procedure W :=
  (((procedure seedOps (P.tickSeed W)).seq
    (procedure factorOps (factorWords W P.factors P.factor))).seq
    (procedure bucketOps (bucketWords W P.lanes P.bucket))).seq
    (GridPinReceiverIntervals.program W P.lanes P.source.blocks P.header.pins intervalBase)

def intervalMemory (intervalBase : ℕ) (m : Memory W) : Memory W :=
  iterRows GridPinReceiverIntervals.step
    (GridPinReceiverIntervals.words W P.lanes P.source.blocks P.header.pins intervalBase)
    (P.bucketed m) P.lanes

def intervalCost : ℕ :=
  (3+P.ticks*(1+seedOps.length))+(3+P.factors*(1+factorOps.length))+
    (3+P.lanes*(1+bucketOps.length))+(3+15*P.lanes)

theorem interval_architecture (W base : ℕ) :
    let p:=P.intervalProgram W base
    p.labels=91 ∧ p.registers=56 ∧ p.slots=48 :=
  ⟨rfl,rfl,rfl⟩

theorem interval_cost_eq :
    P.intervalCost=12+10*P.ticks+35*P.factors+38*P.lanes := by
  change (3+P.ticks*10)+(3+P.factors*35)+(3+P.lanes*23)+(3+15*P.lanes)=_
  omega

/-- Four bounded RAM scans. The first three reproduce numeric bucket prefixes using
only the current receiver's count, owner and key arrays. The fourth installs the
local slot into the actual seed writer's interval rows. -/
theorem interval_exec (base : ℕ) (mem : Memory W) (ticks : P.ticks<2^W)
    (factors : P.factors<2^W) (lanes : P.lanes<2^W) :
    (P.intervalProgram W base).Exec mem (P.intervalMemory base mem) P.intervalCost := by
  have S : (procedure seedOps (P.tickSeed W)).Exec (mem) (P.seeded mem) (3+P.ticks*(1+seedOps.length)) := Procedure.Spec.exec (loop_spec seedOps seedStep (fun _ _ _ _ _ _=> seed_trace ..)
    (P.tickSeed W) _ ticks rfl) mem trivial
  have F : (procedure factorOps (factorWords W P.factors P.factor)).Exec (P.seeded mem) (P.factorized mem) (3+P.factors*(1+factorOps.length)) := Procedure.Spec.exec (loop_spec factorOps factorStep (fun _ _ _ _ _ _=>factor_trace ..)
    (factorWords W P.factors P.factor) _ factors rfl) (P.seeded mem) trivial
  have B : (procedure bucketOps (bucketWords W P.lanes P.bucket)).Exec (P.factorized mem) (P.bucketed mem) (3+P.lanes*(1+bucketOps.length)) := Procedure.Spec.exec (loop_spec bucketOps bucketStep (fun _ _ _ _ _ _=>bucket_trace ..)
    (bucketWords W P.lanes P.bucket) _ lanes rfl) (P.factorized mem) trivial
  have last : (GridPinReceiverIntervals.program W P.lanes P.source.blocks P.header.pins base).Exec
      (P.bucketed mem) (P.intervalMemory base mem) (3+15*P.lanes) := GridPinReceiverIntervals.execute P.lanes P.source.blocks P.header.pins base (P.bucketed mem) lanes
  intro p r k mach pc reg pub exit installed data cfg input start same
  exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then S F) B) last mach pc reg pub exit installed data cfg input start same

theorem interval_read {S N k n q d : ℕ}
    (Q : FactorPinIntervals.Layout (Cell k n×Fin q) S N d)
    (base : ℕ) (mem : Memory W) (lanes : P.lanes<2^W)
    (blocks : P.source.blocks+P.lanes≤2^W) (space : base+4*P.lanes≤2^W)
    (pins : P.header.pins=d) (pinsFit : d<2^W) (fit : (n+1)^k*(q*d)≤2^W)
    (apart : ∀ b<P.lanes, ∀ i<P.lanes, P.source.blocks+b≠base+4*i+3)
    (offset : ∀ j : Fin S, P.bucketed mem (P.source.blocks+j.val/P.source.span)+
      ((j.val%P.source.span:ℕ):Word W)=((GridPinAddressImage.code (Q.address j)).val:Word W))
    (b : Fin P.lanes) (j : Fin S) (atLane : j.val/P.source.span=b.val)
    (first : j.val%P.source.span=0) :
    P.intervalMemory base mem (base+4*b.val+3)=((Q.slot j).val:Word W) := by
  have h := GridPinReceiverIntervals.readback P.lanes P.source.blocks P.header.pins base
    lanes blocks space (by simpa only [pins] using pinsFit) apart (P.bucketed mem)
  change GridPinReceiverIntervals.Readback P.lanes P.source.blocks P.header.pins base
    (P.bucketed mem) (P.intervalMemory base mem) at h
  rw [pins] at h
  exact GridPinReceiverIntervals.slot_at_bucket Q _ _ h fit offset b j atLane first

theorem interval_frame {full raw : ℕ} (R : BankRoom W P raw full)
    (G : PrefixGeometry W P full) (mem : Memory W) (owners : PrefixOwners P mem)
    (base : ℕ) (lanes : P.lanes<2^W) (blocks : P.source.blocks+P.lanes≤2^W)
    (space : base+4*P.lanes≤2^W) (pins : P.header.pins<2^W)
    (apart : ∀ b<P.lanes, ∀ i<P.lanes, P.source.blocks+b≠base+4*i+3)
    (a : ℕ) (off : ∀ i<P.lanes,a≠base+4*i+3)
    (ticks : Bank.ticks.Outside P raw full a) (factors : Bank.factors.Outside P raw full a)
    (buckets : Bank.blocks.Outside P raw full a) : P.intervalMemory base mem a=mem a := by
  have h := GridPinReceiverIntervals.readback P.lanes P.source.blocks P.header.pins base
    lanes blocks space pins apart (P.bucketed mem)
  exact (h.1 a off).trans (R.bucketed_outside G mem owners a ticks factors buckets)

end Plan
export Plan (intervalProgram intervalMemory intervalCost interval_architecture interval_cost_eq interval_exec interval_read interval_frame)

end Hierarchy.GridPinPublisher

end OAI
