import OAI.Hierarchy.GridRegisteredOrder
import OAI.Hierarchy.GridSimulationPublish

namespace OAI
/-! # Publishing the scheduled wiring from a registered physical trace
The instruction stream and its clock use the public terminal row count.
The selected history determines the contents loaded by those instructions.
-/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.GridRegisteredPublication
open ThreeFlat RAM PhysicalProcedure Diagonal
open GridRegisteredSetting GridThrough FactorPinIntervals TraceAdmission TraceDistribution
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical

def procedure (w m n B q d np ell text S roots stages full span logRadix pc : ℕ) : Procedure (64*w) :=
  let rails := GridControllerSimGeometry.railCount m n B
  let P := GridPinPublisher.canonical w (m+1) n q d np ell text B rails S roots stages full (2*span)
  let A := GridCompilerAdmission.arena w
  let b := GridControllerIdle.shape m n B logRadix q d pc
  (GridSimulation.publication P w (GridSimulation.thresholdSource w rails B np) roots (m+1)
    ((n+1)^(m+1)*q) rails).seq ((GridControllerSimGeometry.program (64*w) A b).seq
      (GridOrderedDataRAM.prepare (64*w) (A.data rails n) b.data (b.rails*2)))

def clock (w m n B q d np ell text S roots stages full span logRadix pc : ℕ) : ℕ :=
  let rails := GridControllerSimGeometry.railCount m n B
  let P := GridPinPublisher.canonical w (m+1) n q d np ell text B rails S roots stages full (2*span)
  let A := GridCompilerAdmission.arena w
  let b := GridControllerIdle.shape m n B logRadix q d pc
  (GridSimulation.assignTime w roots ((m+1)+2)+(3+rails*(1+GridPinNativeLoops.seedOps.length)+P.budget (64*w)))+
    (GridControllerSimGeometry.cost (64*w) A b + (9+5*b.data+11*(b.rails*2)))

variable {F : Type} [Field F] [Fintype F] {w pc regs words S base fuel axes low m n B q d np ell text
  tp tr tk stages logRadix : ℕ}
variable (D : RunData F (64*w) pc regs words S base fuel axes low)
variable (template : Resources.Parameters ℕ) (h : D.run.plan.History) (C : D.run.Charges) (unit : ℕ)
variable (X : Catalyst.Approximation F (m+1) (q*d)) (enc : FieldCode F (64*w))
variable (params : Fin np → Word (64*w)) (recv : Machine (64*w) tp tr tk)
local notation "rails" => GridControllerSimGeometry.railCount m n B
local notation "span" => (2^low : ℕ)
local notation "full" => (2^(axes+1) : ℕ)
local notation "J" => GridDescription.sector w
local notation "A" => GridCompilerAdmission.arena w
local notation "shape" => GridControllerIdle.shape m n B logRadix q d tp
variable (x : Fin (GridControllerSimGeometry.railCount m n B*2) → Bool) (sel : Fin ell → Bool) (textFit : text ≤ w^2)

abbrev headers (tt : Cell (m+1) n × Fin q) : List Bool := GridReceiverHeader.header text textFit
  (GridDescription.code (q:=w^2) recv D.machine) ((GridTicks.index tt).val : Word (64*w)) params sel

local notation "hdr" => headers (m:=m) (n:=n) (q:=q) D params recv sel textFit
local notation "adv" => GridPinCapturedSources.advice (S:=S) (e:=rails) (compact:=B) X enc params recv D.machine
local notation "capture" => GridPinPublisher.capture (compact:=B) X enc params recv D.machine x sel
local notation "outer" => GridApproximationAdvice.paddedMemory X enc B (2*J) capture
local notation "P" => D.parameters template h m n B
local notation "actual" => D.costs template h m n B C unit
local notation "baseAnc" => 16*J+GridPinArena.slab w+stages*full

variable (room : D.Room h C unit w m n B q d
  (headers (m:=m) (n:=n) (q:=q) D params recv sel textFit))
variable (reserved : ∀ j, X.width j ≤ B)
local notation "Sched" => (D.scheduled template h C unit hdr adv room X reserved).1

/-- Only the physical registrar's original low-page equation is used. It
covers the input tape, compact approximation and saved selector bits. -/
def Low {W : ℕ} (sector : ℕ) (initial published : Memory W) : Prop :=
  ∀ i, i < 13*sector → published i=initial i

theorem run_at {N : ℕ} (publicRows : N=D.roots h) (pos : 0 < w) (axis : m+1 ≤ w)
    (positive : 0 < q*d) (rawSize : GridSelfHeader.rawSize w rails B np ≤ S)
    (small : GridPinArena.Small w
      (GridPinPublisher.canonical w (m+1) n q d np ell text B rails S N stages full (2*span))
      S full (stages*full) ((20*(w+1)+2)^((m+1)+2)))
    (fit : GridControllerIdle.Fits (64*w) A shape) (geom : GridControllerIdle.Room A shape)
    (space : GridOrderedSources.Fits (r:=rails) (n:=n) (w:=64*w) X A B)
    (mem : Memory (64*w)) (rows : Resources.Registered baseAnc (14*J) P (D.dest h) (D.work h C unit) mem)
    (frame : Low J outer mem) :
    (procedure w m n B q d np ell text S N stages full span logRadix tp).Spec (·=mem)
      (fun _ out => GridOrderedSources.Raw X Sched enc A B x out capture)
      (clock w m n B q d np ell text S N stages full span logRadix tp) := by
  subst N
  let ht := D.tickPos h C unit hdr room
  let Q := scheduledLayout ht w actual (D.origin h) hdr adv (D.pin_room template h C unit hdr room)
  have endRoom : rails*2 ≤ S := by simpa only [Nat.mul_comm 2] using room.external
  let port := pairPorts (GridPinPublisher.exteriorRails endRoom)
  have paired (e : Fin rails) : Q.origin (port (e,true))=Q.origin (port (e,false)) := by
    let t := (GridPinPublisher.exteriorRails endRoom) e
    exact (Physical.origin_pair D.block D.axesFit D.machine D.fit D.field D.state D.passes D.passesFit
      h (D.ordinal h) t.val (by have := t.isLt; omega)).symm
  have sep := (GridPinArena.scales w pos).1
  have bits := small.bits
  have length : ell ≤ GridPinArena.slab w := small.selector
  have Bsmall : B ≤ S := (Nat.le_mul_of_pos_right B (pow_pos pos 2)).trans (by
    dsimp only [GridSelfHeader.rawSize] at rawSize; omega)
  have preserved (a : ℕ) (lo : a < 13*J) (out : a < 2*J ∨ 2*J+12*B ≤ a) :
      mem a=capture a := by
    rw [frame a lo]
    change fillSegment (2*J) (12*B) _ capture a=capture a
    exact ite_eq_right (by omega)
  have addresses (i : Fin S) : (D.bucket i).val=i.val/(2*span) :=
    TraceDistribution.native_interval_index D.machine D.fit D.field D.state i
  have owners (i : Fin S) : D.dest h (D.bucket i)=Q.origin i := D.owns h i
  have charged (f : Fin (D.roots h)) (j : Fin ((m+1)+2)) :
      (mem (14*J+(f.val*((m+1)+2)+j.val))).val=actual f j := by
    rw [← Nat.add_assoc]
    exact Resources.Registered.cost_read P (D.dest h) (D.work h C unit) rows f j
  have inputs (f : Fin (D.roots h)) : mem (14*J+f.val*((m+1)+2)+1)=
      (TraceAdmission.inputCount (D.dest h) f S span : Word (64*w)) := by
    exact (Fin.cast_val_eq_self (mem (14*J+f.val*((m+1)+2)+1))).symm.trans
      (congrArg (fun a : ℕ => (a : Word (64*w))) (rows.inputs f))
  have run1 {targetPC targetRegisters targetSlots : ℕ} (target : Machine (64*w) targetPC targetRegisters targetSlots) := GridSimulation.published X enc params recv D.machine x sel Q ht actual (D.dest h) D.bucket
    addresses owners (fun f => GridTicks.index.apply_symm_apply _) (fun _ => rfl) GridIdleLayout.direction
    endRoom paired textFit (fun _ => rfl) rfl rawSize pos axis (Nat.two_pow_pos _) small mem
    charged inputs rows.owners (fun j hj => preserved j (by omega) (.inl (by omega)))
    (fun i hi => preserved (12*J+i) (by omega) (.inr (by omega))) target
  have compact (i : ℕ) (hi : i < GridApproximationAdvice.wordCount X) : mem (2*J+i)=outer (2*J+i) :=
    frame (2*J+i) (by have cap : GridApproximationAdvice.wordCount X ≤ J := space.words; omega)
  have exterior (i : Fin (rails*2)) : mem i.val=RAM.BitLayout.bitWord (64*w) (x i) := by
    have hi : i.val < rails*2 := i.isLt
    rw [preserved i.val (by omega) (.inl (by omega))]
    exact GridSelfHeader.external_at X enc params recv D.machine x (by omega) sel i
  intro targetPC targetRegisters targetSlots target
  exact GridSimulation.publication_raw X enc Q endRoom paired
    (GridSimulation.thresholdSource w rails B np) positive pos fit geom space
    (D.counts (scale:=w) (q:=q) (m:=m) (n:=n) (B:=B) template h C unit)
    (D.conservation template h C unit hdr adv room) (D.enough template h C unit hdr room X reserved)
    capture mem x _ compact exterior (@run1) target

theorem low_of_register {W sector seed extent : ℕ} {initial published : Memory W}
    (placed : 13*sector ≤ seed)
    (frame : ∀ z, z < seed → (z < 14*sector ∨ 14*sector+extent ≤ z) → published z=initial z) :
    Low sector initial published :=
  fun i hi => frame i (by omega) (.inl (by omega))

/-- The controller continuing after registration reads the cost and ancestry
of the physical run directly. Its public factors parameter is the register's
terminal count for the fixed stage list. -/
theorem run {N : ℕ} (count : D.roots h=N) (pos : 0 < w) (axis : m+1 ≤ w)
    (positive : 0 < q*d) (rawSize : GridSelfHeader.rawSize w rails B np ≤ S)
    (small : GridPinArena.Small w
      (GridPinPublisher.canonical w (m+1) n q d np ell text B rails S N stages full (2*span))
      S full (stages*full) ((20*(w+1)+2)^((m+1)+2)))
    (fit : GridControllerIdle.Fits (64*w) A shape) (geom : GridControllerIdle.Room A shape)
    (space : GridOrderedSources.Fits (r:=rails) (n:=n) (w:=64*w) X A B) :
    let idx := Resources.indexEquiv D.run h count
    let dy := fun j => idx (D.run.plan.destination h (GridPhysicalAdmission.initialLane (Nat.succ_pos axes) j))
    let work := fun v => unit*D.run.chargeAt h C
      (TraceReceiverSeedWords.start D.machine D.fit D.field D.state D.block D.axesFit) (idx.symm v)
    (procedure w m n B q d np ell text S N stages full span logRadix tp).Spec
      (fun mem => Resources.Registered baseAnc (14*J) (GridRegisteredOrder.fixed D template N m n B)
        dy work mem ∧ Low J outer mem)
      (fun _ out => GridOrderedSources.Raw X Sched enc A B x out capture)
      (clock w m n B q d np ell text S N stages full span logRadix tp) := by
  dsimp only
  intro pcs regs' pubs machine pcEntry reg pub exit rom hardware cfg mem start raw
  obtain ⟨registered,framed⟩ := raw
  have rows := GridRegisteredOrder.registered D template h C unit m n B count registered
  exact run_at D template h C unit X enc params recv x sel textFit room reserved
    count.symm pos axis positive rawSize small fit geom space mem rows framed
    machine pcEntry reg pub exit rom hardware cfg mem start rfl

end Hierarchy.GridRegisteredPublication
end

end OAI
