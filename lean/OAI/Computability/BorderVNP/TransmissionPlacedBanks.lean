import OAI.Computability.BorderVNP.TransmissionPlacedImage
import OAI.Computability.BorderVNP.TransmissionAcrossHistory

/-! # Reconstructing physical endpoint banks inside returning directory scans -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Packing.Directory

variable {w : ℕ} {h : TeamHistory w} {d : Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → ℕ}
variable {origin stride cutoff : ℕ} {pins : Pins.Layout}

/-- Read the unchanged lower memory at the actual prefix of this native return. -/
theorem PlacedImage.before_low (f : PlacedImage h d pp lp owner origin stride pins cutoff)
    {i : ℕ} (hi : i ≤ h.count) {a : ℕ} (ha : a < cutoff) :
    h.before i a = h.initial a :=
  tableMemory_protected h.rows h.team h.pub h.initial h.bits i a fun k hk => f.low k (hk.trans_le hi) a ha

/-- Earlier offsets of the selected current range also retain every lower address. -/
theorem PlacedImage.bit_low (f : PlacedImage h d pp lp owner origin stride pins cutoff)
    {i : ℕ} (hi : i < h.count) {mode : Role} (sel : (h.rows i).selected h.team = some (some mode))
    {j : ℕ} (hj : j ≤ (h.rows i).width.val) {a : ℕ} (ha : a < cutoff) :
    bitMemory h.rows h.team h.pub h.initial h.bits i mode j a = h.initial a := by
  unfold bitMemory
  rw [rangeMemory_eq_of_outside]
  · exact f.before_low hi.le ha
  · intro r hr
    have hb := (f.low i hi a ha mode sel r hr).1
    omega
  · intro r hr
    have hb := (f.low i hi a ha mode sel r hr).2
    omega

end RoutingISA.Transmission

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission

variable {R r t d link inner n w header : ℕ} {Edge : Type}
variable {G : Wiring R r t d link inner n Edge} {pin : Fin d → Bool}
variable {ext : Exterior R r link → Bool} {width : Fin (R+1) → Fin (R+1) → ℕ}
variable {u : Fin (R+1)}

/-- A real initialized processor tape and scheduled routing table remain valid after
a memory change confined to the banks above their fitted address intervals. -/
def TransferBank.atLowMemory (a : TransferBank G pin ext width w header u) (m : Memory w)
    (origin : ℕ) (low : ∀ i < origin, m i = a.mem i)
    (input : (G.processorFields u pin ext a.ibase a.hbase a.starbase).header.length ≤ origin)
    (table : scheduleCeiling (readings a.pub) (readings a.mem) (R+1) ≤ origin) :
    TransferBank G pin ext width w header u :=
  { a with
    mem := m
    physical := fun i hi => (low i (hi.trans_le input)).trans (a.physical i hi)
    schedule := a.schedule.of_keeps fun i hi => congrArg Fin.val (low i ((scheduleRead_lt_ceiling hi).trans_le table)) }

/-- The public arguments and memory of a physical bank at the start of a returning
history, together with the two scalar address bounds needed to move it to any bit. -/
structure HistoryBank (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool) (width : Fin (R+1) → Fin (R+1) → ℕ)
    (header : ℕ) (u : Fin (R+1)) (h : TeamHistory w) (origin : ℕ) where
  /-- The true input and scheduling snapshot at transmission entry. -/
  initial : TransferBank G pin ext width w header u
  /-- Native public argument values match the recorded return. -/
  args : initial.pub = h.pub
  /-- The bank refers to the actual starting RAM. -/
  memory : initial.mem = h.initial
  /-- The complete processor tape precedes the writable receiver arena. -/
  input : (G.processorFields u pin ext initial.ibase initial.hbase initial.starbase).header.length ≤ origin
  /-- Routing-table and frame cells all precede the receiver arena. -/
  table : scheduleCeiling (readings initial.pub) (readings initial.mem) (R+1) ≤ origin

variable {H : TeamHistory w} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {owner : ℕ → ℕ} {origin stride cutoff : ℕ} {pins : Pins.Layout}

/-- The executing team number agrees with its initialized routing frame. -/
theorem HistoryBank.team (a : HistoryBank G pin ext width header u H origin) : H.team.val = u.val := by
  have frame := a.initial.schedule.frame.1
  rw [a.args,a.memory] at frame
  simpa [TeamHistory.team,directoryFrame,frameField,Wiring.transferFrame,readings] using frame

/-- Reconstruct a valid physical bank at the sending team's actual prefix memory. -/
def HistoryBank.before (a : HistoryBank G pin ext width header u H cutoff)
    (f : PlacedImage H D pp lp owner origin stride pins cutoff) {i : ℕ} (hi : i ≤ H.count) :
    TransferBank G pin ext width w header u :=
  a.initial.atLowMemory (H.before i) cutoff (fun _ ha => (f.before_low hi ha).trans (congrFun a.memory.symm _))
    a.input a.table

/-- Reconstruct the receiving team's actual bank after the first offsets of its row.
The physical processor input and scheduled peer offsets survive at this instant. -/
def HistoryBank.bit (a : HistoryBank G pin ext width header u H cutoff)
    (f : PlacedImage H D pp lp owner origin stride pins cutoff) {i : ℕ} (hi : i < H.count)
    {mode : Role} (sel : (H.rows i).selected H.team = some (some mode)) {j : ℕ} (hj : j ≤ (H.rows i).width.val) :
    TransferBank G pin ext width w header u :=
  a.initial.atLowMemory (bitMemory H.rows H.team H.pub H.initial H.bits i mode j) cutoff
    (fun _ ha => (f.bit_low hi sel hj ha).trans (congrFun a.memory.symm _)) a.input a.table

end TeamContraction

end BorderVNP
end Computability
end OAI
