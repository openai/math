import OAI.Hierarchy.DescentPaidSweepHeldRepacked
import OAI.Hierarchy.DescentOrdinaryRasterRun
import OAI.Hierarchy.DescentDatedOrdinaryCountRoof

namespace OAI
/-! # From the retained chooser target raster to normalized live and paid host pages -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPaidResidentCount DescentPackedColony DescentPacking.PackedMatch.Local.Stage
open DescentSharedCableNames DescentOrdinaryRasterReturn DescentVenueQuantityPlanes
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
local notation "a" => v.area
local notation "start" => v.endAddress floor
local notation "H" => (a).H
local notation "G" => (a).G
local notation "old" => (a).lanesAt
local notation "M" => v.rasterLanes
local notation "p" => StageVenueTail.OrdinaryRaster.shapes a
local notation "paths" => StageVenueTail.OrdinaryRaster.paths a
local notation "n" => StageVenueTail.OrdinaryRaster.nameBits a
local notation "b" => v.venue.paidBits
local notation "cap" => (a).cap
local notation "k" => (a).k
local notation "dims" => StageVenueTail.OrdinaryRaster.dims a v.venue M
local notation "labels" => (fun l : Fin p=>Packed.token (some l))
local notation "top" => StageVenueTail.OrdinaryRaster.sweep a v.venue M start
local notation "begin_" => StageVenueTail.OrdinaryRaster.prepared a v.venue M start
structure FundedInputs where
  field : Bank
  ports : Ports paths
variable (B : v.FundedInputs) (i : Dated.Operands)
local notation "newCount" => DescentOrdinaryPeerCount.newCount (v.materialEnd floor) H (a).D v.venue.hosts v.venue.degree
def paidRasterBanks : DescentOrdinaryRasterReturn.Sources :=
  ⟨Sweep.paidBank begin_ p (paths*2^k) cap b n H G M,
    Sweep.aliveBank begin_ p (paths*2^k) cap b n H G M,newCount⟩
local notation "banks" => v.paidRasterBanks floor
local notation "gather_" => Sweep.HeldRepacked.program start H G old M k paths cap b n p B.field B.ports i.atoms labels
local notation "cost_" => Sweep.HeldRepacked.ticks start H G old M k paths cap b n p B.field B.ports i.atoms labels
local notation "pop" => Sweep.HeldRepacked.image start H G old M k paths cap b n p B.field B.ports i.atoms labels
local notation "scatter" => DescentOrdinaryRasterReturn.phase dims banks top

structure FundedRoom (w : ℕ) : Prop where
  witness : ∃W:Bank,Accessible B.ports W H G M w start
  field : B.field.Fits w start
  atoms : ∀x< 2^k,(i.atoms x).Fits w start
  roof : top< 2^w
  compact : ∃used,DescentOrdinaryRasterReturn.Room dims banks top used w

variable (w : ℕ) (safe : v.FundedRoom floor B i w)
def heldPhase : NativePhase w :=
  ⟨gather_ w,cost_ w,pop,
    (Sweep.HeldRepacked.any start H G old M k paths cap b n p B.field B.ports i.atoms labels (fun _=>0 : Memory w)
      safe.witness.choose safe.witness.choose_spec safe.field safe.atoms safe.roof).2.1⟩

def fundedRaster : NativePhase w :=(v.heldPhase floor B i w safe).seq (scatter w)

theorem fundedRaster_run (m : Memory w) :
    (v.fundedRaster floor B i w safe).Runs m ∧
      ∀j,j< start ∨ v.rasterEnd floor≤ j→(v.fundedRaster floor B i w safe).image m j=m j :=by
  have hi : top≤ v.rasterEnd floor:=DescentOrdinaryRasterReturn.after dims top
  have before : start≤ top:=by
    have prep:=DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch.intervals H G old M k paths b start
    have cut:=Sweep.geometry begin_ p (paths*2^k) cap b n H G M
    exact (prep.1.trans prep.2).trans (cut.1.trans (cut.2.1.trans ((Nat.le_add_right ..).trans
      (cut.2.2.1.trans (cut.2.2.2.1.trans (Nat.le_add_right ..))))))
  obtain ⟨hr,_,hf⟩:=Sweep.HeldRepacked.any start H G old M k paths cap b n p B.field B.ports i.atoms labels m
    safe.witness.choose safe.witness.choose_spec safe.field safe.atoms safe.roof
  obtain ⟨sr,sf⟩:=DescentOrdinaryRasterReturn.any dims banks top (pop m) safe.compact.choose_spec
  exact ⟨(v.heldPhase floor B i w safe).seq_runs (scatter w) m hr sr,
    fun j h=>(sf _ (h.imp_left (fun h=>h.trans_le before))).trans (hf j (h.imp_right (fun h=>hi.trans h)))⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
