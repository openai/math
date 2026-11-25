import OAI.Hierarchy.DescentResetPublishedTariff
import OAI.Hierarchy.DescentResetCanvasIngressBill
import OAI.Hierarchy.DescentContactOutputWork
import OAI.Hierarchy.DescentPhysicalResetDateTariff
import OAI.Hierarchy.DescentResetReceivedTariff

namespace OAI
/-! Word costs on the original date before and after the actor directory. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentStaticWordColumn ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
variable (a : PhysicalReset) (base : ℕ) (io : Dated.Operands) (sh : a.StencilShape) (count hub : Bank)
  (g Y : ℕ) (inputs : a.RootInputs)
local notation "floor₀" => a.stageStart base
local notation "Q" w => a.rootPhase sh floor₀ count hub g Y inputs w
local notation "front" w => a.ingress.phase base w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)
variable (book : Projected.RootBook a.successor.middle.rotorBits a.successor.middle.rootDepth
  a.ports (2^a.successor.middle.rootDepth) (a.c/2) inputs.field)

private theorem addWordPrices (firstTicks firstNames laterTicks laterNames wordSize firstBill laterBill : ℕ)
    (first : (firstTicks+7*firstNames)*wordSize ≤ firstBill)
    (later : (laterTicks+7*laterNames)*wordSize ≤ laterBill) :
    (firstTicks+laterTicks+7*(firstNames+laterNames))*wordSize ≤ firstBill+laterBill := by
  calc
    _ = (firstTicks+7*firstNames)*wordSize + (laterTicks+7*laterNames)*wordSize := by ring
    _ ≤ _ := Nat.add_le_add first later

theorem ingress_published_price (R D w : ℕ) (safe : (Q w).PreparedFits book)
    (cost : ∀j : Fin (2^a.ingress.k),(io.atoms j.val).work≤7)
    (old : 0 < a.ingress.sourceLanes) (newPitch : 0 < a.ingress.targetLanes) :
    let source:=a.ingress.source base
    let prior:=a.throughPublishedRoots sh floor₀ count hub g Y inputs book source R D w safe
    let ticks:=a.throughPublishedTicks sh floor₀ count hub g Y inputs book R D w safe
    ((front w).ticks+ticks+7*names ((front w).program.seq prior))*w≤
      a.ingress.bill 7*w+a.publishedBill sh floor₀ count hub g Y inputs book source R D w := by
  intro source prior ticks
  have enter:=Nat.mul_le_mul_right w (a.ingress.price base w 7 io.hubs
    (fun x => io.atoms x.val) (fun t => io.wire t.1.val t.2.val) cost old newPitch)
  have rest:=a.through_published_price sh floor₀ count hub g Y inputs book source R D w safe
  rw [names_seq]
  exact addWordPrices _ _ _ _ _ _ _ enter rest

section
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "origin" => a.rebased floor
local notation "A" => (v).front
local notation "begin₀" => (v).actorEnd origin
local notation "scene" => (v).issuedScene origin u.earlier

theorem issued_measured_price (limit : ℕ)
    (operand : (A).OperandPrice (scene) limit)
    (old : 0<(v).contactShape.donor.batch) (blocks : 0<(v).contactShape.blocks) (next : 0<(v).contactShape.batch)
    (past : 0<(A).oldLanes) :
    let n:=(A).newHosts*DescentSIMDLookup.chunks (A).peer.groups (A).peer.lanes
    let views:=3*2^(DescentResetTrunkIssue.width (A).metaBits (A).peer.lanes)
    let loaded:=(A).trunkScene begin₀ (scene) u.sceneFits
    let P:=(v).contactShape.issuedProgram ((A).donorStart begin₀) ((v).trunkEnd origin) (scene).donor w
    let t:=(v).contactShape.issuedTicks ((A).donorStart begin₀) ((v).trunkEnd origin) (scene).donor
    instructionWords loaded.program loaded.ticks+instructionWords P t≤
      (A).receivedBill begin₀ limit+
      ((46+108*(A).newHosts+124*n+10*views)+7*(15*(2*(A).newHosts+4*n+4)+350+15*(views+1)))+
      (v).contactShape.cost ((A).donorStart begin₀) ((v).trunkEnd origin) (v).contactShape.operandWork := by
  intro n views loaded P t
  have bill:=(A).received_price begin₀ (scene) u.sceneFits limit operand past
  have combined:=measured_words u (v).contactShape.operandWork ((v).contactShape.work_bound _ _ _) old blocks next
  exact combined.trans (Nat.add_le_add_right (Nat.add_le_add_right bill _) _)
end

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
