import OAI.Hierarchy.DescentDatedRetainedTicket
import OAI.Hierarchy.DescentPhysicalTrunkRead

namespace OAI
/-! # Retained node hub status on the measured compact reset actor -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetTrunkCompactPointer DescentResetFieldAssembler DescentCommonHost DescentResetTrunkIssue DescentActorRaster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "radius₁" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph radius₁ Ht
local notation "used" => Fintype.card B.next.V
local notation "grp" => S.groupCount (i+1)
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*input.placement.cap)
variable {H0 H bw b : ℕ} (previous : Fintype.card input.V≤H0)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "real" => (Z).rawHostRank T oldRank
local notation "dense" => (Z).denseHostRank T oldRank
local notation "rawSize" => H0*(pal).card


open DescentPackedZip DescentSixParty.Chronology DescentDyadicSpan
variable {M : ℕ}
local notation "L₀" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "cap₀" => input.placement.cap
local notation "slot" => Fin L₀×Fin (2*cap₀)
local notation "Q" => DescentResetStemPackedIssue.count L₀ cap₀
local notation "ord₀" => DescentResetStemPackedIssue.ordinal L₀ cap₀

open ThreeFlat.RAM PhysicalProcedure

variable (v : DescentDatedAddressBook.CandidateFront) (floor : ℕ) (s : v.Scene)
  (safe : v.SceneRoom floor s bw)
local notation "dateBanks" => v.trunkBanks floor s
local notation "midAddr" => v.mixed floor
local notation "counted" => v.peer.endAddress (v.peers floor)
local notation "atStem" => v.stemOutput floor
local notation:max "deck" m:arg => (v.received floor s safe).image m

/-- The later retained-node reader uses the original compact actor's
complemented core bit. Empty hosts have the original blank scalar header. -/
theorem dated_hub_source (initial now : Memory bw) (bits : ℕ)
    (positive : 0<v.peer.lanes) (field : 0<v.metaBits) (stamp : v.metaBits*7*v.peer.lanes≤bw)
    (packing : bits*v.peer.lanes≤bw) (endRoom : v.mixed floor<2^bw)
    (price : ∀r : Fin v.newHosts,v.preParent floor s safe initial (counted+r.val)=
      ((DescentResetFieldAssembler.raw v.metaBits ((originalTrunkRack B r).elim .blank (hostShape B))).val:Word bw))
    (kept : ∀addr,addr<v.mixed floor→now addr=(deck initial) addr) :
    let expr:=DescentRetainedHubFlag.hub v.newHosts v.peer.groups v.peer.lanes v.metaBits bits counted (v.trunkHeader floor)
    expr.Fits bw (v.mixed floor) ∧ Source expr
      (fun (r : Fin v.newHosts) (_ : Fin v.peer.groups)=>if ((originalTrunkRack B r).elim .blank (hostShape B)).core then (0:Cell bits) else 1)
      v.peer.lanes now:=by
  have spans:=v.trunk_regions floor s
  have scalarSafe : counted+1*v.newHosts+span v.newHosts≤v.trunkHeader floor:=by simpa only [one_mul] using spans.1
  have headerRoom : DescentResetStemHeaders.outputBase v.newHosts v.peer.groups v.peer.lanes
      (v.metaBits*7) (v.trunkHeader floor)+1*(v.newHosts*chunks v.peer.groups v.peer.lanes)<2^bw:=by
    simpa only [one_mul] using spans.2.1.trans_lt endRoom
  have safeBody:=DescentResetStemHeaders.body_fits scalarSafe headerRoom (0:Fin 1)
  have bodyEnd:= (Nat.le_add_right ..).trans spans.2.1
  have at_:=DescentRetainedHubFlag.ready (b:=bits) safeBody
  have below:=ProtocolRAMGeneratedWrite.fits_mono _ bodyEnd at_
  let vals (h : Fin v.newHosts):Meta:=(originalTrunkRack B h).elim .blank (hostShape B)
  have unit (h : Fin v.newHosts):(vals h).units=0:=by
    cases at_:originalTrunkRack B h with
    | none=>simp [vals,at_,Meta.blank]
    | some u=>unfold vals;simp only [at_,Option.elim_some];unfold hostShape;split <;> rfl
  have cell (h : Fin v.newHosts) : deck initial (counted+h.val)=((DescentResetFieldAssembler.raw v.metaBits (vals h)).val:Word bw):=
    (v.received_trunk_scalar floor s safe initial h).trans (price h)
  have read:=DescentRetainedHubFlag.source positive field stamp packing vals unit (deck initial)
    (v.received_trunk_header floor s safe initial) cell safeBody
  exact ⟨below,fun p=>(eval_below _ _ (deck initial) now below kept).trans (read p)⟩

theorem primary_hub_digit (t : (Z).Fallback) :
    (hostShape B ((blocks B).src (trunkParent B t)).1.2).core=((T).code t).2.2.isSome:=by
  let u:=(blocks B).src (trunkParent B t)
  obtain ⟨a,here,_,_,mark⟩:=trunk_labels_at B u t false (trunk_side B t false).1 (trunk_side B t false).2
  change (hostShape B u.1.2).core=_
  simpa [hostShape,here] using mark

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
