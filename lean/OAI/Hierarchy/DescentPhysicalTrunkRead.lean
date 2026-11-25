import OAI.Hierarchy.DescentPhysicalResetTrunkScene
import OAI.Hierarchy.DescentResetTrunkOperand
import OAI.Hierarchy.DescentResetTrunkCompactSuffix

namespace OAI
/-! # Reading the signed trunk field on the original dated reset procedure -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup
open DescentResetTrunkCompactPointer DescentResetFieldAssembler DescentCommonHost DescentResetTrunkIssue DescentActorRaster
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
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
local notation "oldRank" => vertex.trans (Fin.castLEEmb previous)
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
local notation "deck" m => (v.received floor s safe).image m

/-- The compiled single dated operand reads the original signed trunk candidate
for every group and low block. The three inputs describe the earlier physical
census, scalar row and signed-stem output on that very execution. -/
theorem trunk_operand (initial : Memory bw)
    (hosts : v.peer.hosts=rawSize) (groups₁ : v.peer.groups=grp)
    (blocks : v.blocks=2^k) (queries : v.signedQueries=Q)
    (denseFit : used≤v.newHosts) (inverse : used≤ s.inverse.size)
    (room : v.trunkEnd floor<2^bw)
    (degree : B.next.placement.degree+1<2^v.metaBits) (cap : B.next.placement.cap<2^v.metaBits)
    (stamp : v.metaBits*7*v.peer.lanes≤bw)
    (census : Measured dateBanks (compactActorName B previous) (compactTrunkPeer B previous) (deck initial))
    (price : ∀r : Fin v.newHosts,v.preParent floor s safe initial (counted+r.val)=
      ((DescentResetFieldAssembler.raw v.metaBits ((originalTrunkRack B r).elim .blank (hostShape B))).val:Word bw))
    (previousRows : ∀(x : Fin (2^k)) (p : slot) (u : Row v.newHosts grp v.peer.lanes),
      (deck initial) (atStem+(finProdFinEquiv (x,ord₀ (true,p))).val*(v.newHosts*chunks grp v.peer.lanes)+
        (row v.newHosts grp v.peer.lanes u).val)=
      ((data (incomingWord B (originalTrunkRack B) v.metaBits x p) u).val:Word bw)) :
    (v.trunkScene floor s safe).Runs initial ∧
      ∀x : Fin (2^k),(v.trunkOperand floor x.val).Fits bw (v.trunkEnd floor) ∧
        Source (v.trunkOperand floor x.val)
          (fun (h₁ : Fin v.newHosts) g₁=>DescentResetFieldAssembler.raw v.metaBits (actualMeta B (originalTrunkRack B) x (trunkCandidate B) h₁ g₁))
          v.peer.lanes ((v.trunkScene floor s safe).image initial):=by
  have borders:=v.trunk_regions floor s
  have limit:=room
  change DescentResetTrunkCompactProgram.endAddress midAddr v.newHosts v.peer.groups v.peer.lanes v.metaBits<2^bw at limit
  rw [groups₁] at limit
  have order:=v.trunk_room floor s safe inverse
  rw [hosts] at order
  have earlier:=borders.2.2.le
  rw [blocks,queries,groups₁] at earlier
  have middle:=borders.2.1
  rw [groups₁] at middle
  have headOK:=v.received_trunk_header floor s safe initial
  rw [groups₁] at headOK
  have stored (r : Fin v.newHosts):= (v.received_trunk_scalar floor s safe initial r).trans (price r)
  have physical:=compact_trunk_suffix B previous denseFit dateBanks midAddr atStem counted (v.trunkHeader floor)
    (deck initial) order census earlier limit degree cap stamp borders.1 middle headOK stored previousRows
  refine ⟨(v.trunkScene_any floor s safe initial room).1,?_⟩
  intro x
  have first:=physical.2.1 x
  have second:=physical.2.2.1 x
  rw [trunk_operand_eq] at first second
  have arity : v.signedQueries/2=half:=by rw [queries];exact Nat.mul_div_cancel_left _ (by decide : 0<2)
  simp only [DescentDatedAddressBook.CandidateFront.trunkOperand,DescentDatedAddressBook.CandidateFront.trunkEnd,
    DescentDatedAddressBook.CandidateFront.gathered,arity,groups₁]
  constructor
  · exact first
  · change Source _ _ v.peer.lanes
      ((DescentResetTrunkCompactProgram.phase bw midAddr v.newHosts v.peer.hosts v.peer.groups v.peer.lanes v.metaBits dateBanks).image (deck initial))
    rw [hosts,groups₁]
    exact second

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
