import OAI.Hierarchy.DescentDatedRegisteredHeaders
import OAI.Hierarchy.DescentOrdinaryMouthStamp

namespace OAI
/-! # The three measured header digits at a genuine newborn receiver -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryOriginMask DescentOrdinaryAtomFieldRAM DescentOrdinaryMouthReturn DescentOrdinaryBorn
open DescentSIMDLookup DescentOperandVectorArena DescentHaloWalkRAM DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
variable (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "B₀" => v.bornBook
local notation "L₀" => v.mouthChart mat.newBlocks
local notation "V₀" => v.vector
local notation "R₀" => v.resolver
local notation "N₀" => DescentPackedActorMask.nodes (breadth (L₀).degree*2^(L₀).depth) (L₀).oldNodes (B₀).cap

theorem booked_mouth_at_birth {nb mb b : ℕ}
    (V : Fin (B₀).args→Fin (V₀).lows→(L₀).Val nb mb)
    (chip : Fin (B₀).hosts→Fin (B₀).groups→Cell (B₀).chipBits)
    (home : (B₀).hosts=(V₀).hosts) (same : (B₀).groups=(V₀).groups*(V₀).radix)
    (j : Fin (R₀).jobs) (h : Fin (R₀).hosts) (g : Fin (R₀).groups)
    (donor : Fin (B₀).hosts) (walk : Fin (breadth (L₀).degree)) (x : Fin (2^(L₀).depth))
    (seat : Fin (B₀).cap) (party : Fin 6) (f : Fin 3) :
    let job:=(R₀).index.symm j
    let arg:=job.2.2.cast (shape.operands.trans mat.newArgs.symm)
    let block:=job.1.cast shape.blocks
    let host:=h.cast (shape.hosts.trans (congrArg (·*(V₀).lows) home.symm))
    let old:=finProdFinEquiv.symm host
    let group:=(finProdFinEquiv (g.cast shape.groups,block)).cast same.symm
    let mask:=marked (V arg old.2) old.1 group
    let i : Fin N₀:=finProdFinEquiv (finProdFinEquiv (walk,x),finSumFinEquiv (.inr (finProdFinEquiv (seat,party))))
    N₀<2^b → DescentSortedRoster.indexed (V arg old.2).walks old.1 walk=some donor →
    ((encode b (R₀).nodes).symm (selection N₀ (R₀).nodes b mask) job.2.1).val=i.val+1 →
    ScalarOperand.take job.2.1 (v.mouthHeaderValue floor A mat shape V chip home same j f h g)=
      RolePorts.value (B₀).bits (pointerAt (B₀).demand (B₀).grain (B₀).scale
        (chipDonor (B₀).format (chip donor group) (finProdFinEquiv (x.cast mat.newBlocks.symm,seat))) party arg.val) f :=by
  intro job arg block host old group mask i room find_ stamped
  exact (L₀).received_born V chip same arg f block host (g.cast shape.groups) donor walk x seat party job.2.1 room find_ stamped

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
