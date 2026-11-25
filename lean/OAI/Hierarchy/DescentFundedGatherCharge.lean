import OAI.Hierarchy.DescentOrdinaryGatherWordTariff
import OAI.Hierarchy.DescentFundedArgumentTables
import OAI.Hierarchy.DescentOrdinaryRoleControlPrice

namespace OAI
/-! # The public operand gather at the true settled date and its selected pitch -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOperandVectorArena DescentGatheredVectorReshape DescentPackedActorMask DescentHaloWalkRAM
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)

/-- These three registers compute the issued population request, the old venue address,
and the count of live donors. Their syntax is independent of the local path multiplicity. -/
theorem dictionary_probe_work (A : ArgumentEntry v) (floor : ℕ) («matching» : A.Match v floor)
    (p : Fin v.vector.pageCount) (j : Fin v.vector.lows) :
    let t:=(A.directory v floor «matching»).refs p j
    t.want.work+t.addr.work+t.counts.work=26:=rfl

def gatherCharge (h u₀ u₁ ratio : ℕ) :=
  let L:=v.vector
  let n:=nodes (breadth v.reference.degree*2^v.reference.k) v.reference.oldNodes v.reference.capacity
  let f:=rowFactor L.pageCount L.lows L.radix n 26
  f*ratio*(h+2*L.hosts*h+L.hosts*(L.groups*L.radix)*u₀+L.hosts*L.groups*u₁)+
    f*ratio*2^(h/2)*h

theorem funded_gather_charge (A : ArgumentEntry v) (other floor w ratio : ℕ)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤ v.area.unit)
    (purchase : 4*v.fundedMaxUnit (max (v.fullArgumentUnit A) other)*2^v.area.k≤ v.payload)
    (bus : w≤ ratio*v.payload) :
    let extra:=max (v.fullArgumentUnit A) other
    let W:=v.withFundedArguments extra A
    let E:=v.fundedEntry extra A
    ∀«matching» : E.Match W floor,
    ((E.directory W floor «matching»).refs.phase w (W.vectorStart floor)).wordInvoice≤
      W.gatherCharge v.payload (v.fundedWorkingUnit extra) (2^v.area.k*v.fundedWorkingUnit extra) ratio :=by
  intro extra W E «matching»
  let C:=(E.directory W floor «matching»).refs
  let l:=W.vector
  let at₀:=W.vectorStart floor
  have caps:=v.funded_argument_bounds extra A paid input purchase
  have old : v.payload≤(l.lanes*l.radix)*v.fundedWorkingUnit extra:=by
    change v.payload≤(W.vector.lanes*W.vector.radix)*_
    rw [«matching».post,«matching».radix]
    exact caps.fill₁
  have fresh : v.payload≤ l.lanes*(2^v.area.k*v.fundedWorkingUnit extra):=by
    change v.payload≤ W.vector.lanes*_
    rw [«matching».post]
    exact caps.fill₂
  have fit : (l.bookBits*l.radix)*l.lanes≤ v.payload/2:=by
    change (W.vector.bookBits*W.vector.radix)*W.vector.lanes≤ v.payload/2
    rw [«matching».radix,«matching».post]
    exact (v.funded_argument_widths A other 7).2.1.trans (by omega)
  exact word_bill C l.hosts (l.groups*l.radix) l.groups l.radix l.lanes l.bookBits w
    (l.tables at₀) (l.out at₀) 26 v.payload ratio (v.fundedWorkingUnit extra)
    (2^v.area.k*v.fundedWorkingUnit extra) (l.scratch at₀)
    (fun p i=>(W.dictionary_probe_work E floor «matching» p i).le) old fresh fit bus

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
