import OAI.Hierarchy.DescentCompactRankPeers
import OAI.Hierarchy.DescentPhysicalRankPortPhase
import OAI.Hierarchy.DescentResetPeerJointRead

namespace OAI
/-! # The physical compact port image names the same sorted neighbors as the sparse source -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentPackedColony DescentSIMDLookup DescentSortedRoster DescentSortedRoster.Compact
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable (v : ResetOutput) (base : ℕ) {N O D w : ℕ}
local notation "h₀" => v.sheets.hosts
local notation "g₀" => v.sheets.groups
local notation "m₀" => v.sheets.lanes
local notation "p₀" => v.front.peer.hosts
local notation "B" => v.rankPortRegs base
variable (name : Fin N↪Fin p₀) (size : N≤h₀) (raw : Fin p₀→Fin 4→Option (Fin p₀))
  (inc : StrictMono name) (closed : ∀u y,y∈present raw (name u)→∃z,name z=y)
  (m : Memory w) (room : v.RankPortRoom base w)

include room in
private theorem raw_limit : p₀<2^w:=room.roster.forwardSize.trans_lt room.roster.forward.2.1

include room in
private theorem compact_limit : h₀<2^w:=by
  have a:=DescentRankPortRoster.bank_size (v.candidateEnd base) h₀
  have b:=(DescentRankPortRoster.bank_fits room.roster).2.1
  omega

include room inc closed in
/-- All three source registers refer to actual stored directory or sparse
roster words. Only the forward lookup is needed in addition to the earlier
joint roster's count, inverse and current four entries. -/
theorem rankPort_compact
    (count : m (B).count.base=(N:Word w)) (inverseSize : N≤(B).inverse.size)
    (inverse : ∀z:Fin N,m ((B).inverse.base+z.val)=((name z).val:Word w))
    (ranks : ∀z:Fin N,m ((B).forward.base+(name z).val)=(z.val:Word w))
    (slots : ∀a j,m ((B).current.base+(a.val*4+j.val))=
      (((indexed raw a j).elim p₀ Fin.val : ℕ):Word w)) :
    Mounted (v.rankPorts base) (indexed (pull name size raw))
      ((v.rankPortPhase base w).image m) g₀ m₀:=by
  classical
  obtain ⟨static,rows⟩:=v.rankPort_mounted base m room
  refine ⟨fun p j=>static.ids j p,?_,static.offsets,static.chunks⟩
  intro x j
  have hp:=raw_limit v base room
  have hh:=compact_limit v base room
  have hc : (m (B).count.base).val=N:=by rw [count,Fin.val_cast_of_lt (size.trans_lt hh)]
  have valid (hx : x.val<N) : (m ((B).inverse.base+x.val)).val=(name ⟨x.val,hx⟩).val:=by
    rw [inverse ⟨x.val,hx⟩,Fin.val_cast_of_lt ((name _).isLt.trans hp)]
  have read:=rows x j (fun hx=>(hc ▸ hx).trans_le inverseSize) (fun hx=>by
    rw [hc] at hx
    rw [valid hx]
    exact (name _).isLt)
  rw [Nat.mul_comm x.val 4,read]
  unfold DescentRankPortRoster.reported
  rw [hc]
  by_cases live:x.val<N
  · let u : Fin N:=⟨x.val,live⟩
    have same : x=u.castLE size:=Fin.ext rfl
    simp only [live, ↓reduceIte]
    rw [valid live,Nat.mul_comm 4 (name u).val,slots (name u) j,same,
      indexed_live name size raw u j inc (closed u)]
    cases entry:indexed raw (name u) j with
    | none=>
      simp [Option.elim,DescentPackedColony.target,Fin.val_cast_of_lt hp]
    | some y=>
      obtain ⟨z,rfl⟩:=closed u y ((indexed_iff ..).mp entry).1
      simp [Option.elim,DescentPackedColony.target,Fin.val_cast_of_lt ((name z).isLt.trans hp),
        (name z).isLt,ranks z,restore_name]
  · simp only [live, ↓reduceIte]
    rw [indexed_missing name size raw (Nat.le_of_not_gt live)]
    rfl

include room inc closed in
/-- Earlier joint roster coordinates can be passed directly from the reached
period. The four registers below the protected prefix retain their values. -/
theorem rankPort_compact_of_reads (earlier : Memory w) (A : DescentResetPeerJointRAM.Sources)
    (old : Fin O→Fin D→Option (Fin O))
    (issued : DescentResetPeerJointRAM.Reads A N name (indexed raw) old earlier)
    (count : A.count=(B).count) (inverse : A.inverse=(B).inverse) (current : A.current=(B).current)
    (roof : ℕ) (frame : ∀a,a<roof→m a=earlier a)
    (countFit : (B).count.Fits w roof) (inverseFit : (B).inverse.Fits w roof)
    (currentFit : (B).current.Fits w roof) (ranks : ∀z:Fin N,m ((B).forward.base+(name z).val)=(z.val:Word w)) :
    Mounted (v.rankPorts base) (indexed (pull name size raw)) ((v.rankPortPhase base w).image m) g₀ m₀:=by
  have countRoom : (B).count.base<roof:=by have s:=countFit.1;have addr:=countFit.2.2;omega
  have invSize : N≤(B).inverse.size:=inverse ▸ issued.inverseSize
  refine v.rankPort_compact base name size raw inc closed m room ?_ invSize ?_ ranks ?_
  · rw [frame _ countRoom,←count];exact issued.count
  · intro z
    rw [frame _ ((Nat.add_lt_add_left (z.isLt.trans_le invSize) _).trans_le inverseFit.2.2),←inverse]
    exact issued.inverse z
  · intro a j
    have ix : a.val*4+j.val<4*p₀:=by have :=j.isLt;have :=a.isLt;omega
    rw [frame _ ((Nat.add_lt_add_left (ix.trans_le room.roster.currentSize) _).trans_le currentFit.2.2),←current]
    exact issued.current a j

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
