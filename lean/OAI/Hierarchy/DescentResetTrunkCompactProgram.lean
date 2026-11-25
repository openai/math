import OAI.Hierarchy.DescentResetTrunkCompactGather
import OAI.Hierarchy.DescentResetTrunkPhases

namespace OAI
/-! # The fixed trunk suffix for the actual compact actor numbering -/
namespace Hierarchy.DescentResetTrunkCompactProgram
open DescentSixParty.Chronology DescentDyadicSpan
open DescentSIMDLookup (chunks)
open DescentResetTrunkCompactPointer (Banks Room)
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w N H P G M b : ℕ}

def endAddress (base H G M b : ℕ):=DescentResetTrunkIssue.endAddress
  (DescentResetTrunkCompactGather.endAddress base H G M) b M

def phase (w base H P G M b : ℕ) (banks : Banks) : NativePhase w:=
  (DescentResetTrunkCompactGather.phase w base H P G M banks).seq
    (DescentResetTrunkIssue.phase w (DescentResetTrunkCompactGather.endAddress base H G M) b M)

theorem grow (base H G M : ℕ):base≤DescentResetTrunkCompactGather.endAddress base H G M:=by
  unfold DescentResetTrunkCompactGather.endAddress DescentResetTrunkCompactGather.geometry
    DescentResetTrunkCompactRows.endAddress DescentResetTrunkCompactRows.rowBase
  omega

theorem any (base : ℕ) (banks : Banks) (m : Memory w)
    (inputs : Room banks N H P w base) (room : endAddress base H G M b<2^w) :
    let p:=phase w base H P G M b banks
    p.Runs m ∧ ∀a,a<base ∨ endAddress base H G M b≤a→p.image m a=m a:=by
  intro p
  let limit:=DescentResetTrunkCompactGather.endAddress base H G M
  let first:=DescentResetTrunkCompactGather.phase w base H P G M banks
  have lt : limit≤endAddress base H G M b:=Nat.le_add_right ..
  have get:=DescentResetTrunkCompactGather.any (M:=M) (G:=G) base banks m inputs (lt.trans_lt room)
  have finish:=DescentOrdinaryAtomFieldRAM.ROM.run (DescentResetTrunkIssue.pages b M)
    (DescentResetTrunkIssue.width b M) limit (first.image m) room
  have stay:=DescentOrdinaryAtomFieldRAM.ROM.frame (DescentResetTrunkIssue.pages b M)
    (DescentResetTrunkIssue.width b M) limit (first.image m)
  refine ⟨NativePhase.seq_runs first (DescentResetTrunkIssue.phase w limit b M) m get.1 finish.1, ?_⟩
  intro a h
  rcases h with low|high
  · exact (stay a (.inl (low.trans_le (grow ..)))).trans (get.2 a (.inl low))
  · exact (stay a (.inr high)).trans (get.2 a (.inr (lt.trans high)))

theorem price (w base H P G M b : ℕ) (banks : Banks) :
    let n:=H*chunks G M
    let pages:=3*2^(DescentResetTrunkIssue.width b M)
    let p:=phase w base H P G M b banks
    p.ticks≤46+108*H+124*n+10*pages ∧
      DescentStaticWordColumn.names p.program≤15*(2*H+4*n+4)+350+15*(pages+1) ∧
      endAddress base H G M b≤base+(4*H+6*n+5)+pages:=by
  intro n pages p
  have original:=DescentResetTrunkCompactGather.price w base H P G M banks
  let limit:=DescentResetTrunkCompactGather.endAddress base H G M
  have second : DescentStaticWordColumn.names (DescentResetTrunkIssue.program limit b M w)=15*(pages+1):=
    DescentStaticWordColumn.names_mount ..
  refine ⟨?_,?_,?_⟩
  · have time:=original.1
    change (DescentResetTrunkCompactGather.phase w base H P G M banks).ticks+(4+10*pages)≤_;omega
  · change DescentStaticWordColumn.names ((DescentResetTrunkCompactGather.phase w base H P G M banks).program.seq
      (DescentResetTrunkIssue.program limit b M w))≤_
    rw [DescentStaticWordColumn.names_seq,second]
    exact Nat.add_le_add_right original.2.1 _
  · have fit:=original.2.2
    change DescentResetTrunkCompactGather.endAddress base H G M+pages≤_
    omega

end
end Hierarchy.DescentResetTrunkCompactProgram

end OAI
