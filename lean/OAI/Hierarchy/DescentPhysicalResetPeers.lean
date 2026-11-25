import OAI.Hierarchy.DescentDatedPeerAperture

namespace OAI
/-! # Publish the new peer roster, its sorted four sockets, and its trunk endpoints in one RAM -/
namespace Hierarchy.DescentDatedAddressBook.PeerAperture
open DescentResetPeerUnionRAM DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open private cheapProgram from OAI.Hierarchy.DescentResetSelfPortsRAM
noncomputable section
variable (p : PeerAperture)

structure Inputs where
  old : Bank
  test : Fin p.slots→Fin p.evidence→Cell p.bits→Bool
  src : Fin p.evidence→Fin (chunks p.evidenceGroups p.evidenceLanes)→Expr
  n : ℕ
  h : ℕ
  rootBits : ℕ
  depth : ℕ
  board : NonlinearExpanders.Graph n h
  palette : (DescentDenseHostOrder.roster board rootBits depth).card=p.shapes

variable (u : p.Inputs) (base : ℕ)
def rawPeers := DescentResetPeerUnionRAM.outBase (Program.scratchAt base p.oldHosts p.shapes p.oldDegree
  p.evidence p.bits p.evidenceLanes) p.hosts p.slots
def ports := DescentResetSelfPortsRAM.ports (p.three base) p.hosts p.groups p.lanes
def program (w : ℕ) :=
  ((Program.program w base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups u.old u.test u.src).seq
    (DescentResetSelfPortsRAM.program (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes w)).seq
    (DescentResetTrunkPalette.program u.board u.rootBits u.depth w (p.threshold base) p.oldHosts)
private theorem paletteCheap {n h : ℕ} (board : NonlinearExpanders.Graph n h)
    (rootBits depth w base hosts : ℕ) :
    CheapCode (DescentResetTrunkPalette.program board rootBits depth w base hosts) := by
  exact @DescentStaticWordColumn.cheap w base
    (DescentResetTrunkPalette.literals board rootBits depth hosts)
    (3 * (hosts * (DescentDenseHostOrder.roster board rootBits depth).card))

private theorem joinCheap {w : ℕ} (left middle right : Procedure w)
    (first : CheapCode left) (second : CheapCode middle) (last : CheapCode right) :
    CheapCode ((left.seq middle).seq right) :=
  @cheap_seq w (left.seq middle) right (@cheap_seq w left middle first second) last

def ticks :=
  (Program.clock base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups u.old u.src+
    DescentResetSelfPortsRAM.ticks (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes)+
    (4+10*(3*p.hosts))
def memory {w : ℕ} (m : Memory w) :=
  let three:=Program.output base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups u.old u.test u.src m
  let four:=DescentResetSelfPortsRAM.memory (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes three
  DescentResetTrunkPalette.memory u.board u.rootBits u.depth (p.threshold base) p.oldHosts four

structure Room (w : ℕ) : Prop where
  old : Program.Space base p.oldHosts p.shapes p.oldDegree p.evidence p.bits p.evidenceLanes p.evidenceGroups w u.old u.src
  width : 4<2^w
  total : p.endAddress base<2^w

theorem ordered : base≤p.three base ∧ p.three base≤p.self base ∧
    p.self base≤p.threshold base ∧ p.threshold base≤p.endAddress base := by
  refine ⟨?_,?_,?_,(Nat.le_add_right ..).trans (Nat.le_add_right ..)⟩
  · rw [p.three_extent];omega
  · unfold self
    rw [DescentResetSelfPortsRAM.extent];omega
  · exact le_rfl

set_option maxHeartbeats 2500000 in
theorem publish {w : ℕ} (m : Memory w) (safe : p.Room u base w) :
    (p.program u base w).Exec m (p.memory u base m) (p.ticks u base) ∧
    (∀i,i<base ∨ p.endAddress base≤ i → p.memory u base m i=m i) ∧ CheapCode (p.program u base w) ∧
    (∀i<p.three base,p.memory u base m i=
      Program.output base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups u.old u.test u.src m i) ∧
    (∀i<p.self base,p.memory u base m i=
      DescentResetSelfPortsRAM.memory (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes
        (Program.output base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups u.old u.test u.src m) i) := by
  obtain ⟨start,directory,peers,threshold⟩:=p.ordered base
  have selfSpace: p.self base<2^w:=(peers.trans threshold).trans_lt safe.total
  have size:p.hosts<2^w:=by
    have last:=safe.total
    change p.threshold base+2*p.hosts+DescentDyadicSpan.span p.hosts<2^w at last
    omega
  have inputFits:p.rawPeers base+3*p.hosts≤p.three base:=le_rfl
  let m₁:=Program.output base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups u.old u.test u.src m
  let m₂:=DescentResetSelfPortsRAM.memory (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes m₁
  have a:=Program.any u.old u.test u.src safe.old m
  have b:=DescentResetSelfPortsRAM.any (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes m₁ inputFits size safe.width selfSpace
  have rawEnd : p.threshold base+3*p.hosts≤p.endAddress base:=by
    have:=DescentDyadicSpan.span_ge p.hosts
    unfold PeerAperture.endAddress
    omega
  have d:=DescentResetTrunkPalette.run u.board u.rootBits u.depth (p.threshold base) p.oldHosts m₂
    (by simpa only [u.palette,PeerAperture.hosts] using rawEnd.trans_lt safe.total)
  have step : (DescentResetTrunkPalette.program u.board u.rootBits u.depth w (p.threshold base) p.oldHosts).Exec
      m₂ (p.memory u base m) (4+10*(3*p.hosts)) := by
    have countEq : 3 * (p.oldHosts * (DescentDenseHostOrder.roster u.board u.rootBits u.depth).card)
        = 3 * p.hosts := by rw [u.palette]; rfl
    rw [← countEq]
    intro P R K machine
    exact d.1 machine
  have held : ∀i,i<p.threshold base ∨ p.endAddress base≤ i → p.memory u base m i=m₂ i := by
    intro i hi
    apply d.2.2.1
    simpa only [u.palette,PeerAperture.hosts] using hi.imp_right (rawEnd.trans ·)
  have firstWords : ∀i<p.three base,p.memory u base m i=m₁ i := by
    intro i hi
    exact (held i (.inl (hi.trans_le (directory.trans peers)))).trans
      (b.2.1 i (.inl hi))
  have secondWords : ∀i<p.self base,p.memory u base m i=m₂ i := by
    intro i hi
    exact held i (.inl (hi.trans_le peers))
  refine ⟨?_,?_,?_,firstWords,secondWords⟩
  · intro P R K machine
    exact Procedure.Exec.then (Procedure.Exec.then a.1 b.1) step machine
  · intro i away
    rcases away with low|high
    · exact (held i (.inl (low.trans_le ((start.trans directory).trans peers)))).trans
        ((b.2.1 i (.inl (low.trans_le start))).trans (a.2.2 i (.inl low)))
    · exact (held i (.inr high)).trans
        ((b.2.1 i (.inr ((peers.trans threshold).trans high))).trans
          (a.2.2 i (.inr (((directory.trans peers).trans threshold).trans high))))
  · let left : Procedure w := Program.program w base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups u.old u.test u.src
    let middle : Procedure w := DescentResetSelfPortsRAM.program (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes w
    let right : Procedure w := DescentResetTrunkPalette.program u.board u.rootBits u.depth w (p.threshold base) p.oldHosts
    exact @joinCheap w left middle right
      (fun pc reg pub ex i => a.2.1 pc reg pub ex i)
      (@cheapProgram (p.rawPeers base) (p.three base) p.hosts p.groups p.lanes w)
      (@paletteCheap _ _ u.board u.rootBits u.depth w (p.threshold base) p.oldHosts)

private theorem keep_run_frame_cost {run frame cost details : Prop}
    (all : run ∧ frame ∧ cost ∧ details) : run ∧ frame ∧ cost :=
  ⟨all.1, all.2.1, all.2.2.1⟩

theorem any {w : ℕ} (m : Memory w) (safe : p.Room u base w) :
    (p.program u base w).Exec m (p.memory u base m) (p.ticks u base) ∧
    (∀i,i<base ∨ p.endAddress base≤ i → p.memory u base m i=m i) ∧ CheapCode (p.program u base w) := by
  exact keep_run_frame_cost (p.publish u base m safe)

/-- Every authenticated earlier neighbor row survives the later sorted roster and trunks. -/
theorem three_word {w : ℕ} (m : Memory w) (safe : p.Room u base w)
    (side : Fin 3) (i : Fin p.hosts) :
    let addr:=p.rawPeers base+side.val*p.hosts+i.val
    p.memory u base m addr=Program.output base p.oldHosts p.shapes p.oldDegree p.bits p.evidenceLanes p.evidenceGroups
      u.old u.test u.src m addr := by
  let addr := p.rawPeers base + side.val*p.hosts + i.val
  have inside : addr < p.three base := by
    change p.rawPeers base + side.val*p.hosts + i.val < p.rawPeers base + 3*p.hosts
    have step := Nat.mul_le_mul_right p.hosts (Nat.succ_le_of_lt side.isLt)
    rw [Nat.succ_mul] at step
    have row := i.isLt
    omega
  exact (p.publish u base m safe).2.2.2.1 addr inside

open scoped Fin.CommRing in
theorem palette_word {w : ℕ} (m : Memory w) (safe : p.Room u base w) (j : Fin 3)
    (i : Fin (p.oldHosts*(DescentDenseHostOrder.roster u.board u.rootBits u.depth).card)) :
    p.memory u base m (p.threshold base+j.val*p.hosts+i.val)=
      (DescentResetTrunkPalette.value u.board u.rootBits u.depth j i:Word w) := by
  have small : p.threshold base+3*p.hosts<2^w:=by
    have:=DescentDyadicSpan.span_ge p.hosts
    have:=safe.total
    unfold PeerAperture.endAddress at this
    omega
  have sites : p.oldHosts*(DescentDenseHostOrder.roster u.board u.rootBits u.depth).card=p.hosts:=by
    simp only [PeerAperture.hosts,u.palette]
  have range:p.threshold base+3*(p.oldHosts*(DescentDenseHostOrder.roster u.board u.rootBits u.depth).card)<2^w:=by simpa [sites] using small
  have addrs : p.threshold base+j.val*p.hosts+i.val=p.threshold base+j.val*
      (p.oldHosts*(DescentDenseHostOrder.roster u.board u.rootBits u.depth).card)+i.val:=
    congrArg (fun count : ℕ => p.threshold base + j.val*count + i.val) sites.symm
  rw [addrs]
  unfold memory
  exact (DescentResetTrunkPalette.run u.board u.rootBits u.depth (p.threshold base) p.oldHosts _ range).2.1 j i
end
end Hierarchy.DescentDatedAddressBook.PeerAperture

end OAI
