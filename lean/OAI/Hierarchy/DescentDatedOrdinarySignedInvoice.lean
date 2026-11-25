import OAI.Hierarchy.DescentDatedSignedLimits
import OAI.Hierarchy.DescentDatedOrdinarySignedPhase
import OAI.Hierarchy.DescentSignedPrefixInvoice
import OAI.Hierarchy.DescentOrdinarySignedInvoice
import OAI.Hierarchy.DescentOrdinaryControlWork

namespace OAI
/-! The fixed ordinary signed date is charged for the two actual traversals,
the resident-field compilation, and each public literal page, including holes. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty.Chronology DescentHaloWalkRAM DescentSIMDLookup DescentDyadicSpan DescentPackedColony
open DescentParallelBase DescentParallelBase.ParentFilter DescentPackedZip DescentOrdinarySignedDate DescentOrdinarySignedMeta
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentStaticWordColumn (names)
noncomputable section
variable (s:SignedExtent) (I:s.Input) (base w K:ℕ)

structure SnippetWork (s:SignedExtent) (I:s.Input) (K:ℕ):Prop where
  degree:I.newDegree≤K
  path:∀z,(I.path z).work≤K
  endpoints:∀z t,(I.endpoints z t).work≤K
  donor:∀z i,(I.donor z i).work≤K
  mark:∀z,(I.mark z).work≤K
  forward:∀x o,(I.donorForward x o).work≤K
  low:∀x o,(I.donorLow x o).work≤K

theorem rank_work (ok:s.SnippetWork I K) (z:s.Socket) (i:Fin 5):
    (s.rankField I base z i).work ≤ s.rankCost K:=by
  simp only [rankField,DescentPackedChildNeighbor.SIMD.work,List.length_finRange,DescentPackedZip.work,rankCost]
  have a:=ok.path z;have b:=ok.endpoints z (DescentOrdinaryDonorSources.PathKeys.side i)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _

theorem parent_work (ok:s.SnippetWork I K) (z:s.Socket) (f:Fin 11):
    (s.donorField I base z f).work≤donorCost K:=by
  dsimp only [donorField, donorCost]
  apply DescentOrdinaryDonorSources.work _ _ _ (K+16) ?_ ?_ f
  · intro j;have:=ok.donor z j;omega
  · intro j;dsimp only [Expr.work];omega

theorem route_work (ok:s.SnippetWork I K) (c:s.Consumer) (f:Fin 11):
    (s.routed I base c f).work ≤ s.routeCost K:=by
  dsimp only [routed]
  split
  · apply (SourceReturn.RAM.work ..).trans
    unfold routeCost;apply Nat.add_le_add_left;apply Nat.mul_le_mul_left;apply Nat.add_le_add_right
    simp only [routeQuery,SourceReturn.Query.expr,backDigit,DescentPackedZip.work,DescentPackedChildNeighbor.SIMD.work,List.length_finRange,queryCost]
    have a:=ok.forward c.1.1 (s.priorSlot c).2
    have b:=ok.low c.1.1 (s.priorSlot c).2
    have p:=Nat.mul_le_mul_left s.reach (Nat.add_le_add_right a 36)
    omega
  · change 1≤1+_;omega

private theorem within_index {n:ℕ} (f:Fin n→Expr) {lim:ℕ} (cost:∀i,(f i).work≤lim) (i:ℕ) (hi:i<n):
    (fromIndex f i).work≤lim:=by rw [fromIndex,dite_eq_left hi];exact cost _

theorem prefix_work (ok:s.SnippetWork I K):∀j∈s.jobs I base,j.within (s.prepLimit K):=by
  have bound (n:ℕ) (h:n≤120):n ≤ s.prepLimit K:=by unfold prepLimit;omega
  have ranks:=fun z i=>(s.rank_work I base K ok z i).trans (by unfold prepLimit;omega : s.rankCost K ≤ s.prepLimit K)
  have donorRows:=fun z i=>(s.parent_work I base K ok z i).trans (by unfold prepLimit;omega : donorCost K ≤ s.prepLimit K)
  have routes:=fun c f=>(s.route_work I base K ok c f).trans (by unfold prepLimit;omega : s.routeCost K ≤ s.prepLimit K)
  intro j hj
  simp only [jobs,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> try trivial
  all_goals intro j hj
  all_goals first | apply within_index _ _ j hj;intro i | skip
  · exact bound _ (DescentOrdinaryDonorRankDirectory.expression_work_le_120 ..)
  · apply bound
    norm_num [indexed, transposed, Expr.work]
  · apply ranks
  · apply donorRows
  · apply bound
    norm_num [indexed, transposed, Expr.work]
  · apply routes
  · change (s.peerHeadExpr I base).work ≤ s.prepLimit K
    rw [peerHeadExpr,DescentOrdinaryCompactPeer.work]
    have d:=Nat.mul_le_mul_right (30+36*(s.reach*s.reach)) ok.degree
    unfold prepLimit directoryCost;omega

private theorem block_read (z:s.Socket) (f:Fin 11):(s.rawField base z f).work≤12:=by simp [rawField,Expr.work]

theorem operand_work (ok:s.SnippetWork I K) (c:s.Consumer) (f:Fin 11):
    (s.operand I base c f).work≤gatedLimit K:=by
  let raw:=Fused.TablesROM.joins s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes (s.shapesStart base)
  have flag:=RawControls.expression_work raw (s.rawField base (c.1.1,c.2.1)) (I.mark (c.1.1,c.2.1)) (RawControls.flagsTable (s.rawStart base) s.fieldBits s.fieldBits s.lanes) 12
    (s.block_read base (c.1.1,c.2.1))
  have m:=ok.mark (c.1.1,c.2.1)
  have late:(s.remoteWord I base c f).work≤128:=by simp [remoteWord,Expr.work]
  have early:=s.block_read base (s.socketAt c) f
  unfold operand;rw [DescentPackedZip.work]
  split <;> change _≤512+K <;> dsimp only [flags,gathered,raw] at * <;> omega

theorem header_work (ok:s.SnippetWork I K) (z:s.Socket):
    ((s.layout I base).header z.1 z.2).work ≤ s.headerLimit K:=by
  have raw (lut:Tables): (lut.read (s.gathered base z) (I.mark z)).work≤1+11*(12+11)+(I.mark z).work+11:=
    RawControls.expression_work _ _ _ _ _ (s.block_read base z)
  have input:(s.gathered base z).work≤1+11*(12+11):=by
    simpa only [List.length_finRange,gathered,DescentPacking.PackedMatch.Local.Gather.assembly] using
      DescentPacking.PackedMatch.Local.Gather.collect_work _ (s.rawField base z) (List.finRange 11) 12 (s.block_read base z)
  have peer:(s.peerField I base z).work≤1+s.peerKinds*512:=by
    simp only [peerField,DescentPackedChildNeighbor.SIMD.work,List.length_finRange,DescentOrdinarySocketPeer.query,Expr.work]
    apply Nat.add_le_add_left;apply Nat.mul_le_mul_left;omega
  rcases z with ⟨x,j⟩
  have f:=raw (RawControls.flagsTable (s.rawStart base) s.fieldBits s.fieldBits s.lanes)
  have u:=raw (RawControls.unitsTable (s.rawStart base) s.fieldBits s.fieldBits s.lanes)
  have m:=ok.mark (x,j)
  simp only [layout,DescentOrdinarySignedMeta.mountedExpr,DescentOrdinarySignedMeta.expression,DescentPackedZip.work,flags,headerLimit] at *
  omega

local notation "lay"=>s.layout I base
local notation "cut"=>s.tailStart base
local notation "paid"=>s.candidates
local notation "u"=>s.headerLimit K
local notation "v"=>gatedLimit K
local notation "N"=>s.slab
local notation "dhead"=>Fused.TablesROM.length s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes+
  2*2^(DescentOrdinarySignedParents.ROM.width s.fieldBits s.lanes)
local notation "rhead"=>DescentResetSignedScan.Ranks.headWords s.fieldBits s.lanes
local notation "mhead"=>32*2^(DescentResetFieldAssembler.width s.fieldBits s.lanes)
local notation "shead"=>DescentNextSignedWindow.Native.All.headWords s.cap s.fieldBits s.lanes
local notation "nr"=>DescentResetSignedScan.Ranks.count s.blocks paid
local notation "ns"=>DescentNextSignedWindow.Native.All.count s.blocks s.cap
local notation "wr"=>1+paid*(2*(13+11*(v+11))+12)
local notation "ws"=>1+(2*paid)*(14+8*((u+18)+11))

def clockInvoice:=
  ((s.jobs I base).map (SignedPrefix.Job.clocks (s.prepLimit K))).sum+
  ((8+10*dhead)+((4+10*rhead)+(4+nr*(4+N*(2*wr+4))))+
    ((4+10*mhead)+((4+10*shead)+(4+ns*(4+N*(2*ws+4))))))
def textInvoice:=
  ((s.jobs I base).map (SignedPrefix.Job.textSize (s.prepLimit K))).sum+
  (15*(dhead+2)+(15*(rhead+1)+15+nr*(11+4*wr))+
    (15*(mhead+1)+(15*(shead+1)+15+ns*(11+4*ws))))

theorem phase_cost (ok:s.SnippetWork I K):
    s.phaseTicks I base w ≤ s.clockInvoice I base K ∧ names (s.phase I base w).program ≤ s.textInvoice I base K:=by
  have p:=SignedPrefix.invoice (fun _=>s.kernel I base w) (s.jobs I base) base (s.prepLimit K) (s.prefix_work I base K ok)
  have q:=Layout.clock_bound (D:=s.degree) (Q:=s.lowSites) (K:=s.tickets) (L:=s.cap) (b:=s.fieldBits) (M:=s.lanes)
    (H:=s.hosts) (G:=s.groups) lay cut I.newDegree u v (fun x j=>s.header_work I base K ok (x,j))
    (fun x p j f=>s.operand_work I base K ok ((x,p),(j,0)) f) (fun x p j a f=>s.operand_work I base K ok ((x,p),(j,a.succ)) f)
  have t:=Layout.text_bound (w:=w) (D:=s.degree) (Q:=s.lowSites) (K:=s.tickets) (L:=s.cap) (b:=s.fieldBits) (M:=s.lanes)
    (H:=s.hosts) (G:=s.groups) lay cut I.newDegree u v (fun x j=>s.header_work I base K ok (x,j))
    (fun x p j f=>s.operand_work I base K ok ((x,p),(j,0)) f) (fun x p j a f=>s.operand_work I base K ok ((x,p),(j,a.succ)) f)
  exact ⟨p.1.trans (Nat.add_le_add_left q _), p.2.trans (Nat.add_le_add_left t _)⟩

theorem fixed_cost (ok:s.SnippetWork I K):
    s.phaseTicks I base w ≤ s.fixedTime K ∧ names (s.phase I base w).program ≤ s.fixedNames K:=by
  let js:=s.jobs I base
  have measuredCost:=s.phase_cost I base w K ok
  have real:∀j∈js,j.pitched:=by
    intro j hj
    simp only [js,jobs,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst j <;> first | exact True.intro | exact ⟨span_ge _,Nat.two_pow_pos _⟩
  have bound:=SignedPrefix.budgets js (s.prepLimit K) real
  have parts:(js.map SignedPrefix.Job.width).sum ≤ s.roof 0:=by
    have edge:=SignedPrefix.width_sum js base
    rw [s.finish_jobs I base] at edge
    have hi:s.tailStart base ≤ s.phaseEnd base:=by
      let a:=DescentOrdinarySignedParents.ROM.endAddress (s.tailStart base) s.degree s.lowSites s.tickets s.cap s.fieldBits s.lanes
      have a₀:s.tailStart base≤a:=by dsimp [a,DescentOrdinarySignedParents.ROM.endAddress];omega
      have hi:=DescentOrdinarySignedAll.ordered (X:=s.blocks) (K:=s.candidates) (b:=s.fieldBits) (M:=s.lanes) (H:=s.hosts) (gg:=s.groups) (cap:=s.cap) a
      exact a₀.trans (hi.1.trans hi.2)
    rw [s.calibrated base,s.shift base] at hi;omega
  have count:js.length=21:=rfl
  have max_:=Nat.mul_le_mul_left (20*(s.prepLimit K+1)) (Nat.add_le_add_left parts 21)
  rw [←count] at max_
  exact ⟨measuredCost.1.trans (Nat.add_le_add_right (bound.1.trans max_) _),
    measuredCost.2.trans (Nat.add_le_add_right (bound.2.trans max_) _)⟩

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
