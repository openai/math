import OAI.Computability.VPVNP.PairVertexRoleDomains
import OAI.Computability.VPVNP.PairVertexCursorDomain
import OAI.Computability.VPVNP.PairSimulationLeafSegment

/-! # Exact native cursor execution on the selected vertex domain -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM BurstRAM.PrivateRAM DFS NodeArguments LocalHistory TreeDecode LeafStartup NativeFrame CursorNetwork
open scoped Fin.CommRing

variable {w endAddr : ℕ} {L : PrimedInputRAM.Lengths} {n a H count : ℕ}
    {Q : PrimedInputRAM.Layout L n a H w} (D : PrimedCounter.Data Q count)
    {b l e degree pad : ℕ} (hD : 1 < b+l) (hd : 2+pad = 2^degree)

local notation "X₀" => LeafArguments.state hD hd (2^e) w
local notation "vals₀" => LeafVisit.cacheWords D (b+l) e

/-- A cursor packet in the selected domain supplies the exact private inputs
of the leaf verification table, including its geometry and public operands. -/
theorem Leaf.toRole {R : LeafArena.Regions} {data : Fin 10 → Word w} {offset node : Word w}
    {cap base : ℕ} {s : Scratch w endAddr} (address : base = ((LeafRole.addressFields data) .base).val)
    (leaf : Leaf (X₀) cap base R data offset (vals₀) node s) :
    LeafRole.Domain (e := e) data D hD hd R cap (frameBase R) node s := by
  obtain ⟨u,z,atNode,fits,stored⟩ := leaf.packet
  let packet := Packet.mk (TraversalRows.sitePointers cap base (siteOrder (X₀)) u).1 (packed (X₀) u z)
  change node.val = packet.node at atNode
  have same : (packet.node : Word w) = node := by
    rw [← atNode]; exact Fin.ext (Nat.mod_eq_of_lt node.isLt)
  have typed : ∃ v h, packet = ⟨(TraversalRows.sitePointers cap ((LeafRole.addressFields data) .base).val
      (siteOrder (X₀)) v).1, packed (X₀) v h⟩ := ⟨u,z,by simp only [packet,← address]⟩
  have verified := LeafRole.domain_of_packet (e := e) D hD hd typed (atNode ▸ leaf.within)
    (atNode ▸ node.isLt) fits stored leaf.frame
  simpa only [same] using verified

/-- Restrict a proved native parser to its actual physical input domain. -/
theorem restrict {p r k : ℕ} {M : Machine w p r k} {pc ret : Fin p} {regs : Fin 9 ↪ Fin r}
    {m : Memory w} {domain sub : Word w → Scratch w endAddr → Prop} {parser : HookParser w endAddr}
    (exactRole : parser.ExactOn domain M pc ret regs m) (ready : ∀ node s, sub node s → domain node s) :
    parser.ExactOn sub M pc ret regs m where
  success node s h := exactRole.success node s (ready node s h)
  reject node bits cfg top pending h := exactRole.reject node bits cfg top pending (ready _ _ h)

variable [NeZero (b+l)] {geometry rootFields shrink refresh : Segment} {p r : ℕ}
    (V : Placement (segments geometry rootFields LeafRole.segment shrink refresh) p r)
    (M : Machine w p r 11) (budget : ProcessorBudget n (b+l) e w)
    (m : Memory w) (header offset : Word w) (arity cap clock base : ℕ)

local notation "regions₀" => fromHeader arity M.publicData header m
local notation "data₀" => leafWords arity M.publicData header offset m

/-- Success and rejection at the physical cursor entry, for arbitrary
nomination tapes at any selected first-layer packet. -/
theorem nativeLeaf (fit : (regions₀).stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    (link : Contains V M) (address : base = ((LeafRole.addressFields (data₀)) .base).val)
    (stride : (m (header+15).val).val = cap+2) (rb : (m (header+18).val).val = 2^b)
    (rl : (m (header+19).val).val = 2^l)
    (span : (m (header+20).val).val = LiveAuxiliaryHeaders.span L D.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header+20).val).val ≤ 2^w)
    (headers : ∀ i < (m (header+20).val).val, (m ((M.publicData 3).val+i)).val = (D.initial i).val)
    (size : (M.publicData 6).val = n)
    (time : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w),
      steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ clock)
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length + clock ≤ n^40) :
    (LeafRole.parser (endAddr := n) (data₀) D budget (regions₀) fit m clock).ExactOn
      (Leaf (X₀) cap base (regions₀) (data₀) offset (vals₀)) M (V.entry .leaf) (V.dfsPC 3) V.dfs m :=
  restrict (LeafRole.site_exact V M D hD hd budget m header offset arity cap clock fit link stride rb rl
    span shadowFit headers size time room) fun _ _ h => Leaf.toRole D hD hd address h

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
