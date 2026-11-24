import OAI.Computability.VPVNP.PairVertexSiteSegments
import OAI.Computability.VPVNP.PairTreeDecodeDomain

/-! # The accepting private tapes of an actual assembled final-site burst -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS LocalHistory NetworkKernel NodeArguments TreeDecode
open scoped Fin.CommRing

variable {geometry rootFields leaf shrink refresh : Segment} {p r W endAddr : ℕ}
    (A : Placement (segments geometry rootFields leaf shrink refresh) p r)
    (M : Machine W p r 11)
    {R : Type*} [CommRing R] {L : Type} [Fintype L] {f : L → R} {N Y : Network}

/-- A genuine singleton-root burst returns on precisely one encoding of
a selected site occurrence. Malformed child tapes and truncated or extra
bits are covered by the two directions of the equivalence. The hypotheses
on computation and storage concern the individual row handlers only. -/
theorem returns_iff_occurrence (linked : Contains A M) (G offset hist : Word W) (m : Memory W)
    (domain : Word W → Scratch W endAddr → Prop) (valid : List Packet → Scratch W endAddr → Prop)
    (resident : ∀ node s, domain node s → ResidentGeometry s G offset hist)
    (head : HeadDomain valid domain)
    (handlers : NodeDispatch.Role → HookParser W endAddr)
    (exactRole : ∀ role, (handlers role).ExactOn
      (fun node saved => domain node saved ∧ NodeDispatch.role (m (offset+node).val) = role)
      M (A.entry (rolePart role)) (A.dfsPC 3) A.dfs m)
    (c : TermChain R N Y) (readers : ChainParsers f c) (ptr : RowPointers c)
    (layers : PacketLayers c) (P : SiteParsers f N) (leaves : N.Site → ℕ × ℕ) (input : Packets N)
    (leafAddress : ∀ v z, (input v z).node = (leaves v).1) (addresses : PointerLayers c ptr layers)
    (leafs : Subtrees (dispatcher handlers m offset) valid P (fun v => leafTree (leaves v)) input)
    (steps : StepLayers (dispatcher handlers m offset) valid c readers ptr layers input)
    (v : Y.Site) (z : Y.Half v)
    (cfg : Config W p r) (here : cfg.pc = A.dfsPC 0) (top : ℕ) (root : Word W)
    (stack : Represents cfg.privateMem top [root]) (length : top+1 = endAddr)
    (sp : cfg.reg (A.dfs 5) = (top : Word W)) (endReg : cfg.reg (A.dfs 6) = (endAddr : Word W))
    (one : cfg.reg (A.dfs 3) = 1) (events : List (Event W))
    (visits : Visits m endAddr [root]
      (((chainTrees c readers ptr (fun u => leafTree (leaves u))) v).preorder.map (fun n : ℕ => (n : Word W))) events)
    (ready : valid [finalPackets c layers input v z] (scratch endAddr cfg.privateMem)) (bits : List Bool) :
    Returns M cfg m bits ↔ ∃! x, bits = ((finalParsers c readers P).read v z).encode x := by
  let H := dispatcher handlers m offset
  let init := fun u => leafTree (leaves u)
  have along := chain_along H valid domain c readers ptr layers P init input leafs
    (leaf_along H valid domain leaves input leafAddress head) steps addresses head
  have decode := chain_exact H valid c readers ptr layers P init input leafs steps
  rw [site_returns linked G offset hist m domain resident handlers exactRole (finish_terminal A M linked)
    visits cfg here top stack length sp endReg one bits (along v z [] _ bits (by simpa using ready))]
  simpa only [List.append_nil] using (decode v z).unique H valid ((finalParsers c readers P).read v z)
    (pending := []) (by simpa using ready) bits []

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
