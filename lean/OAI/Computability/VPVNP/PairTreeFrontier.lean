import OAI.Computability.VPVNP.PairTreeDecodeDomain

/-!
# Prepared packets and the unvisited descriptor subtrees

Distinct current addresses alone would allow a pending sibling to occupy
a child's address. The frontier therefore records the numerical preorders
of the entire remaining subtrees. Popping a row and exposing its children
removes precisely one address from this list, regardless of the guessed
half-wire values and regardless of whether a later visit accepts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NodeArguments
open scoped Fin.CommRing

variable {W endAddr : ℕ}

/-- Preorder address list of a packet's subtree, beginning with its node followed by the
recorded descendant addresses. -/
def subtreeAddresses (desc : ℕ → List ℕ) (q : Packet) := q.node :: desc q.node

private theorem roots_sublist (desc : ℕ → List ℕ) (pending : List Packet) :
    (pending.map Packet.node).Sublist (pending.flatMap (subtreeAddresses desc)) := by
  induction pending with
  | nil => exact List.Sublist.refl _
  | cons q qs ih =>
    exact .cons_cons _ (ih.trans (List.sublist_append_right (desc q.node) _))

/-- The whole private state outside live argument packets is constrained
only by the supplied stability predicate, for instance the resident geometry
and operand cache. The typed format accepts arbitrary old half-wire values. -/
structure Frontier (arena : Arena) (format : Packet → Prop) (stable : Scratch W endAddr → Prop)
    (desc : ℕ → List ℕ) (pending : List Packet) (s : Scratch W endAddr) : Prop where
  frame : stable s
  prepared : PreparedPackets arena format pending s
  disjoint : (pending.flatMap (subtreeAddresses desc)).Nodup

variable {arena : Arena} {format : Packet → Prop} {stable : Scratch W endAddr → Prop}
    {desc : ℕ → List ℕ}

theorem Frontier.singleton {q : Packet} {s : Scratch W endAddr} (frame : stable s)
    (type : format q) (fits : q.Fits arena W endAddr) (stored : q.Stored arena s)
    (tree : (subtreeAddresses desc q).Nodup) :
    Frontier arena format stable desc [q] s := by
  refine ⟨frame,⟨by simp,?_⟩,by simpa using tree⟩
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact ⟨type,fits,stored⟩

theorem Frontier.head {q : Packet} {pending : List Packet} {s : Scratch W endAddr}
    (h : Frontier arena format stable desc (q::pending) s) :
    stable s ∧ format q ∧ q.Fits arena W endAddr ∧ q.Stored arena s :=
  ⟨h.frame,h.prepared.2 q List.mem_cons_self⟩

/-- The actual typed role domain only needs the first prepared packet,
its numerical address and its physical scratch. -/
theorem frontier_headDomain (domain : Word W → Scratch W endAddr → Prop)
    (ready : ∀ (q : Packet) s, stable s → format q → q.Fits arena W endAddr →
      q.Stored arena s → domain (q.node : Word W) s) :
    HeadDomain (Frontier arena format stable desc) domain :=
  fun q _ s h => ready q s h.head.1 h.head.2.1 h.head.2.2.1 h.head.2.2.2

/-- A leaf may change its own private workspace. No old pending packet is
lost if its fitted interval remains stored and the common frame persists. -/
theorem Frontier.pop {head : Packet} {pending : List Packet} {s out : Scratch W endAddr}
    (h : Frontier arena format stable desc (head::pending) s) (frame : stable out)
    (keep : ∀ q ∈ pending, q.Fits arena W endAddr → q.Stored arena s → q.Stored arena out) :
    Frontier arena format stable desc pending out := by
  have disjoint := (List.sublist_append_right (subtreeAddresses desc head)
    (pending.flatMap (subtreeAddresses desc))).nodup h.disjoint
  refine ⟨frame,⟨(roots_sublist desc pending).nodup disjoint,?_⟩,disjoint⟩
  intro q hq
  obtain ⟨type,fits,stored⟩ := h.prepared.2 q (List.mem_cons_of_mem _ hq)
  exact ⟨type,fits,keep q hq fits stored⟩

/-- The children are precisely the next packets in the row's stored
placement order. Their regions cannot collide with any older pending
sibling, because all these subtrees already belonged to a disjoint forest. -/
theorem Frontier.push {head : Packet} {children pending : List Packet} {s out : Scratch W endAddr}
    (h : Frontier arena format stable desc (head::pending) s)
    (shape : desc head.node = children.flatMap (subtreeAddresses desc)) (frame : stable out)
    (types : ∀ q ∈ children, format q ∧ q.Fits arena W endAddr)
    (agree : ∀ q ∈ children++pending, ∀ i : Fin q.bits.length,
      rawScratch out ((arena.base q.node+i.val : ℕ) : Word W) =
        rawScratch (writePackets arena children s) ((arena.base q.node+i.val : ℕ) : Word W)) :
    Frontier arena format stable desc (children++pending) out := by
  have disjoint : ((children++pending).flatMap (subtreeAddresses desc)).Nodup := by
    have hd := h.disjoint
    change (head.node :: (desc head.node ++ pending.flatMap (subtreeAddresses desc))).Nodup at hd
    rw [shape] at hd
    simpa only [List.flatMap_append] using (List.nodup_cons.mp hd).2
  exact ⟨frame,preparedPackets_push arena format head children pending s out h.prepared types
    ((roots_sublist desc (children++pending)).nodup disjoint) agree,disjoint⟩

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
