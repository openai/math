import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.PairSimulationDFSDecode

/-!
# Pending arguments of the depth-first native hook

The node address indexes a private argument interval. Writing a batch of
child half-wires establishes their exact bit values, preserves distinct
pending siblings, and leaves the DFS stack below the scratch boundary.
The row traversal then propagates the local hook's input invariant through
all visited addresses, including prefixes that reject.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments

open BurstRAM BurstRAM.PrivateRAM DFS
open scoped Fin.CommRing

variable {w endAddr : ℕ}

/-- A genuinely supplied local half-wire argument, named by its node address. -/
structure Packet where
  /-- Absolute DFS node address used as the index of this packet’s interval in the private
  argument arena. -/
  node : ℕ
  /-- Ordered half-wire bits supplied to the node’s handler, stored one bit per word in its
  argument interval. -/
  bits : List Bool

/-- Bounds ensuring the packet starts at or above the DFS stack boundary, occupies at most one
arena stride and ends within the machine-word address space. -/
def Packet.Fits (q : Packet) (A : Arena) (w endAddr : ℕ) : Prop :=
  endAddr ≤ A.base q.node ∧ q.bits.length ≤ A.stride ∧ A.base q.node + q.bits.length ≤ 2^w

/-- Extend the typed scratch to the full private word space solely for
expressing native stores above the stack boundary. -/
def rawScratch (s : Scratch w endAddr) (a : Word w) : Word w :=
  if h : endAddr ≤ a.val then s ⟨a,h⟩ else 0

/-- States that each addressed scratch word of the packet equals the machine-word encoding of
the corresponding bit, beginning at the node’s arena base. -/
def Packet.Stored (q : Packet) (A : Arena) (s : Scratch w endAddr) : Prop :=
  ∀ i : Fin q.bits.length, rawScratch s ((A.base q.node + i.val : ℕ) : Word w) =
    PrivateFields.bitValue w q.bits[i.val]

/-- Updates scratch by storing the packet bits consecutively from its node’s arena base and
restricting the resulting private memory to addresses at or above the stack boundary. -/
def Packet.write (q : Packet) (A : Arena) (s : Scratch w endAddr) : Scratch w endAddr :=
  scratch endAddr (PrivateFields.storeBits (A.base q.node) q.bits (rawScratch s))

private theorem raw_write_at (q : Packet) (A : Arena) (s : Scratch w endAddr) {a : Word w}
    (ha : endAddr ≤ a.val) : rawScratch (q.write A s) a =
      PrivateFields.storeBits (A.base q.node) q.bits (rawScratch s) a := by
  simp [rawScratch, Packet.write, scratch, ha]

private theorem address_val (q : Packet) (A : Arena) (hq : q.Fits A w endAddr)
    (i : Fin q.bits.length) : (((A.base q.node + i.val : ℕ) : Word w)).val = A.base q.node+i.val :=
  Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le hq.2.2)

theorem Packet.stored_write (q : Packet) (A : Arena) (s : Scratch w endAddr)
    (hq : q.Fits A w endAddr) : q.Stored A (q.write A s) := by
  intro i
  rw [raw_write_at _ _ _ (by rw [address_val q A hq i]; exact hq.1.trans (Nat.le_add_right _ _))]
  exact PrivateFields.storeBits_read _ _ _ hq.2.2 i

theorem Packet.stored_other (q p : Packet) (A : Arena) (s : Scratch w endAddr)
    (hq : q.Fits A w endAddr) (hp : p.Fits A w endAddr) (hne : q.node ≠ p.node)
    (stored : p.Stored A s) : p.Stored A (q.write A s) := by
  intro i
  let addr := ((A.base p.node + i.val : ℕ) : Word w)
  have hi : addr.val = A.base p.node + i.val := address_val p A hp i
  have ha := hp.1.trans (Nat.le_add_right (A.base p.node) i.val)
  change rawScratch (q.write A s) addr = _
  rw [raw_write_at q A s (hi ▸ ha)]
  have ho : addr.val < A.base q.node ∨ A.base q.node+q.bits.length ≤ addr.val := by
    rw [hi]
    rcases A.disjoint hne with left | right
    · exact Or.inr ((Nat.add_le_add_left hq.2.1 _).trans (left.trans (Nat.le_add_right _ _)))
    · exact Or.inl ((Nat.add_lt_add_left (i.isLt.trans_le hp.2.1) _).trans_le right)
  rw [PrivateFields.storeBits_outside _ _ _ _ hq.2.2 ho]
  exact stored i

/-- The physical child writes occur in their listed order. -/
def writePackets (A : Arena) (xs : List Packet) (s : Scratch w endAddr) : Scratch w endAddr :=
  xs.foldl (fun old p => p.write A old) s

theorem writePackets_preserves (A : Arena) (xs : List Packet) (p : Packet) (s : Scratch w endAddr)
    (hf : ∀ q ∈ xs, q.Fits A w endAddr) (hp : p.Fits A w endAddr)
    (hne : ∀ q ∈ xs, q.node ≠ p.node) (h : p.Stored A s) :
    p.Stored A (writePackets A xs s) := by
  induction xs generalizing s with
  | nil => exact h
  | cons q qs ih =>
    exact ih _ (fun j hj => hf j (List.mem_cons_of_mem _ hj))
      (fun j hj => hne j (List.mem_cons_of_mem _ hj))
      (q.stored_other p A s (hf q List.mem_cons_self) hp (hne q List.mem_cons_self) h)

/-- Distinct child records retain every bit value assigned to them. -/
theorem writePackets_children (A : Arena) (xs : List Packet) (s : Scratch w endAddr)
    (hf : ∀ q ∈ xs, q.Fits A w endAddr) (hn : (xs.map Packet.node).Nodup) :
    ∀ q ∈ xs, q.Stored A (writePackets A xs s) := by
  induction xs generalizing s with
  | nil => simp
  | cons q qs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    intro p hp
    rcases List.mem_cons.mp hp with rfl | mem
    · exact writePackets_preserves A qs p _ (fun j hj => hf j (List.mem_cons_of_mem _ hj))
        (hf p List.mem_cons_self) (fun j hj he => hn.1 (he ▸ List.mem_map_of_mem hj))
        (p.stored_write A s (hf p List.mem_cons_self))
    · exact ih _ (fun j hj => hf j (List.mem_cons_of_mem _ hj)) hn.2 p mem

/-- Other private work may change the histogram or scratch tables. Matching
the packet's own addressed words is sufficient to retain its arguments. -/
theorem Packet.Stored.congr {q : Packet} {A : Arena} {s t : Scratch w endAddr}
    (h : q.Stored A s) (eqn : ∀ i : Fin q.bits.length,
      rawScratch t ((A.base q.node + i.val : ℕ) : Word w) =
        rawScratch s ((A.base q.node + i.val : ℕ) : Word w)) : q.Stored A t :=
  fun i => (eqn i).trans (h i)

/-- Ghost values of all current argument frames. The predicate on packets
specifies the node's actual half-wire format while retaining all its bit values. -/
def PreparedPackets (A : Arena) (format : Packet → Prop) (xs : List Packet)
    (s : Scratch w endAddr) : Prop :=
  (xs.map Packet.node).Nodup ∧ ∀ q ∈ xs, format q ∧ q.Fits A w endAddr ∧ q.Stored A s

/-- Replace the popped argument by its ordered children. The physical
argument cells of every child and every older pending sibling agree with
the corresponding logical half-wire packet after the native update. -/
theorem preparedPackets_push (A : Arena) (format : Packet → Prop) (head : Packet)
    (children pending : List Packet) (s out : Scratch w endAddr)
    (before : PreparedPackets A format (head::pending) s)
    (valid : ∀ q ∈ children, format q ∧ q.Fits A w endAddr)
    (nodup : ((children ++ pending).map Packet.node).Nodup)
    (agree : ∀ q ∈ children ++ pending, ∀ i : Fin q.bits.length,
      rawScratch out ((A.base q.node + i.val : ℕ) : Word w) =
        rawScratch (writePackets A children s) ((A.base q.node + i.val : ℕ) : Word w)) :
    PreparedPackets A format (children ++ pending) out := by
  rw [List.map_append, List.nodup_append] at nodup
  refine ⟨by simpa only [List.map_append, List.nodup_append] using nodup, ?_⟩
  intro q hq
  have hwrite := fun p hp => (valid p hp).2
  rcases List.mem_append.mp hq with child | sibling
  · obtain ⟨hf,hfit⟩ := valid q child
    exact ⟨hf,hfit,(writePackets_children A children s hwrite nodup.1 q child).congr (agree q hq)⟩
  · obtain ⟨hf,hfit,hs⟩ := before.2 q (List.mem_cons_of_mem _ sibling)
    have sep : ∀ p ∈ children, p.node ≠ q.node := fun p hp eqn =>
      nodup.2.2 p.node (List.mem_map_of_mem hp) q.node (List.mem_map_of_mem sibling) eqn
    exact ⟨hf,hfit,(writePackets_preserves A children q s hwrite hfit sep hs).congr (agree q hq)⟩

end PairSimulation.NodeArguments

namespace PairSimulation.DFS

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

/-- A node's completed local hook establishes the invariant on the recorded
children and preserves it on the existing stack suffix. No reachability
requirement is imposed on unrelated scratch cells. -/
def HookParser.PreparesChildren {w endAddr : ℕ} (P : HookParser w endAddr)
    (domain : Word w → Scratch w endAddr → Prop) (m : Memory w) : Prop :=
  ∀ (node : Word w) src kids pending (s : Scratch w endAddr) bs job tail,
    Row m node.val src kids → (∀ j ∈ node :: pending, domain j s) →
    P.read node s bs = some (job,tail) → ∀ j ∈ kids ++ pending, domain j (job.update s)

/-- A prepared frontier may contain node-specific argument values, stack
separation and histogram information shared by its pending vertices. -/
def HookParser.PreparesFrontier {w endAddr : ℕ} (P : HookParser w endAddr)
    (domain : Word w → Scratch w endAddr → Prop)
    (valid : List (Word w) → Scratch w endAddr → Prop) (m : Memory w) : Prop :=
  ∀ node pending s, valid (node :: pending) s → domain node s ∧
    ∀ src kids bs job tail, Row m node.val src kids → P.read node s bs = some (job,tail) →
      valid (kids ++ pending) (job.update s)

/-- The admissibility of actual hook calls can use the whole current
frontier, including the distinctness of unprocessed sibling buffers. -/
theorem HookParser.validAlong_of_frontier {w endAddr : ℕ} (P : HookParser w endAddr)
    {domain : Word w → Scratch w endAddr → Prop}
    {valid : List (Word w) → Scratch w endAddr → Prop} {m : Memory w}
    {pending nodes : List (Word w)} {es : List (Event w)}
    (visits : Visits m endAddr pending nodes es) (prep : P.PreparesFrontier domain valid m)
    (s : Scratch w endAddr) (bs : List Bool) (hs : valid pending s) :
    P.ValidAlong domain nodes s bs := by
  induction visits generalizing s bs with
  | nil => trivial
  | @cons node pending kids nodes src es row fits rest ih =>
    obtain ⟨head, tail⟩ := prep node pending s hs
    exact ⟨head, fun job suffix hread => ih _ _ (tail src kids bs job suffix row hread)⟩

/-- Follow the concrete chronological DFS. Every hook is entered on its
prepared argument cells, for every possible remaining binary stream. -/
theorem HookParser.validAlong_of_visits {w endAddr : ℕ} (P : HookParser w endAddr)
    {domain : Word w → Scratch w endAddr → Prop} {m : Memory w}
    {pending nodes : List (Word w)} {es : List (Event w)}
    (visits : Visits m endAddr pending nodes es)
    (hchild : P.PreparesChildren domain m) (s : Scratch w endAddr) (bs : List Bool)
    (hroot : ∀ j ∈ pending, domain j s) : P.ValidAlong domain nodes s bs := by
  exact P.validAlong_of_frontier visits
    (valid := fun pending s => ∀ j ∈ pending, domain j s)
    (fun node pending s h => ⟨h node List.mem_cons_self, fun src kids bs job tail row hread =>
      hchild node src kids pending s bs job tail row h hread⟩) s bs hroot

end PairSimulation.DFS

end VPVNP
end Computability
end OAI
