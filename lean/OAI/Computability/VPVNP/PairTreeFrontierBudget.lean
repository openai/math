import OAI.Computability.VPVNP.PairTreeFrontier

/-!
# Word headroom for every pending vertex

Each remaining vertex can add at most `nodeCap` to any one label counter.
The total allowance decreases by exactly one vertex when a row exposes its
children, including a leaf with no children. This bounds every intermediate
counter on arbitrary accepting prefixes, before the native word addition.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TreeDecode

open BurstRAM PrivateRAM DFS NodeArguments
open scoped Fin.CommRing

variable {W endAddr : ℕ} {Label : Type*}
variable {arena : Arena} {format : Packet → Prop} {stable : Scratch W endAddr → Prop}
  {desc : ℕ → List ℕ} {hist : Scratch W endAddr → Label → ℕ} {nodeCap limit : ℕ}

/-- Count the unvisited vertices, including descendants of pending roots. -/
def remaining (desc : ℕ → List ℕ) (pending : List Packet) : ℕ :=
  (pending.flatMap (subtreeAddresses desc)).length

theorem remaining_step {head : Packet} {children pending : List Packet}
    (shape : desc head.node = children.flatMap (subtreeAddresses desc)) :
    remaining desc (head :: pending) = remaining desc (children ++ pending) + 1 := by
  simp [remaining,subtreeAddresses,List.flatMap_append,← shape,Nat.add_comm,
    Nat.add_left_comm]

/-- The bound applies to each label separately, also when a later node
reads a field that was not reached on a successful whole-site path. -/
structure Budgeted (arena : Arena) (format : Packet → Prop) (stable : Scratch W endAddr → Prop)
    (desc : ℕ → List ℕ) (hist : Scratch W endAddr → Label → ℕ) (nodeCap limit : ℕ)
    (pending : List Packet) (s : Scratch W endAddr) : Prop where
  frontier : Frontier arena format stable desc pending s
  room : ∀ l, hist s l + remaining desc pending * nodeCap ≤ limit

theorem Budgeted.singleton {q : Packet} {s : Scratch W endAddr}
    (front : Frontier arena format stable desc [q] s) (zero : ∀ l, hist s l = 0)
    (fit : (subtreeAddresses desc q).length * nodeCap ≤ limit) :
    Budgeted arena format stable desc hist nodeCap limit [q] s := by
  refine ⟨front,fun l => ?_⟩
  simpa only [zero l,Nat.zero_add,remaining,
    List.flatMap_cons,List.flatMap_nil,List.append_nil] using fit

/-- A nonempty frontier always has room for the local update, before its
value is represented modulo the machine's word size. -/
theorem Budgeted.headRoom {head : Packet} {pending : List Packet} {s : Scratch W endAddr}
    (h : Budgeted arena format stable desc hist nodeCap limit (head :: pending) s) (l : Label) :
    hist s l + nodeCap ≤ limit := by
  have one : 1 ≤ remaining desc (head :: pending) := by simp [remaining,subtreeAddresses]
  have step := Nat.mul_le_mul_right nodeCap one
  rw [Nat.one_mul] at step
  exact (Nat.add_le_add_left step _).trans (h.room l)

theorem Budgeted.word_add {head : Packet} {pending : List Packet} {s : Scratch W endAddr}
    (h : Budgeted arena format stable desc hist nodeCap limit (head :: pending) s)
    (wordFit : limit < 2 ^ W) (l : Label) {delta : ℕ} (small : delta ≤ nodeCap) :
    ((hist s l : Word W) + (delta : Word W)).val = hist s l + delta := by
  have lt := ((Nat.add_le_add_left small (hist s l)).trans (h.headRoom l)).trans_lt wordFit
  rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt lt]

theorem Budgeted.advance {head : Packet} {children pending : List Packet}
    {s out : Scratch W endAddr}
    (h : Budgeted arena format stable desc hist nodeCap limit (head :: pending) s)
    (shape : desc head.node = children.flatMap (subtreeAddresses desc))
    (front : Frontier arena format stable desc (children ++ pending) out)
    (localBound : ∀ l, hist out l ≤ hist s l + nodeCap) :
    Budgeted arena format stable desc hist nodeCap limit (children ++ pending) out := by
  refine ⟨front,fun l => ?_⟩
  have old := h.room l
  rw [remaining_step shape,Nat.add_mul,Nat.one_mul] at old
  have step := Nat.add_le_add_right (localBound l) (remaining desc (children ++ pending)*nodeCap)
  omega

theorem Budgeted.pop {head : Packet} {pending : List Packet} {s out : Scratch W endAddr}
    (h : Budgeted arena format stable desc hist nodeCap limit (head :: pending) s)
    (leaf : desc head.node = []) (frame : stable out)
    (keep : ∀ q ∈ pending, q.Fits arena W endAddr → q.Stored arena s → q.Stored arena out)
    (zero : ∀ l, hist out l = hist s l) :
    Budgeted arena format stable desc hist nodeCap limit pending out := by
  exact h.advance (children := []) leaf (h.frontier.pop frame keep)
    (fun l => (zero l).le.trans (Nat.le_add_right _ _))

theorem Budgeted.push {head : Packet} {children pending : List Packet} {s out : Scratch W endAddr}
    (h : Budgeted arena format stable desc hist nodeCap limit (head :: pending) s)
    (shape : desc head.node = children.flatMap (subtreeAddresses desc)) (frame : stable out)
    (types : ∀ q ∈ children, format q ∧ q.Fits arena W endAddr)
    (agree : ∀ q ∈ children ++ pending, ∀ i : Fin q.bits.length,
      rawScratch out ((arena.base q.node+i.val : ℕ) : Word W) =
        rawScratch (writePackets arena children s) ((arena.base q.node+i.val : ℕ) : Word W))
    (localBound : ∀ l, hist out l ≤ hist s l + nodeCap) :
    Budgeted arena format stable desc hist nodeCap limit (children ++ pending) out :=
  h.advance shape (h.frontier.push shape frame types agree) localBound

theorem budgeted_headDomain (domain : Word W → Scratch W endAddr → Prop)
    (ready : ∀ (q : Packet) s, stable s → format q → q.Fits arena W endAddr → q.Stored arena s →
      (∀ l, hist s l + nodeCap ≤ limit) → domain (q.node : Word W) s) :
    HeadDomain (Budgeted arena format stable desc hist nodeCap limit) domain :=
  fun q _ s h => ready q s h.frontier.head.1 h.frontier.head.2.1 h.frontier.head.2.2.1
    h.frontier.head.2.2.2 h.headRoom

end PairSimulation.TreeDecode

end VPVNP
end Computability
end OAI
