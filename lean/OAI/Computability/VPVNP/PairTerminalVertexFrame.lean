import OAI.Computability.VPVNP.PairSimulationCounters
import OAI.Computability.VPVNP.PairTerminalGatherGeometry
import OAI.Computability.VPVNP.PairTraversalRoleExecution

/-!
# External memory throughout the final-site traversal

The site's successful flush changes only its motif-counter suffix. The same
typed root packet, child rows, role words, auxiliary input, grammar choices
and header fields can consequently be read at each later ordinal. The bounds
used for the live machine are those of its eleven public operands.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexFrame

open BurstRAM PrivateRAM Compression CompressorRecords TraversalRows TraversalRoles
open scoped Fin.CommRing

variable {w base grammar g : ℕ} {reference m : Memory w} {ord : ℕ}

/-- Only the contiguous motif counter suffix may differ from the shared-bit
stage's output. The ordinal index matches the ascending vertex interpreter. -/
def Stable (base grammar g : ℕ) (reference : Memory w) (_ord : ℕ) (m : Memory w) : Prop :=
  ∀ a, a < base+grammar ∨ base+grammar+g ≤ a → m a = reference a

theorem initial (base grammar g ord : ℕ) (reference : Memory w) :
    Stable base grammar g reference ord reference := fun _ _ => rfl

theorem Stable.preserve (h : Stable base grammar g reference ord m) (powers : Fin g → ℕ) :
    Stable base grammar g reference (ord+1) (Counters.addHistogram base grammar powers m) :=
  fun a ha => (Counters.addHistogram_outside base grammar powers m a ha).trans (h a ha)

theorem Stable.visit {V : Type*} (h : Stable base grammar g reference ord m)
    (hist : V → Fin g → ℕ) (sites : List V) :
    Stable base grammar g reference (ord+sites.length) (Counters.visit base grammar hist sites m) :=
  fun a ha => (Counters.visit_outside base grammar hist sites m a ha).trans (h a ha)

theorem Stable.grammarCell (h : Stable base grammar g reference ord m) (j : Fin grammar) :
    m (base+j.val) = reference (base+j.val) := h _ (.inl (Nat.add_lt_add_left j.isLt _))

theorem Stable.above (h : Stable base grammar g reference ord m) {lo : ℕ}
    (sep : base+grammar+g ≤ lo) (j : ℕ) : m (lo+j) = reference (lo+j) :=
  h _ (.inr (sep.trans (Nat.le_add_right _ _)))

theorem Stable.header (h : Stable base grammar g reference ord m) (head : Word w)
    (sep : base+grammar+g ≤ head.val) (room : head.val+32 ≤ 2^w) (j : ℕ) (hj : j < 32) :
    m (head+(j : Word w)).val = reference (head+(j : Word w)).val := by
  rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j<2^w),Nat.mod_eq_of_lt (by omega)]
  exact h.above sep j

theorem Stable.rows (h : Stable base grammar g reference ord m) {cap previous first : ℕ}
    (sep : base+grammar+g ≤ first) (ls : List Layer) (rows : AllRows w reference cap previous first ls) :
    AllRows w m cap previous first ls := by
  induction ls generalizing previous first with
  | nil => trivial
  | cons L ls ih =>
    refine ⟨fun i => ?_,ih (sep.trans (Nat.le_add_right _ _)) rows.2⟩
    let node := address cap first i.val
    have low : base+grammar+g ≤ node := sep.trans (Nat.le_add_right _ _)
    obtain ⟨hn,hn1,hs,h0,h1,hj⟩ := rows.1 i
    exact ⟨hn,hn1,hs,(h _ (.inr low)).trans h0,(h.above low 1).trans h1,
      fun j => (h.above (low.trans (Nat.le_add_right node 2)) j.val).trans (hj j)⟩

open private reads_above from OAI.Computability.VPVNP.PairTraversalRoleExecution

theorem Stable.roles (h : Stable base grammar g reference ord m) {offset cap first : ℕ}
    (sep : base+grammar+g ≤ offset+first) {ls : List TaggedLayer} (tags : Reads w reference offset cap first ls) :
    Reads w m offset cap first ls := reads_above tags (fun x hx => h x (.inr (sep.trans hx)))

theorem Stable.gatherRows (h : Stable base grammar g reference ord m) {a labels : ℕ} (X : State a labels)
    (L : TerminalRootGather.Layout) (rows : TerminalGatherGeometry.Rows X L reference)
    (sep : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead], base+grammar+g ≤ head) :
    TerminalGatherGeometry.Rows X L m := rows.transfer X L (fun head hh i => h.above (sep head hh) i.val)

theorem Stable.packet (h : Stable base grammar g reference ord m) {a labels : ℕ} (X : State a labels)
    (L : TerminalRootGather.Layout) (v : X.network.Site) (num : TerminalGatherGeometry.Numbering X L v)
    (rows : TerminalGatherGeometry.Rows X L reference)
    (sep : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead,L.wires], base+grammar+g ≤ head)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (bits : ∀ i, reference (L.wires+i.val) = PrivateFields.bitValue w (f i)) :
    L.packet m = (NodeArguments.packed X v (TerminalGatherGeometry.half X f v)).map (PrivateFields.bitValue w) := by
  apply TerminalGatherGeometry.packet_eq num
    (h.gatherRows X L rows (fun head hh => sep head (List.mem_append_left [L.wires] hh))) f
  exact fun j => (h.above (sep _ (by simp)) j.val).trans (bits j)

end PairSimulation.VertexFrame

end VPVNP
end Computability
end OAI
