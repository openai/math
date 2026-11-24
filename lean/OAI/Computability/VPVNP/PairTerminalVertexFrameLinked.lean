import OAI.Computability.VPVNP.PairTerminalVertexFrame
import OAI.Computability.VPVNP.PairSimulationTerminalSplice
import OAI.Computability.VPVNP.PairTraversalControllerMemory

/-!
# Final-site memory under physical terminal dispatch

The controller writes its stage and saved ordinal after each continuing
call. Excluding exactly those two addresses from the motif-counter invariant
allows the next worker to read the selected compressor records, the shared
bits and its immutable header fields directly from the actual memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexFrame

open BurstRAM PrivateRAM Compression CompressorRecords TraversalRows TraversalRoles TerminalLink
open scoped Fin.CommRing

variable {w base grammar g ord : ℕ} {reference m : Memory w} {addr : Word w}

/-- The physical memory agrees with the shared-bit result outside the
motif-counter suffix and the two terminal controller cells. -/
def Linked (addr : Word w) (base grammar g : ℕ) (reference : Memory w) (_ord : ℕ) (phy : Memory w) : Prop :=
  ∀ a, (a < base+grammar ∨ base+grammar+g ≤ a) → workerCell addr a → phy a = reference a

theorem linked_initial (addr : Word w) (base grammar g ord : ℕ) (ref : Memory w) :
    Linked addr base grammar g ref ord ref := fun _ _ _ => rfl

theorem linked_of_agree (h : SourceTransport.Agree (workerCell addr) reference m) (ord base grammar g : ℕ) :
    Linked addr base grammar g reference ord m := fun i _ hi => (h i hi).symm

theorem Stable.linked (h : Stable base grammar g reference ord m) (addr : Word w) :
    Linked addr base grammar g reference ord m := fun i hi _ => h i hi

theorem Linked.preserve (h : Linked addr base grammar g reference ord m) (powers : Fin g → ℕ) :
    Linked addr base grammar g reference (ord+1) (Counters.addHistogram base grammar powers m) :=
  fun i hi hc => (Counters.addHistogram_outside base grammar powers m i hi).trans (h i hi hc)

/-- The worker may terminate or resume. In both cases the actual physical
entry and exit report preserve every selected operand outside the counter suffix. -/
theorem Linked.after_report {raw : Report w} (e : Entry w) {n : ℕ}
    (post : Linked addr base grammar g reference n (after m raw.events)) :
    Linked addr base grammar g reference n (after m (TerminalLink.report addr e raw).events) := by
  rw [report_after]
  cases ht : target e.stage raw.result with
  | none => exact post
  | some p =>
    obtain ⟨s,x⟩ := p
    intro i hi hc
    simpa only [writeMemory,ite_eq_right hc.1,ite_eq_right hc.2] using post i hi hc

theorem Linked.report (h : Linked addr base grammar g reference ord m) (e : Entry w) (raw : Report w)
    (powers : Fin g → ℕ) (flush : after m raw.events = Counters.addHistogram base grammar powers m) :
    Linked addr base grammar g reference (ord+1) (after m (TerminalLink.report addr e raw).events) :=
  Linked.after_report e (flush ▸ h.preserve powers)

private theorem at_offset (addr : Word w) (room : addr.val+32 ≤ 2^w) (j : ℕ) (hj : j<32) :
    (addr+(j : Word w)).val = addr.val+j := by
  rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j<2^w),Nat.mod_eq_of_lt (by omega)]

theorem Linked.below (h : Linked addr base grammar g reference ord m) (room : addr.val+32 ≤ 2^w)
    {x : ℕ} (lo : base+grammar+g ≤ x) (hi : x < addr.val) : m x = reference x := by
  have last : (addr+31).val = addr.val+31 := at_offset addr room 31 (by decide)
  exact h x (.inr lo) ⟨hi.ne,by omega⟩

/-- At every real counter address the linked report applies precisely the
worker's histogram increment. The two controller stores are outside the array. -/
theorem report_motif {raw : Report w} (e : Entry w) (room : addr.val+32 ≤ 2^w)
    (low : base+grammar+g ≤ addr.val) (powers : Fin g → ℕ)
    (flush : after m raw.events = Counters.addHistogram base grammar powers m) (i : Fin g) :
    after m (TerminalLink.report addr e raw).events (base+grammar+i.val) =
      m (base+grammar+i.val) + ((powers i : ℕ) : Word w) := by
  have last : (addr+31).val = addr.val+31 := at_offset addr room 31 (by decide)
  have ix := i.isLt
  have h0 : base+grammar+i.val ≠ addr.val := by omega
  have h31 : base+grammar+i.val ≠ (addr+31).val := by omega
  rw [report_after,flush]
  cases h : target e.stage raw.result with
  | none => exact Counters.addHistogram_at base grammar powers m i
  | some p =>
    obtain ⟨s,x⟩ := p
    simpa only [writeMemory,ite_eq_right h0,ite_eq_right h31] using Counters.addHistogram_at base grammar powers m i

theorem Linked.grammarCell (h : Linked addr base grammar g reference ord m) (room : addr.val+32 ≤ 2^w)
    (low : base+grammar ≤ addr.val) (i : Fin grammar) : m (base+i.val) = reference (base+i.val) := by
  have last : (addr+31).val = addr.val+31 := at_offset addr room 31 (by decide)
  have hi := i.isLt
  exact h _ (.inl (by omega)) ⟨by omega,by omega⟩

theorem Linked.header (h : Linked addr base grammar g reference ord m) (room : addr.val+32 ≤ 2^w)
    (low : base+grammar+g ≤ addr.val) (j : ℕ) (hj : 0<j) (hj' : j<31) :
    m (addr+(j : Word w)).val = reference (addr+(j : Word w)).val := by
  rw [at_offset addr room j (by omega)]
  have last : (addr+31).val = addr.val+31 := at_offset addr room 31 (by decide)
  exact h _ (.inr (by omega)) ⟨by omega,by omega⟩

private def restore (addr : Word w) (ref m : Memory w) : Memory w :=
  fun i => if i = addr.val ∨ i = (addr+31).val then ref i else m i

private theorem Linked.restored (h : Linked addr base grammar g reference ord m) :
    Stable base grammar g reference ord (restore addr reference m) := by
  intro i hi
  unfold restore
  split
  · rfl
  · rename_i hn
    exact h i hi (not_or.mp hn)

private theorem restore_below (room : addr.val+32 ≤ 2^w) :
    ControllerMemory.AgreeBelow addr.val m (restore addr reference m) := by
  intro i hi
  have last : (addr+31).val = addr.val+31 := at_offset addr room 31 (by decide)
  have notControl : ¬ (i=addr.val ∨ i=(addr+31).val) := by omega
  exact (ite_eq_right notControl).symm

theorem Linked.rows (h : Linked addr base grammar g reference ord m) (room : addr.val+32 ≤ 2^w)
    {cap previous first : ℕ} {ls : List Layer} (lo : base+grammar+g ≤ first)
    (hi : first + words cap ls ≤ addr.val) (capacity : ∀ L ∈ ls, ∀ i, (L.ids i).length ≤ cap)
    (data : AllRows w reference cap previous first ls) : AllRows w m cap previous first ls :=
  ControllerMemory.allRows_below ls (restore_below room) hi capacity (h.restored.rows lo ls data)

theorem Linked.roles (h : Linked addr base grammar g reference ord m) (room : addr.val+32 ≤ 2^w)
    {offset cap first : ℕ} {ls : List TaggedLayer} (lo : base+grammar+g ≤ offset+first)
    (hi : offset+first+tagWords cap ls ≤ addr.val) (tags : Reads w reference offset cap first ls) :
    Reads w m offset cap first ls :=
  ControllerMemory.reads_below ls (restore_below room) hi (h.restored.roles lo tags)

theorem Linked.packet (h : Linked addr base grammar g reference ord m) (room : addr.val+32 ≤ 2^w)
    {a k : ℕ} (X : State a k) (L : TerminalRootGather.Layout) (v : X.network.Site)
    (num : TerminalGatherGeometry.Numbering X L v) (rows : TerminalGatherGeometry.Rows X L reference)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (bits : ∀ i, reference (L.wires+i.val) = PrivateFields.bitValue w (f i))
    (bounds : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead],
      base+grammar+g ≤ head ∧ head+TerminalPrefix.arcCount X ≤ addr.val)
    (wires : base+grammar+g ≤ L.wires ∧ L.wires+X.totalWidth ≤ addr.val) :
    L.packet m = (NodeArguments.packed X v (TerminalGatherGeometry.half X f v)).map (PrivateFields.bitValue w) := by
  apply TerminalGatherGeometry.packet_eq num
  · apply rows.transfer X L
    intro head hh i
    obtain ⟨low,high⟩ := bounds head hh
    exact h.below room (low.trans (Nat.le_add_right _ _)) ((Nat.add_lt_add_left i.isLt _).trans_le high)
  · intro j
    have hj := j.isLt.trans_eq (TerminalPrefix.width_sum X)
    exact (h.below room (wires.1.trans (Nat.le_add_right _ _)) ((Nat.add_lt_add_left hj _).trans_le wires.2)).trans (bits j)

end PairSimulation.VertexFrame

end VPVNP
end Computability
end OAI
