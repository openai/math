import OAI.Computability.VPVNP.PairShrinkCallFrameStores

/-!
# Vertex frame, counters and packet cells after both shrinking field stores

The old-child packets lie between the geometry pointer and the histogram. The
hidden-field slots lie beyond the verifier stacks. Hence the physical memory
passed to the first map has the original frame and histogram, and reads each
argument packet exactly as the child batch wrote it.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open BurstRAM DFS NodeArguments LeafSourceLoad VertexImage TreeDecode
open scoped Fin.CommRing
open private child_outside from OAI.Computability.VPVNP.PairShrinkCallFrameStores

variable {w n pitch : ℕ} {R : LeafArena.Regions} {priv : Word w → Word w}
  {qs : List Packet} {es : List ShrinkHiddenGuess.Row}
local notation "heap" => ShrinkCallABI.hiddenBase R n
local notation "G" => NativeFrame.frameBase R
local notation "childMem" => ChildScan.storePackets R.arguments qs priv
local notation "written" => scratch n (ShrinkHiddenGuess.storeRows heap pitch es childMem)

namespace ShrinkRole

private theorem rawScratch_of_eq {m₁ m₂ : Word w → Word w} (x : Word w) (h : m₁ x = m₂ x) :
    rawScratch (scratch n m₁) x = rawScratch (scratch n m₂) x := by
  by_cases live : n ≤ x.val <;> simp [rawScratch, scratch, live, h]

private theorem fields_outside (x : Word w)
    (room : ∀ e ∈ es, heap + e.1 * pitch + e.2.length ≤ 2 ^ w)
    (fits : ∀ q ∈ qs, q.Fits R.arguments w n) (below : x.val < heap)
    (outside : ∀ q ∈ qs, x.val < R.arguments.base q.node ∨
      R.arguments.base q.node + q.bits.length ≤ x.val) :
    rawScratch written x = rawScratch (scratch n priv) x := by
  apply rawScratch_of_eq
  exact (ShrinkCallFrameLive.hidden_below heap pitch es x room below).trans
    (child_outside R.arguments qs x (fun q hq ↦ (fits q hq).2.2) outside)

private theorem fields_above_arguments (k : ℕ) (lo : R.histBase ≤ k) (hi : k < heap)
    (heapFit : heap ≤ 2 ^ w) (room : ∀ e ∈ es, heap + e.1 * pitch + e.2.length ≤ 2 ^ w)
    (fits : ∀ q ∈ qs, q.Fits R.arguments w n) (nodes : ∀ q ∈ qs, q.node < R.nodes) :
    rawScratch written (k : Word w) = rawScratch (scratch n priv) (k : Word w) := by
  have val : (k : Word w).val = k := Nat.mod_eq_of_lt (hi.trans_le heapFit)
  apply fields_outside (k : Word w) room fits (val.le.trans_lt hi)
  intro q hq
  exact .inr ((Nat.add_le_add_left (fits q hq).2.1 _).trans
    ((R.node_before (nodes q hq)).trans (lo.trans val.ge)))

/-- The physical word of an individual histogram counter survives both readers. -/
theorem fields_histCell (k : ℕ) (within : k < R.histWords) (heapFit : heap ≤ 2 ^ w)
    (room : ∀ e ∈ es, heap + e.1 * pitch + e.2.length ≤ 2 ^ w)
    (fits : ∀ q ∈ qs, q.Fits R.arguments w n) (nodes : ∀ q ∈ qs, q.node < R.nodes) :
    rawScratch written ((R.histBase + k : ℕ) : Word w) =
      rawScratch (scratch n priv) ((R.histBase + k : ℕ) : Word w) := by
  have before := R.hist_before
  have stack : R.cacheBase + 38 ≤ heap := Nat.le_add_right ..
  exact fields_above_arguments _ (Nat.le_add_right ..) (by omega) heapFit room fits nodes

/-- Both readers retain the original value of the entire typed histogram. -/
theorem fields_histogram {Label : Type} (order : Fin R.histWords ≃ Label)
    (heapFit : heap ≤ 2 ^ w) (room : ∀ e ∈ es, heap + e.1 * pitch + e.2.length ≤ 2 ^ w)
    (fits : ∀ q ∈ qs, q.Fits R.arguments w n) (nodes : ∀ q ∈ qs, q.node < R.nodes) :
    privateHistogram order R.histBase written =
      privateHistogram order R.histBase (scratch n priv) := by
  funext l
  exact congrArg Fin.val (fields_histCell _ (order.symm l).isLt heapFit room fits nodes)

/-- Throughout the argument arena the hidden scan leaves the logical child batch intact. -/
theorem fields_arguments (room : ∀ e ∈ es, heap + e.1 * pitch + e.2.length ≤ 2 ^ w)
    (a : ℕ) (before : a < R.histBase) :
    rawScratch written (a : Word w) =
      rawScratch (writePackets R.arguments qs (scratch n priv)) (a : Word w) := by
  rw [← ChildScan.scratch_storePackets]
  apply rawScratch_of_eq
  apply ShrinkCallFrameLive.hidden_below heap pitch es _ room
  have hist : R.histBase ≤ R.cacheBase := (Nat.le_add_right ..).trans R.hist_before
  have stack : R.cacheBase + 38 ≤ heap := Nat.le_add_right ..
  exact (Nat.mod_le ..).trans_lt (before.trans_le (hist.trans (by omega)))

/-- Every cell of any genuine argument packet, including an older pending sibling,
reads exactly as it would immediately after the logical child writes. -/
theorem fields_packet (q : Packet) (realNode : q.node < R.nodes)
    (width : q.bits.length ≤ R.arguments.stride)
    (room : ∀ e ∈ es, heap + e.1 * pitch + e.2.length ≤ 2 ^ w) (i : Fin q.bits.length) :
    rawScratch written ((R.arguments.base q.node + i.val : ℕ) : Word w) =
      rawScratch (writePackets R.arguments qs (scratch n priv))
        ((R.arguments.base q.node + i.val : ℕ) : Word w) :=
  fields_arguments room _ ((Nat.add_lt_add_left (i.isLt.trans_le width) _).trans_le
    (R.node_before realNode))

end ShrinkRole

/-- Both shrinking readers retain the geometry pointer, all twelve geometry fields,
and the cached validator operands in the scratch used by the resident map loop. -/
theorem TreeDecode.VertexFrameData.after_shrink_fields {data : Fin 10 → Word w}
    {offset : Word w} {vals : Static 34 → Word w}
    (frame : VertexFrameData R data offset vals (scratch n priv)) (above : n ≤ G)
    (heapFit : heap ≤ 2 ^ w) (room : ∀ e ∈ es, heap + e.1 * pitch + e.2.length ≤ 2 ^ w)
    (fits : ∀ q ∈ qs, q.Fits R.arguments w n) (nodes : ∀ q ∈ qs, q.node < R.nodes)
    (abovePointer : ∀ q ∈ qs, n < R.arguments.base q.node) :
    VertexFrameData R data offset vals written := by
  have hist : R.histBase ≤ G := Nat.le_add_right ..
  have cache : G ≤ R.cacheBase := R.hist_before
  have stack : R.cacheBase + 38 ≤ heap := Nat.le_add_right ..
  apply frame.transfer
  · exact ShrinkRole.fields_outside _ room fits ((Nat.mod_le ..).trans_lt (by omega))
      (fun q hq ↦ .inl ((Nat.mod_le ..).trans_lt (abovePointer q hq)))
  · intro j
    have hi := j.isLt
    exact ShrinkRole.fields_above_arguments _ (hist.trans (Nat.le_add_right ..)) (by omega)
      heapFit room fits nodes
  · intro j
    have hi : j.offset < 38 := by cases j <;> simp [Static.offset]; omega
    exact ShrinkRole.fields_above_arguments _ ((hist.trans cache).trans (Nat.le_add_right ..))
      ((Nat.add_lt_add_left hi _).trans_le stack) heapFit room fits nodes

end PairSimulation

end VPVNP
end Computability
end OAI
