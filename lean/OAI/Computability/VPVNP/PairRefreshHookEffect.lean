import OAI.Computability.VPVNP.PairRefreshHookSite
import OAI.Computability.VPVNP.PairRefreshTraversalFrames
import OAI.Computability.VPVNP.PairRefreshTraversalHistogram
import OAI.Computability.VPVNP.PairRefreshTraversalValue
import OAI.Computability.VPVNP.PairVertexFrameData

/-!
# Scratch effects of a refresh on the pending DFS frontier

The unique child write fills one argument slot below the histogram. The
selected map then increments the label words and uses a private workspace
between the vertex geometry and the cache. All pending arguments, geometry
fields and cached operands can still be read at their original addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM PrivateRAM Compression CompressorRecords CompressorRecords.PortRefresh
open NodeArguments TreeDecode VertexImage DFS LeafSourceLoad Compression.DegreeRefresh Compression.Refresh
open CompressorRecords.RefreshMapOperands MotifConversion
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {w n hist t : ℕ}
variable (R : Site B n hist w) (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ)
  (order : B.Entry ≃ Fin hist) (pub : Fin 11 → BurstRAM.Word w) (m : Memory w)
  (old : R.state.network.Half R.olderSite) (new : R.nextState.network.Half R.newerSite)
local notation "child" => packet R.state R.olderSite R.oldNode old
local notation "base" => LeafArena.Regions.histBase R.regions
local notation "directory" => LeafArena.Regions.histBase R.regions + hist + 12 + 2*n
local notation "upper" => TraversalPlan.canonicalUpper B ties stride order R.state R.choice R.port
  R.degree n R.rowEnd R.oldNode R.parent R.room old new
local notation "names" => TraversalPlan.emitted B order R.state R.choice R.port old new

variable {s out : Scratch w n} {es : List (Event w)}
variable (result : R.action ties stride order pub m old new
  ((RefreshHook.packet R.state R.olderSite R.oldNode old).write R.arena s) = some (es,out))

private theorem option_fields {α β : Type*} (condition : Bool) (e : α) (v : β) (es : α) (out : β)
    (result : (if condition then some (e,v) else none) = some (es,out)) :
    condition = true ∧ out = v := by
  cases condition <;> simp_all

set_option maxHeartbeats 1800000 in
-- The concrete refresh action has dependent slot and workspace indices.
include result in
/-- A successful parser selects the actual map update applied after its unique
old-half packet has been written. -/
theorem action_scratch : (names).isSome = true ∧ out = upper ((child).write R.arena s) := by
  exact option_fields (names).isSome _ (upper ((child).write R.arena s)) es out result

private theorem hist_room : base+hist ≤ 2^w :=
  R.regions.hist_before.trans R.room.capacity.room.le

private theorem wordBelow (i : Fin hist) :
    (((base+i.val : ℕ) : BurstRAM.Word w)).val = base+i.val :=
  Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le (hist_room R))

include result in
/-- The map preserves each raw scratch word in the indicated regions, excluding
its histogram interval. This includes arbitrary old values in unused cells. -/
theorem action_frame (a : BurstRAM.Word w)
    (far : a.val < directory ∨ R.regions.cacheBase ≤ a.val)
    (apart : a.val < base ∨ base+hist ≤ a.val) :
    rawScratch out a = rawScratch ((child).write R.arena s) a := by
  rw [(R.action_scratch ties stride order pub m old new result).2]
  by_cases ha : n ≤ a.val
  · simp only [rawScratch,dite_eq_left ha]
    apply TraversalPlan.upper_frame B ties stride order R.state R.choice R.port R.degree n
      R.rowEnd R.oldNode R.parent R.room old new _ _ ha far
    intro i eqn
    have value := (congrArg Fin.val eqn).trans (wordBelow R i)
    have ix := i.isLt
    omega
  · simp only [rawScratch,dite_eq_right ha]

private theorem child_outside (a : BurstRAM.Word w)
    (apart : a.val < R.arena.base R.oldNode ∨ R.arena.base R.oldNode + (child).bits.length ≤ a.val) :
    rawScratch ((child).write R.arena s) a = rawScratch s a := by
  by_cases ha : n ≤ a.val
  · simp only [rawScratch,dite_eq_left ha,Packet.write,scratch]
    exact (PrivateFields.storeBits_outside _ _ (rawScratch s) a (R.oldFit old).2.2 apart).trans
      (dite_eq_left ha)
  · simp only [rawScratch,dite_eq_right ha]

private theorem childEnd : R.arena.base R.oldNode + (child).bits.length ≤ base :=
  (Nat.add_le_add_left (R.oldFit old).2.1 _).trans (R.regions.node_before R.room.childBound)

include result in
/-- Any fitted pending node, including the newly written child, retains its
packet words after the map has run. -/
theorem action_packet (q : Packet) (node : q.node < R.rowEnd) (fit : q.Fits R.arena w n)
    (i : Fin q.bits.length) :
    rawScratch out ((R.arena.base q.node+i.val : ℕ) : BurstRAM.Word w) =
      rawScratch ((child).write R.arena s) ((R.arena.base q.node+i.val : ℕ) : BurstRAM.Word w) := by
  have ix := (Nat.add_lt_add_left (i.isLt.trans_le fit.2.1) _).trans_le (R.regions.node_before node)
  have room : R.arena.base q.node+i.val < 2^w := (Nat.add_lt_add_left i.isLt _).trans_le fit.2.2
  have bound : (((R.arena.base q.node+i.val : ℕ) : BurstRAM.Word w)).val < base :=
    (Nat.mod_eq_of_lt room).trans_lt ix
  apply R.action_frame ties stride order pub m old new result _ (Or.inl ?_) (Or.inl bound)
  omega

include result in
/-- The ten record words, the role and histogram pointers, and all 38 cached
operands survive the child write and the map. -/
theorem action_vertexFrame {data : Fin 10 → BurstRAM.Word w} {offset : BurstRAM.Word w} {vals : Static 34 → BurstRAM.Word w}
    (before : VertexFrameData R.regions data offset vals s) (positive : 0 < R.oldNode)
    (cacheFit : R.regions.cacheBase+38 ≤ 2^w) :
    VertexFrameData R.regions data offset vals out := by
  have lowChild : n < R.arena.base R.oldNode := by
    change n < n + R.oldNode*(2*R.degree*n+1)
    exact Nat.lt_add_of_pos_right (Nat.mul_pos positive (Nat.succ_pos _))
  have endBefore := childEnd R old
  have cache : base+hist ≤ R.regions.cacheBase := R.regions.hist_before
  have frameBase : NativeFrame.frameBase R.regions = base+hist := rfl
  have geomRoom : base+hist+12 ≤ R.regions.cacheBase := by
    change base+hist+12 ≤ base+hist+n^5
    exact Nat.add_le_add_left ((by decide : 12 ≤ 5^5).trans (Nat.pow_le_pow_left R.room.five 5)) _
  apply before.transfer
  · have val : (n : BurstRAM.Word w).val = n := Nat.mod_eq_of_lt before.resident.endFit
    apply (R.action_frame ties stride order pub m old new result _ (Or.inl (by rw [val]; omega))
      (Or.inl (by rw [val]; omega))).trans
    exact child_outside R old _ (Or.inl (val.trans_lt lowChild))
  · intro i
    have ix := i.isLt
    have fit : NativeFrame.frameBase R.regions+i.val < 2^w := by rw [frameBase]; omega
    have val : (((NativeFrame.frameBase R.regions+i.val : ℕ) : BurstRAM.Word w)).val = base+hist+i.val :=
      (Nat.mod_eq_of_lt fit).trans (congrArg (·+i.val) frameBase)
    apply (R.action_frame ties stride order pub m old new result _ (Or.inl (by rw [val]; omega))
      (Or.inr (by rw [val]; omega))).trans
    exact child_outside R old _ (Or.inr (by rw [val]; omega))
  · intro j
    have hj : j.offset < 38 := by cases j <;> simp [Static.offset]; omega
    have fit : R.regions.cacheBase + j.offset < 2^w := by omega
    have val : (((R.regions.cacheBase+j.offset : ℕ) : BurstRAM.Word w)).val = R.regions.cacheBase+j.offset :=
      Nat.mod_eq_of_lt fit
    apply (R.action_frame ties stride order pub m old new result _ (Or.inr (by rw [val]; omega))
      (Or.inr (by rw [val]; omega))).trans
    exact child_outside R old _ (Or.inr (by rw [val]; omega))

private theorem index_length {u : ℕ} {α β : Type*} (indices : Option (Fin u → α)) (toLabel : α → β) :
    (((indices.map List.ofFn).map (List.map toLabel)).getD []).length ≤ u := by
  cases indices <;> simp

/-- A refresh emits at most one label for each allocated copy. This bound
applies to every independent old half and every parent packet. -/
theorem action_count_le (i : Fin hist) : ((names).getD []).count i ≤ n := by
  let placed := TraversalPlan.splitPlaced R.state R.port (TraversalPlan.placedHalf R.state R.port old)
  have half := TraversalPlan.splitPlaced_child R.state R.port (TraversalPlan.placedHalf R.state R.port old)
  have eqn := TraversalPlan.emitted_eq_indices B order R.state R.choice R.port old new placed half
  refine (List.count_le_length ..).trans ?_
  rw [eqn]
  exact (index_length ..).trans R.room.copyBound

include result in
/-- Word-level readback for the complete action. The preceding child store
is disjoint from each histogram word, including words previously incremented. -/
theorem action_histogram (i : Fin hist) :
    rawScratch out ((base+i.val : ℕ) : BurstRAM.Word w) =
      rawScratch s ((base+i.val : ℕ) : BurstRAM.Word w) + (((names).getD []).count i : BurstRAM.Word w) := by
  let a : BurstRAM.Word w := ((base+i.val : ℕ) : BurstRAM.Word w)
  have va : a.val = base+i.val := wordBelow R i
  have low : n ≤ base := Nat.le_add_right ..
  have hi : n ≤ a.val := va ▸ low.trans (Nat.le_add_right _ _)
  have ⟨good,next⟩ := R.action_scratch ties stride order pub m old new result
  have keep := child_outside (s := s) R old a (Or.inr ((childEnd R old).trans ((Nat.le_add_right _ _).trans_eq va.symm)))
  have update := TraversalPlan.upper_histogram B ties stride order R.state R.choice R.port R.degree n
    R.rowEnd R.oldNode R.parent R.room old new ((child).write R.arena s) good i hi
  rw [next]
  change rawScratch (upper ((child).write R.arena s)) a = rawScratch s a + _
  rw [← keep]
  simp only [rawScratch,dite_eq_left hi]
  exact update

include result in
/-- The accepted action advances the pending forest by exactly one visit and
increments every natural label exponent by its true emitted multiplicity. -/
theorem action_budgeted {data : Fin 10 → BurstRAM.Word w} {offset : BurstRAM.Word w} {vals : Static 34 → BurstRAM.Word w}
    (format : Packet → Prop) (desc : ℕ → List ℕ) (nodeCap limit : ℕ) (head : Packet) (pending : List Packet)
    (before : Budgeted R.arena format (VertexFrameData R.regions data offset vals) desc
      (privateHistogram order.symm base) nodeCap limit (head::pending) s)
    (shape : desc head.node = subtreeAddresses desc child) (typed : format child)
    (nodeBound : ∀ q, format q → q.node < R.rowEnd) (positive : 0 < R.oldNode)
    (cacheFit : R.regions.cacheBase+38 ≤ 2^w) (limitFit : limit < 2^w) (capFit : n ≤ nodeCap) :
    Budgeted R.arena format (VertexFrameData R.regions data offset vals) desc
      (privateHistogram order.symm base) nodeCap limit (child::pending) out ∧
      ∀ label, privateHistogram order.symm base out label = privateHistogram order.symm base s label +
        ((names).getD []).count (order label) := by
  have hit (label) : privateHistogram order.symm base out label =
      privateHistogram order.symm base s label + ((names).getD []).count (order label) := by
    let i := order label
    have small := (R.action_count_le order old new i).trans capFit
    have nat := before.word_add limitFit label small
    have word := R.action_histogram ties stride order pub m old new result i
    change (rawScratch out ((base+i.val : ℕ) : BurstRAM.Word w)).val =
      (rawScratch s ((base+i.val : ℕ) : BurstRAM.Word w)).val + _
    rw [word]
    simpa only [privateHistogram,Equiv.symm_symm,Fin.cast_val_eq_self] using nat
  refine ⟨before.push (children := [child]) (by simpa using shape)
    (R.action_vertexFrame ties stride order pub m old new result before.frontier.frame positive cacheFit)
    ?_ ?_ (fun label => (hit label).le.trans (Nat.add_le_add_left
      ((R.action_count_le order old new (order label)).trans capFit) _)),hit⟩
  · intro q hq
    obtain rfl := List.mem_singleton.mp hq
    exact ⟨typed,R.oldFit old⟩
  · intro q hq i
    have facts : format q ∧ q.Fits R.arena w n := by
      rcases List.mem_append.mp hq with childEq | sibling
      · obtain rfl := List.mem_singleton.mp childEq
        exact ⟨typed,R.oldFit old⟩
      · have ready := before.frontier.prepared.2 q (List.mem_cons_of_mem _ sibling)
        exact ⟨ready.1,ready.2.1⟩
    exact R.action_packet ties stride order pub m old new result q (nodeBound q facts.1) facts.2 i

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
