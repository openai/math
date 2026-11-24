import OAI.Computability.VPVNP.PairVertexLevelLocator
import OAI.Computability.VPVNP.CompressorLevelOrder
import OAI.Computability.VPVNP.CompressorDirectoryBudget

/-!
# The level locator on the selected compression branch

Each block has one shrinking pass at each index, followed by its refresh.
The locator returns the ordinal of the pass producing the popped row. Its
remainder within the block selects the degree of the actual kernel reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevel

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression LocalHistory CursorNetwork
open TraversalRoles TraversalRows TraversalControllerInputs NodeArguments.ChildScan
open scoped Fin.CommRing

private theorem repeated_range_get (s T i : ℕ)
    (h : i < (List.replicate T (List.range s)).flatten.length) :
    (List.replicate T (List.range s)).flatten[i] = i % s := by
  induction T generalizing i with
  | zero => simp at h
  | succ T ih =>
    simp only [List.replicate_succ, List.flatten_cons] at h ⊢
    by_cases hi : i < s
    · rw [List.getElem_append_left (by simpa using hi), List.getElem_range, Nat.mod_eq_of_lt hi]
    · have le : s ≤ i := Nat.le_of_not_gt hi
      rw [List.getElem_append_right (by simpa using le), ih, List.length_range,
        ← Nat.mod_eq_sub_mod le]

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
variable {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)
local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z

/-- Every block contributes exactly its shrinking passes and one refresh. -/
theorem selected_pass_count : (passes).length = T * (S.steps + 1) := by
  simpa [List.length_flatten] using congrArg List.length (executeLevels_order B f hf T hT X z)

/-- Including the cursor input, there is precisely one more traversal level than passes. -/
theorem selected_level_count : (tags).length = T * (S.steps + 1) + 1 := by
  simp [TraversalRoles.selected, selected_pass_count B f hf T hT X z]

/-- The block-relative ordinal is the one on the producing pass of the
mathematical execution, for every occurrence on every choice branch. -/
theorem selected_pass_ordinal (i : Fin (passes).length) :
    passes[i].origin.ordinal = i.val % (S.steps + 1) := by
  have order := executeLevels_order B f hf T hT X z
  have e := List.getElem_of_eq order (i := i.val) (by simp)
  rw [List.getElem_map] at e
  exact e.trans (repeated_range_get _ _ _ _)

private theorem exponent_of_ordinal {a g b n : ℕ} {Y : State a g} {p : StatePass R Y b n}
    (o : PassOrigin B f hf p) : a = S.exponentAt o.ordinal := by
  cases o with
  | shrink i h X => exact (S.exponentAt_castSucc i).symm
  | refresh X =>
    simp [PassOrigin.ordinal, BlockSchedule.exponentAt, BlockSchedule.portExponent, Fin.last]

private theorem role_of_ordinal {a g b n : ℕ} {Y : State a g} {p : StatePass R Y b n}
    (o : PassOrigin B f hf p) :
    TraversalRoles.ofOrigin o = if o.ordinal = S.steps then .refresh else .shrink := by
  cases o with
  | shrink i h X => simp [TraversalRoles.ofOrigin, PassOrigin.ordinal, i.isLt.ne]
  | refresh X => simp [TraversalRoles.ofOrigin, PassOrigin.ordinal]

/-- The physical old-level ordinal selects exactly the input exponent used
by the old incidence slots of the true placement-fiber reader. -/
theorem selected_inputExponent (i : Fin (passes).length) :
    passes[i].inputExponent = S.exponentAt (i.val % (S.steps + 1)) := by
  rw [← selected_pass_ordinal B f hf T hT X z i]
  exact exponent_of_ordinal B f hf passes[i].origin

/-- The unique refresh occupies the last ordinal in the block. -/
theorem selected_pass_role (i : Fin (passes).length) :
    tagLevel B f hf passes[i] = if i.val % (S.steps + 1) = S.steps then .refresh else .shrink := by
  rw [← selected_pass_ordinal B f hf T hT X z i]
  exact role_of_ordinal B f hf passes[i].origin

variable {w : ℕ}

/-- Upper bounds for a locator call on any actual output level of this branch. -/
theorem selected_trace_bounds (pub : Fin 11 → Word w) (m : Memory w)
    (i : Fin (passes).length) :
    let es := trace pub m (i.val + 1) ((passes).length - (i.val + 1))
    es.length ≤ 32 + 6 * (T * (S.steps + 1)) ∧ countProbes es ≤ 5 + T * (S.steps + 1) := by
  intro es
  obtain ⟨length, probes, _⟩ := trace_cost pub m (i.val + 1) ((passes).length - (i.val + 1))
  have h := (Nat.sub_le (passes).length (i.val + 1)).trans_eq (selected_pass_count B f hf T hT X z)
  exact ⟨length.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_left 6 h) 32),
    probes.trans_le (Nat.add_le_add_left h 5)⟩

open private blocks_le_log from OAI.Computability.VPVNP.CompressorDirectoryBudget

/-- With the paper's genuine block count, both costs are linear in the
binary logarithm of the input length. The constants depend only on the schedule. -/
theorem selected_trace_log (u : PairExponents B.growthConstant) {n : ℕ} (hn : 1 ≤ n)
    (ht : T = blockCount (u.θ : ℝ) n) (pub : Fin 11 → Word w) (m : Memory w)
    (i : Fin (passes).length) :
    let es := trace pub m (i.val + 1) ((passes).length - (i.val + 1))
    es.length ≤ (32 + 6 * (S.steps + 1)) * (n.log2 + 1) ∧
    countProbes es ≤ (5 + (S.steps + 1)) * (n.log2 + 1) := by
  intro es
  have hblocks : T ≤ n.log2 + 1 := ht.trans_le (blocks_le_log B u hn)
  have h := Nat.mul_le_mul_right (S.steps + 1) hblocks
  obtain ⟨len, probes⟩ := selected_trace_bounds B f hf T hT X z pub m i
  constructor
  · calc
      es.length ≤ _ := len
      _ ≤ 32 * (n.log2 + 1) + 6 * ((n.log2 + 1) * (S.steps + 1)) :=
        Nat.add_le_add (Nat.le_mul_of_pos_right 32 (Nat.succ_pos _)) (Nat.mul_le_mul_left 6 h)
      _ = _ := by ring
  · calc
      countProbes es ≤ _ := probes
      _ ≤ 5 * (n.log2 + 1) + (n.log2 + 1) * (S.steps + 1) :=
        Nat.add_le_add (Nat.le_mul_of_pos_right 5 (Nat.succ_pos _)) h
      _ = _ := by ring

set_option maxHeartbeats 800000 in
-- Instantiating the locator identifies the selected level in two dependent row lists.
/-- Execute the linked locator on a row of an actual selected term. The stage
register supplies the native remainder for the kernel, the owner is the row's
packed site ordinal, and the trace uses the true number of later levels. -/
theorem selected_run {p r H first pitch offset base : ℕ} {raw m : Memory w}
    (ds : (j : Fin (passes).length) → LevelDirectory passes[j] raw base)
    (M : Machine w p r 11) (loc : Fin 35 → Fin p) (dfs : Fin 9 ↪ Fin r)
    (saved : VertexImage.Saved ↪ Fin r) (reg : Fin 14 ↪ Fin r) (done : Fin p)
    (rows : ∀ j, M.code (loc j) = (segment.row loc dfs saved reg done j).resize w)
    (d : Resident M.publicData m H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers passes ds))
    (i : Fin (passes).length) (id : Fin passes[i].outputSites)
    (c : Config w p r) (hc : c.pc = loc segment.entry)
    (node : (c.reg (dfs 7)).val = address B.recordLimit
      (layerBase B.recordLimit base tags (i.val + 1)) id.val)
    (fit : layerBase B.recordLimit base tags ((passes).length + 1) < 2 ^ w) :
    ∃ out, Prefix M m c out [] (trace M.publicData m (i.val + 1) ((passes).length - (i.val + 1))) ∧
      out.pc = done ∧ Located M.publicData m reg (c.reg (dfs 7)) i.val (id.val : Word w) out ∧
      (BinaryOp.mod.eval (out.reg (reg 13)) ((S.steps + 1 : ℕ) : Word w)).val =
        passes[i].origin.ordinal ∧
      Frame reg c out := by
  let old : TaggedLayer := ⟨leafLayer (siteOrder X), .cursor⟩
  let fibers := levelFibers passes ds
  have length : fibers.length = (passes).length := by simp [fibers, levelFibers]
  have layers : old :: fibers.map Prod.fst = tags := by
    rw [show fibers.map Prod.fst = _ from levelFibers_tags passes ds]
    rfl
  let j : Fin (old :: fibers.map Prod.fst).length := ⟨i.val + 1, by simp [length]⟩
  have count : (old :: fibers.map Prod.fst)[j].layer.count = passes[i].outputSites := by
    simp [j, fibers, levelFibers_tags, levelLayer_count]
  let id' : Fin (old :: fibers.map Prod.fst)[j].layer.count :=
    ⟨id.val, by rw [count]; exact id.isLt⟩
  have address' : (c.reg (dfs 7)).val = address B.recordLimit
      (layerBase B.recordLimit base (old :: fibers.map Prod.fst) j.val) id'.val := by
    simpa only [layers, j, id'] using node
  have fit' :
      layerBase B.recordLimit base (old :: fibers.map Prod.fst) (fibers.length + 1) < 2 ^ w := by
    rwa [layers, length]
  obtain ⟨out, runPrefix, atDone, located, frame⟩ :=
    run M loc dfs saved reg done rows d j i.val rfl id' c hc address' fit'
  change Prefix M m c out []
    (trace M.publicData m (i.val + 1) (fibers.length - (i.val + 1))) at runPrefix
  rw [length] at runPrefix
  refine ⟨out, runPrefix, atDone, located, ?_, frame⟩
  have levels : (m (H + 1)).val = (passes).length + 1 := d.levels.trans (congrArg (· + 1) length)
  have total : (passes).length < 2 ^ w := by have := (m (H + 1)).isLt; omega
  have ip : i.val < 2 ^ w := i.isLt.trans total
  have count_eq := selected_pass_count B f hf T hT X z
  have positive : 0 < T := by
    by_contra! h
    have zero : T * (S.steps + 1) = 0 := by rw [Nat.eq_zero_of_le_zero h, Nat.zero_mul]
    exact Nat.not_lt_zero _ (i.isLt.trans_eq (count_eq.trans zero))
  have periodFit : S.steps + 1 < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ positive).trans_lt (count_eq ▸ total)
  rw [located.stage, selected_pass_ordinal B f hf T hT X z i]
  change (((i.val % 2 ^ w) % ((S.steps + 1) % 2 ^ w)) % 2 ^ w) = _
  rw [Nat.mod_eq_of_lt ip, Nat.mod_eq_of_lt periodFit,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ (Nat.succ_pos _)).trans periodFit)]

end PairSimulation.VertexLevel

end VPVNP
end Computability
end OAI
