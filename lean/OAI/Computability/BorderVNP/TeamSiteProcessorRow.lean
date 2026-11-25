import OAI.Computability.BorderVNP.TeamSiteProcessorPrelude
import OAI.Computability.BorderVNP.TeamSiteProcessorBudget
import OAI.Computability.BorderVNP.TeamSiteProcessorSortReplay
import OAI.Computability.BorderVNP.TeamSiteConsistencyExits
import OAI.Computability.BorderVNP.TeamSiteInverse
import OAI.Computability.BorderVNP.TeamSiteEndpointLive
import OAI.Computability.BorderVNP.TeamSiteEndpointHalt

/-! # Exact physical replay of a processor row

A row starts at the raw input. Its fixed prefix has run to the frame decoder, its
initializer has produced the specified word records, and its local sorter sees the
two streams cut from that input. Every RAM replay that reaches a tested outgoing
frame then has a complete physical terminal witness, including legitimate zero
weights and arbitrary proposed successor and sorting messages.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Row

open VPVNP BurstRAM RAMTape RAMSerialization TeamPrivateFragment Layout TeamTapeSorting TeamTapeHandoff
open scoped Classical

variable {Q Γ : Type} {p r k a m g n d e w : ℕ}

/-- The prepared row, together with its actual deterministic execution from the raw input.
The input layout construction supplies these data and proofs for every interior assignment. -/
structure Context (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (n d e w : ℕ) where
  /-- The complete physical processor input, including its own program prefix. -/
  raw : List Bool
  /-- All physical stacks after the deterministic prefix. -/
  base : Stacks (Layout.Port r k (m*g))
  /-- Whether this processor must check the final halt. -/
  last : Bool
  /-- Exact source-stack steps spent before decoding the incoming frame. -/
  preludeTicks : ℕ
  prelude : StackRuns (code P lib) preludeTicks start (StackCompiler.labeledInput input raw) (beginBlock last) base
  /-- Public operands of the fixed RAM template. -/
  pub : Fin k → Word w
  /-- The logical tick allocation for this block. -/
  block : Word w
  /-- The global tick limit for the whole team. -/
  limit : Word w
  /-- The maximum length of a private read. -/
  cap : Word w
  /-- The typed incoming register frame supplied by the predecessor or first literal. -/
  frame : Frame w r
  startup : base ∘ endpoint ∘ Endpoint.startup = TeamLocalClock.Startup.input pub block limit cap frame.bits
  payload : base .payload = []
  /-- The actual assignment to physical sorting and boundary wires. -/
  fields : Fields d e (w+1)
  /-- The real virtual-sorter block owned by the processor. -/
  primary : Word d
  /-- The optional padding block checked by the same physical processor. -/
  secondary : Option (Word d)
  distinct : ∀ u, secondary = some u → u ≠ primary
  /-- Time-zero records emitted from this processor’s own initialized memory segment. -/
  initial : List (WordRecord (w+1))
  hw₂ : 2 ≤ w+1
  capacity : 2^d*2^e < 2^(w+1)
  hd : d ≤ n
  hw : w+1 ≤ n
  hB : 2^e ≤ n
  hL : TeamTapeInputRoute.comparisonSize d e (w+1) ≤ n
  work : Work.Ready hw₂ (2^e) initial (base ∘ site)
  space : initial.length+2*block.val ≤ 4*(2^e)
  fits : p ≤ 2^w
  route : RouteReady n fields primary secondary base

variable {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
variable (X : Context P lib n d e w)

/-- Word records for the real sorting lane of this row. -/
def Context.slots (es : List (TeamRAM.Event w)) :=
  X.initial ++ chunkSlots (X.frame.elapsed.val+1) es

/-- Virtual padding owners have empty rows. Only the primary lane consumes the records
of this RAM block. -/
def Context.rows (es : List (TeamRAM.Event w)) (v : Word d) : List (WordRecord (w+1)) :=
  if v = X.primary then X.slots es else []

@[simp] theorem Context.rows_primary (es : List (TeamRAM.Event w)) : X.rows es X.primary = X.slots es := by
  simp [Context.rows]

/-- All physical comparisons and boundary checks on the owner's occupied lanes. -/
def Context.sorted (es : List (TeamRAM.Event w)) : Prop :=
  TeamTapeInputRoute.Verify.ownerValid X.hw₂ X.capacity X.fields (rowInput e (X.rows es)) X.primary X.secondary

/-- Required final halt, or exact equality of all proposed bits of the successor. -/
def Context.guard (output : Frame w r) : Bool :=
  if X.last then output.halted else decide (output.bits=X.base .outgoing)

/-- A concrete whole-processor time envelope using this prefix's actual elapsed time. -/
def Context.cost (body : ℕ) (es : List (TeamRAM.Event w)) : ℕ :=
  X.preludeTicks + Budget.endpoint r w body + Budget.close w (2^e) (X.slots es).length + Budget.sort n d e w

/-- A physically checked terminal carries the original sorter accept bit even when
the coefficient machine assigns that path weight zero. -/
def Checked (q : Label P Q m g) (sg : Option Bool) : Prop :=
  ∃ z, q = .sort sg (some z) ∧ TeamTapeInputRoute.Verify.processor.body.code z = .halt true

/-- Complete replay from the sole input stack, with its physical and unmasked terminal
outcomes. The recorded finite bit list is exactly the consumed choice prefix. -/
def Context.Model (bits : List Bool) (sg : Option Bool) (pass : Prop) (clock : ℕ) : Prop :=
  ∃ t < clock, ∃ q out b, StackRuns (replay (code P lib)) t (start,bits)
    (StackCompiler.labeledInput input X.raw) (q,[]) out ∧ code P lib q = .halt b ∧
    (b = true ↔ pass ∧ sg.isSome = true) ∧
    (∀ z, Checked q z ↔ pass ∧ z = sg) ∧ (b = true → negative q = sg.getD false)

/-- A full endpoint replay is extended through the real physical record close and sorter.
Incorrect successor bits reject before sorting. Valid zero-weight endpoints still undergo
the complete memory validation and retain its verdict in their terminal label. -/
theorem Context.finish (es : List (TeamRAM.Event w)) (sg : Option Bool) (ok : Bool) (body : ℕ)
    {ticks : ℕ} {out : Stacks (Endpoint.Port r k (m*g))}
    (bound : ticks ≤ TeamLocalClock.Startup.budget r w+1+body+(7*r+45)*(w+1))
    (ep : StackRuns (replay (Endpoint.code P lib)) ticks (.startup X.last (TeamLocalClock.Startup.entry p r),chunkBits es)
      (X.base ∘ endpoint) (Endpoint.finishLabel sg ok,[]) out)
    (buffered : RecordBuffer.Holds X.hw₂ (2^e) (X.slots es)
      (out ∘ Endpoint.Port.site ∘ probe ∘ TeamProbeEmit.Port.buffer)) :
    X.Model (chunkBits es) sg (ok=true ∧ X.sorted es) (X.cost body es) := by
  let full := installStacks endpoint X.base out
  have pre := replay_segment X.prelude (chunkBits es)
  have mid := endpoint_replay P lib ep X.base rfl
  have whole := pre.trans mid
  have budget : X.preludeTicks + ticks + 1 ≤ X.preludeTicks + Budget.endpoint r w body := by
    unfold Budget.endpoint; omega
  cases ok with
  | false =>
    refine ⟨_, ?_, _,_,false,whole,rfl,by simp,?_,by simp⟩
    · have hpos : 0 < Budget.sort n d e w := by unfold Budget.sort; omega
      unfold Context.cost; omega
    · intro z; simp [Checked,Endpoint.finishLabel]
  | true =>
    have eq (i : RecordBuffer.Port) :
        full (buffer i) = out (.site (probe (.buffer i))) := installStacks_at endpoint_injective X.base out (.site (probe (.buffer i)))
    have hb : RecordBuffer.Holds X.hw₂ (2^e) (X.rows es X.primary) (full ∘ buffer) := by
      rw [X.rows_primary]
      have hv : full ∘ buffer = out ∘ Endpoint.Port.site ∘ probe ∘ TeamProbeEmit.Port.buffer := funext eq
      rw [hv]; exact buffered
    obtain ⟨t,ht,q,b,srt,finishRun,sortRow,check,row⟩ := closeSort_replay P lib sg n X.hw₂ X.capacity
      X.fields X.primary X.secondary (X.rows es) (fun u h => by simp [Context.rows,X.distinct u h])
      full (X.route.installEndpoint _) X.hd X.hw X.hB X.hL hb (Budget.sort n d e w) (by rfl)
    have fin := (whole.trans (endpoint_done P lib sg full [])).trans (finishRun [])
    refine ⟨_, ?_, _,_,_,fin,row,?_,?_,?_,⟩
    · change t < Budget.sort n d e w + Budget.close w (2^e) (X.rows es X.primary).length at ht
      rw [X.rows_primary] at ht
      unfold Context.cost; omega
    · simp only [Bool.and_eq_true_iff,true_and,Context.sorted]
      exact and_congr_left (fun _ => check)
    · intro z
      constructor
      · rintro ⟨z',e,h⟩
        have h' := Label.sort.inj e
        obtain ⟨rfl,he⟩ := h'
        obtain rfl := Option.some.inj he
        exact ⟨⟨rfl,check.mp (StackOp.halt.inj (sortRow.symm.trans h))⟩,rfl⟩
      · rintro ⟨⟨_,pass⟩,rfl⟩
        exact ⟨q,rfl,check.mpr pass ▸ sortRow⟩
    · intro _; rfl

end TeamSite.Processor.Row

end BorderVNP
end Computability
end OAI
