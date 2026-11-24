import OAI.Computability.VPVNP.LiveNativePairContinuation
import OAI.Computability.VPVNP.LiveProgramCaps
import OAI.Computability.VPVNP.LiveDeterministicReachable
import OAI.Computability.VPVNP.PairSimulationSelectorReindex

/-!
# Relocating the compressed pair's complete native paths into the live table

The pair instruction table runs on eleven public words. Relocation preserves
every supplied tape, report and memory write. A common prefix and the
branch-dependent terminal calls thus enter the outer linker on their original
chronological list. Only the dispatch and successor-tag events are appended
when charging the outer reports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.CompressedPaths

open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveExponent PairSimulation.LocalHistory

variable (G : Group)

/-- Eleven words supplied to the pair stage, obtained by selecting its operands from the live
group’s geometry and literal prefix. -/
abbrev publicWords := Pieces.word G.g G.lit ∘ StageOperands.pair G.constants
/-- Unrelocated burst RAM program of the group’s pair table instantiated at the group word
width and pair operands. -/
abbrev native := (G.pair.table.instantiate G.w (publicWords G)).program
/-- Per-call instruction allowance assigned to the pair stage by the live group’s clock. -/
abbrev fuel := G.clockAt Stage.pair
/-- Lists of call tapes that take the native pair from cursor zero and the specified memory to
an accepting halt within the per-call fuel. -/
abbrev Raw (m : Memory G.w) := ActualPaths (native G) (fuel G) 0 m (fun _ => True)

variable {G} {m : Memory G.w}
/-- Chronological reports returned by running the call tapes of an accepting native pair path. -/
noncomputable def reports (p : Raw G m) : List (Report G.w) := p.property.choose

theorem rawRun (p : Raw G m) :
    runSegment (native G) (fuel G) (some 0) m p.val = some (reports p) := p.property.choose_spec.1

/-- The memory and state of any actual continuing prefix, including one
which may later reject. -/
inductive Reachable (G : Group) (initial : Memory G.w) : Word G.w → Memory G.w → Prop
  | start : Reachable G initial 0 initial
  | more {st mem bits r st'} : Reachable G initial st mem →
      execute (native G) (fuel G) ((native G).start st) mem bits = some r → r.result = some st' →
      Reachable G initial st' (after mem r.events)

/-- Every continuing call in this physical component preserves the outer
tag, even when the supplied tape has no accepting extension. -/
def PreservesTag (G : Group) (initial : Memory G.w) : Prop :=
  ∀ {st mem bits r st'}, Reachable G initial st mem →
    execute (native G) (fuel G) ((native G).start st) mem bits = some r → r.result = some st' →
    after mem r.events G.addr.val = mem G.addr.val

/-- The generic address-preservation proof on the original native table
supplies the tag invariant required after relocation. -/
theorem preservesTag_of_protectsAddress (G : Group) (m : Memory G.w)
    (h : ProtectsAddress (native G) (fuel G) 0 m G.addr.val) : PreservesTag G m := by
  have embed {s u} (reached : Reachable G m s u) : Reached (native G) (fuel G) 0 m s u := by
    induction reached with
    | start => exact .start
    | more _ call cont ih => exact .more ih call cont
  intro st mem bits r st' reached call result
  exact h (embed reached) call result

private theorem relocated {st : Option (Word G.w)} {mem : Memory G.w} {bs : List (List Bool)} :
    runSegment (sourceProgram G.T G.pub Stage.pair) (fuel G) st mem bs =
      runSegment (native G) (fuel G) st mem bs :=
  component_segment G Stage.pair (fuel G) st mem bs

private theorem frame (preserves : PreservesTag G m) :
    TagFrame G.T G.pub G.addr Stage.pair (fuel G) (Reachable G m) := by
  intro st mem bits r st' reached tag run cont
  have localRun : execute (native G) (fuel G) ((native G).start st) mem bits = some r :=
    (Pieces.component_eq G.components G.g G.lit Stage.pair (fuel G) st mem bits).symm.trans run
  exact ⟨reached.more localRun cont,(preserves reached localRun cont).trans tag⟩

/-- Room for the final transfer follows from a private-instruction bound on
the actual, unrelocated pair reports. All earlier pair calls return directly. -/
theorem room_of_work {r : Report G.w} (hr : r.events.length + 4 ≤ fuel G) :
    room G.nextStage G.addr Stage.pair (fuel G) r := by
  unfold room exitReport
  have nextPair : G.nextStage Stage.pair = some Stage.exponents := rfl
  rw [nextPair]
  cases r.result <;> simp only [transferEvents,List.length_append,List.length_cons,List.length_nil] <;> omega

/-- Equality on the entire tape list gives a bijection between the original
pair completion and its ordinary stage in the outer table. -/
noncomputable def ordinary (fits : ∀ p : Raw G m, ∀ r ∈ reports p, room G.nextStage G.addr Stage.pair (fuel G) r) :
    Raw G m ≃ G.StagePaths Stage.pair m where
  toFun p := ⟨p.val,reports p,relocated.trans (rawRun p),p.property.choose_spec.2.1,fits p⟩
  invFun p := ⟨p.val,ordinaryReports p,relocated.symm.trans (ordinaryRun p),p.property.choose_spec.2.1,trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Classify the physical stage by the range of the descriptor/arc/DFS tape
emission and its decoding equivalence to the *same* monomial witness. -/
noncomputable def indexed {X : Type} {enc : TraceEncoding X} (R : SelectorReindex enc)
    (paths : Set.range R.emit ≃ Raw G m) (tag : G.tagged Stage.pair m) (preserves : PreservesTag G m)
    (fits : ∀ p : Raw G m, ∀ r ∈ reports p, room G.nextStage G.addr Stage.pair (fuel G) r) :
    Indexed G Stage.pair m X :=
  ⟨⟨Reachable G m,frame preserves,.start,tag⟩,R.decode.symm.trans (paths.trans (ordinary fits))⟩

variable {X : Type} {enc : TraceEncoding X} (R : SelectorReindex enc) (paths : Set.range R.emit ≃ Raw G m)
    (tag : G.tagged Stage.pair m) (preserves : PreservesTag G m)
    (fits : ∀ p : Raw G m, ∀ r ∈ reports p, room G.nextStage G.addr Stage.pair (fuel G) r)

/-- The chronological descriptor prefix, arc bits and independent site
tapes all survive relocation. -/
theorem indexed_tapes (p : Set.range R.emit) :
    ((indexed R paths tag preserves fits).traces (R.decode p)).val = (paths p).val := by
  simp only [indexed,Equiv.trans_apply,Equiv.symm_apply_apply,ordinary,Equiv.coe_fn_mk]

theorem indexed_reports (p : Set.range R.emit) :
    ordinaryReports ((indexed R paths tag preserves fits).traces (R.decode p)) = reports (paths p) := by
  apply Option.some.inj
  have h := ordinaryRun ((indexed R paths tag preserves fits).traces (R.decode p))
  rw [relocated,indexed_tapes] at h
  exact h.symm.trans (rawRun _)

theorem indexed_memory (p : Set.range R.emit) :
    (indexed R paths tag preserves fits).memory (R.decode p) =
      transferMemory G.addr (some Stage.exponents) (after m (eventLog (reports (paths p)))) := by
  rw [Indexed.memory,indexed_reports]
  rfl

theorem indexed_logs (p : Set.range R.emit) :
    (indexed R paths tag preserves fits).logs (R.decode p) =
      (reports (paths p)).map (linkedReport G.nextStage G.addr Stage.pair) := by
  rw [Indexed.logs,indexed_reports]

/-- Charge the outer dispatch and control transfer to the slack left by the
native pair simulator. The resulting reports fit the exact pair allowance
in the first-half chronology. -/
theorem indexed_budget (p : Set.range R.emit) (S H : ℕ) (hH : 4 ≤ H)
    (total : 4*RAMBuckets.cost Report.probes (reports (paths p)) ≤ S*H)
    (each : ∀ r ∈ reports (paths p), 3+r.probes ≤ H) :
    let rs := (indexed R paths tag preserves fits).logs (R.decode p)
    RAMBuckets.cost Report.probes rs ≤ S*(H-1) ∧ ∀ r ∈ rs, 1+r.probes ≤ H := by
  rw [indexed_logs]
  constructor
  · have a := linked_cost_le_three G.nextStage G.addr Stage.pair (reports (paths p))
    have b : 4*S ≤ S*H := by simpa only [Nat.mul_comm 4 S] using Nat.mul_le_mul_left S hH
    have eq : S*(H-1)+S=S*H := by rw [← Nat.mul_succ,show (H-1).succ=H by omega]
    omega
  · intro r hr
    obtain ⟨src,hs,rfl⟩ := List.mem_map.mp hr
    rw [linkedReport_probes]
    have h := each src hs
    split <;> omega

end LiveProgram.PairStages.Group.CompressedPaths

end VPVNP
end Computability
end OAI
