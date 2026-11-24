import OAI.Computability.VPVNP.RAMProcessorGraphStart
import OAI.Computability.VPVNP.RAMProcessorInitFields
import OAI.Computability.VPVNP.RAMProcessorGraphProbeEmit

/-!
# Initializing and entering the complete burst-site graph

A freshly parsed site has empty architectural registers. The prelude creates
width-correct zeros in those registers and stages the five-word initialization
record. The caller supplies the zero-extended site address and the four-bit
header packed in a word, exactly the values produced by the input preparer.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM

variable {p r k w : ℕ}

/-- Stack bank of a freshly parsed site, with empty private register stacks ready for
initialization. -/
def Snapshot.bare (s : Snapshot w p r k) : Stacks (Port r k)
  | .isa (.reg _) => []
  | i => s.bank i

/-- Stage the initialization record's tag one, saved site address and zero probe ordinal in the
snapshot. -/
def Snapshot.withInitFields (s : Snapshot w p r k) (a : Word w) : Snapshot w p r k :=
  {s with tag := wordBits (Fin.ofNat (2^w) 1), savedStart := wordBits a, ordinal := wordBits (0 : Word w)}

/-- Initialize the private registers and write log for a fresh call, then stage the
initialization record fields. -/
def boot : FiniteRoutine (Port r k) :=
  ((ISA.freshCall (r := r) (k := k)).onPorts Port.isa).followedBy (RecordBuffer.initFields.onPorts recordPorts)

theorem initFields_run (s : Snapshot w p r k) (a : Word w) (ha : s.address = wordBits a) (ho : s.output = []) :
    (RecordBuffer.initFields.onPorts recordPorts).Runs (s.tag.length+s.savedStart.length+s.ordinal.length+21*w+9)
      s.bank (s.withInitFields a).bank := by
  have h := RecordBuffer.initFields_run s.records a ha (UnaryWord.zeros_wordBits w) rfl ho
  apply RecordBuffer.initFields.runs_onPorts_framed recordPorts_injective h s.record_at
  · intro j
    rw [Snapshot.record_at]
    cases j with
    | field j => fin_cases j <;> rfl
    | _ => rfl
  · intro j hj
    cases j with
    | isa _ | scratch _ => rfl
    | test i => cases i with | word f => cases f <;> rfl | _ => rfl
    | credit i =>
      cases i with
      | savedStart => exact (hj (.field 3) rfl).elim
      | ordinal => exact (hj (.field 4) rfl).elim
      | _ => rfl
    | record i =>
      cases i with
      | field i =>
        fin_cases i <;> first | rfl | exact (hj (.field 0) rfl).elim
      | _ => rfl

theorem boot_run (T : Template p r k) (s : Snapshot w p r k) (a : Word w)
    (ha : s.address = wordBits a) (ho : s.output = []) :
    ∃ t ≤ r*(8*w+3)+3*(s.cfg.writes.length*(w+1)+1)+2 +
      (s.tag.length+s.savedStart.length+s.ordinal.length+21*w+9),
      boot.Runs t s.bare ((s.afterFresh T).withInitFields a).bank := by
  obtain ⟨t, ht, fresh⟩ := ISA.freshCall_run s.pub s.cfg.persistent (fun _ : Fin r => [])
    s.cfg.writes (by simp)
  have h₁ : (ISA.freshCall.onPorts (Port.isa : ISA.Port r k → Port r k)).Runs t s.bare (s.afterFresh T).bank := by
    apply ISA.freshCall.runs_onPorts_framed (fun _ _ h => Port.isa.inj h) fresh
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · intro j hj
      cases j with
      | isa i => exact (hj i rfl).elim
      | test i => cases i with | word f => cases f <;> rfl | _ => rfl
      | record i => cases i <;> rfl
      | _ => rfl
  exact ⟨_, Nat.add_le_add_right ht _, h₁.followedBy (initFields_run (s.afterFresh T) a ha ho)⟩

/-- Test whether the control is at the site graph's successful completion label. -/
def graphDone {T : Template p r k} (q : Control T) : Bool :=
  match q.1 with | .done => true | _ => false

theorem graphDone_row (T : Template p r k) (q : Control T) (hq : graphDone q = true) :
    table T q = .halt true := by
  rcases q with ⟨q, state⟩
  cases q <;> first | contradiction | rfl

/-- Normal graph completion transfers the padded block to the next local
validator. A rejecting row halts the entire path. -/
def graphRoutine (T : Template p r k) : FiniteRoutine (Port r k) :=
  .ofStackCode (table T) id (atLabel T .initialRecord) graphDone

theorem graphRoutine_run (T : Template p r k) {t s u}
    (h : StackRuns (table T) t (atLabel T .initialRecord) s (atLabel T .done) u) :
    (graphRoutine T).Runs t s u := by
  have hhalt (q : Control T) (hq : graphDone q = true) : (table T q).returns = true := by
    rw [graphDone_row T q hq]; rfl
  exact FiniteRoutine.runs_ofStackCode_framed Function.injective_id (normal := graphDone) rfl rfl hhalt h
    (fun _ => rfl) (fun _ => rfl) (fun j hj => (hj j rfl).elim)

/-- Boot a freshly parsed site and execute its graph from initialization-record emission
through successful completion or rejection. -/
def callSite (T : Template p r k) : FiniteRoutine (Port r k) := boot.followedBy (graphRoutine T)

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
