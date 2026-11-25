import OAI.Computability.BorderVNP.TeamGuessReplay
import OAI.Computability.BorderVNP.TeamLink
import OAI.Computability.BorderVNP.TeamProbeEmit
import OAI.Computability.BorderVNP.TeamWordAssignments
import OAI.Computability.BorderVNP.TeamOpcodeDispatch

/-! # Physical preparation and completion of an ordinary RAM probe

The processor stages the address before changing a load destination, including when the two
registers coincide. It guesses one full previous word, writes the previous and resulting
words to the shared sort buffer, and installs the result of a load. A store's previous word
is guessed and checked exactly like that of a load.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamMemoryCallback

open VPVNP RAMTape BurstRAM RAMSerialization TeamPrivateFragment TeamProbeEmit

variable {r k w H : ℕ}

/-- Register operands of an ordinary shared-memory instruction. -/
inductive Op (r : ℕ) where
  | load (dst address : Fin r)
  | store (address src : Fin r)
  deriving DecidableEq, Fintype

/-- Register whose original word addresses the external probe. -/
def Op.addr : Op r → Fin r | .load _ a | .store a _ => a

/-- The register file, physical paired-probe buffer, probe tick, and reusable copy scratch. -/
abbrev Port (r k : ℕ) := ISA.Port r k ⊕ TeamProbeEmit.Port ⊕ Bool

private abbrev isa (p : ISA.Port r k) : Port r k := .inl p
private abbrev emit (p : TeamProbeEmit.Port) : Port r k := .inr (.inl p)
private abbrev word (p : Operand) : Port r k := emit (.operand p)
private abbrev tick : Port r k := .inr (.inr false)
private abbrev temp : Port r k := .inr (.inr true)

private def src (op : Op r) : Port r k :=
  match op with | .load .. => word .before | .store _ reg => isa (.reg reg)

/-- Original register and tick values and a possibly reused probe buffer. -/
structure Ready (hw : 2 ≤ w+1) (H : ℕ) (pub : Fin k → Word w) (reg : Fin r → Word w)
    (t : Word w) (rs : List (WordRecord (w+1))) (s : Stacks (Port r k)) : Prop where
  /-- Register, public, and arithmetic work ports form a clean instruction boundary. -/
  registers : s ∘ isa = ISA.bank pub 0 reg []
  /-- Tick of the probe, starting at one in the global run. -/
  time : s tick = BurstRAM.wordBits t
  /-- Scratch used by copies and the binary guess is blank. -/
  tmp : s temp = []
  /-- Reused operand ports hold at most one logical word apiece. -/
  short : ∀ i, (s (word i)).length ≤ w
  /-- The scratch of the widening routine is blank. -/
  scratch : s (emit .temp) = []
  /-- All reused widened words fit the sorting width. -/
  lifted : ∀ i, (s (emit (.lifted i))).length ≤ w+1
  /-- Existing record prefix and remaining physical capacity. -/
  buffer : RecordBuffer.Holds hw H rs (s ∘ emit ∘ TeamProbeEmit.Port.buffer)
  /-- The five reusable serialization words fit the physical width. -/
  fields : ∀ j, (s (emit (.buffer (.field j)))).length ≤ w+1

private def pre (op : Op r) : FiniteRoutine (Port r k) :=
  ((TeamWords.assign (isa (.reg op.addr)) (word .address) temp).followedBy
    (TeamWords.assign tick (word .tick) temp)).followedBy (SliceArithmetic.CallClear.clear (word .before))

private def begun (s : Stacks (Port r k)) (op : Op r) : Stacks (Port r k) :=
  Function.update (Function.update (Function.update s (word .address) (s (isa (.reg op.addr)))) (word .tick)
    (s tick)) (word .before) []

private theorem pre_runs {hw : 2 ≤ w+1} {pub : Fin k → Word w} {reg : Fin r → Word w} {t : Word w}
    {rs : List (WordRecord (w+1))} {s : Stacks (Port r k)} (op : Op r) (ready : Ready hw H pub reg t rs s) :
    ∃ n ≤ 13*w+7, (pre op).Runs n s (begun s op) := by
  let mid := Function.update s (word .address) (s (isa (.reg op.addr)))
  let next := Function.update mid (word .tick) (s tick)
  have h1 := TeamWords.assign_runs (isa (.reg op.addr)) (word .address) temp (by simp) (by simp)
    (by simp) s ready.tmp
  have h2 := TeamWords.assign_runs tick (word .tick) temp (by simp) (by simp) (by simp) mid
    (by simpa [mid] using ready.tmp)
  have h3 := SliceArithmetic.CallClear.clear_runs (word .before) next
  have hreg : s (isa (.reg op.addr)) = BurstRAM.wordBits (reg op.addr) := congrFun ready.registers _
  simp only [mid, Function.update_of_ne (show tick ≠ (word .address : Port r k) by simp)] at h2
  refine ⟨_, ?_, (h1.followedBy h2).followedBy h3⟩
  have ha := ready.short .address; have ht := ready.short .tick; have hb := ready.short .before
  simp [mid, next, hreg, ready.time]; omega

/-- Words in the RAM probe, including the previous word on a store. -/
def operands (op : Op r) (reg : Fin r → Word w) (t old : Word w) : Operand → Word w
  | .address => reg op.addr | .tick => t | .before => old
  | .after => match op with | .load .. => old | .store _ i => reg i

/-- Architectural register update after the memory probe. -/
def registers (op : Op r) (reg : Fin r → Word w) (old : Word w) : Fin r → Word w :=
  match op with | .load dst _ => Function.update reg dst old | .store .. => reg

/-- The two physical slots to append, on the widened sorter wires. -/
def pair (op : Op r) (reg : Fin r → Word w) (t old : Word w) : List (WordRecord (w+1)) :=
  let z := operands op reg t old
  TeamTapeSorting.wordPair (widenRecord (probe z)) (probeFits z)

private def setResult (op : Op r) : FiniteRoutine (Port r k) :=
  match op with | .load dst _ => TeamWords.assign (word .before) (isa (.reg dst)) temp | .store .. => .ret

private def post (op : Op r) : FiniteRoutine (Port r k) :=
  ((TeamWords.assign (src op) (word .after) temp).followedBy (TeamProbeEmit.program.onPorts emit)).followedBy
    (setResult op)

private abbrev guessed (s : Stacks (Port r k)) (op : Op r) (old : Word w) :=
  Function.update (begun s op) (word .before) (BurstRAM.wordBits old)

private theorem emit_inj : Function.Injective (emit : TeamProbeEmit.Port → Port r k) :=
  Sum.inr_injective.comp Sum.inl_injective

private theorem post_runs {hw : 2 ≤ w+1} {pub : Fin k → Word w} {reg : Fin r → Word w} {t : Word w}
    {rs : List (WordRecord (w+1))} {s : Stacks (Port r k)} (op : Op r) (old : Word w)
    (ready : Ready hw H pub reg t rs s) (free : rs.length+2 ≤ 4*H) :
    ∃ n out, n ≤ 167*w+215 ∧ (post op).Runs n (guessed s op old) out ∧
      Ready hw H pub (registers op reg old) t (rs++pair op reg t old) out := by
  let g := guessed s op old
  let z := operands op reg t old
  let staged := Function.update g (word .after) (g (src op))
  have hgReg (i) : g (isa (.reg i)) = BurstRAM.wordBits (reg i) := by
    exact congrFun ready.registers _
  have hsrc : g (src op) = BurstRAM.wordBits (z .after) := by
    cases op with
    | load d a => simp [g, guessed, src, z, operands]
    | store a i => exact hgReg i
  have tmpG : g temp = [] := ready.tmp
  have prepare := TeamWords.assign_runs (src op) (word .after) temp (by cases op <;> simp [src])
    (by cases op <;> simp [src]) (by simp) g tmpG
  have regStage : staged ∘ isa = ISA.bank pub 0 reg [] := ready.registers
  have hs : Staged hw H z rs (staged ∘ emit) := by
    refine ⟨?_,ready.scratch,ready.lifted,ready.buffer,ready.fields⟩
    intro i
    cases i with
    | address => exact congrFun ready.registers _
    | tick => exact ready.time
    | before => simp [staged, g, guessed, operands, z, emit, word]
    | after => simpa [staged, emit, word] using hsrc
  obtain ⟨em, small, he, emitRun, hend⟩ := TeamProbeEmit.runs hs free
  let v := installStacks emit staged small
  have hv : v ∘ emit = small := funext fun p => installStacks_at emit_inj staged small p
  have outside (p : ISA.Port r k) : v (isa p) = staged (isa p) := installStacks_outside _ _ (by simp [emit, isa])
  have outsideAux (p : Bool) : v (.inr (.inr p)) = staged (.inr (.inr p)) := installStacks_outside _ _ (by simp [emit])
  have rt := TeamProbeEmit.program.runs_onPorts emit_inj staged emitRun
  rw [installStacks_eq emit_inj staged (staged ∘ emit) (fun _ => rfl)] at rt
  have vregs : v ∘ isa = ISA.bank pub 0 reg [] := (funext outside).trans regStage
  have postV : Ready hw H pub reg t (rs++pair op reg t old) v := by
    rw [← hv] at hend
    exact ⟨vregs,(outsideAux false).trans ready.time,(outsideAux true).trans ready.tmp,
      fun i => by rw [show v (word i) = BurstRAM.wordBits (z i) from hend.operands i, length_wordBits],
      hend.scratch,hend.work,hend.buffer,hend.fields⟩
  have hl := ready.short .after
  have hlen : (g (word .after)).length ≤ w := hl
  have before : v (word .before) = BurstRAM.wordBits old := (congrFun hv _).trans (hend.operands .before)
  cases op with
  | store a i =>
    refine ⟨_,v,?_,(prepare.followedBy rt).followedBy (Routine.runs_ret v),postV⟩
    rw [hsrc, length_wordBits]; omega
  | load dst a =>
    let final := Function.update v (isa (.reg dst)) (BurstRAM.wordBits old)
    have update := TeamWords.assign_runs (word .before) (isa (.reg dst)) temp (by simp) (by simp) (by simp) v postV.tmp
    rw [before] at update
    have dval : v (isa (.reg dst)) = BurstRAM.wordBits (reg dst) := congrFun vregs _
    refine ⟨_,final,?_,(prepare.followedBy rt).followedBy update,?_,postV.time,postV.tmp,postV.short,
      postV.scratch,postV.lifted,postV.buffer,postV.fields⟩
    · rw [dval, hsrc, length_wordBits, length_wordBits, length_wordBits]; omega
    · rw [registers, ← ISA.bank_updateReg]
      funext p; by_cases eq : p = .reg dst <;> simp [final, eq, isa, ← vregs]

/-- Embedded stack labels of one complete ordinary load or store. -/
inductive Label (k : ℕ) (op : Op r) where
  | setup (q : (pre (k := k) op).State)
  | guess (q : TeamGuessWord.State)
  | finish (q : (post (k := k) op).State)
  | done
  deriving Fintype

private def guessPort : TeamGuessWord.Port → Port r k
  | .width => word .address | .saved => temp | .out => word .before

private theorem guess_inj : Function.Injective (guessPort (r := r) (k := k)) := by
  intro p q eq; cases p <;> cases q <;> simp_all [guessPort]

/-- Physical stack machine for one adaptive shared-memory load or store. -/
def code (op : Op r) : StackCode (Port r k) (Label k op)
  | .setup q => ((pre op).body.code q).rename id (fun z => z.elim (.guess .scan) Label.setup)
  | .guess .done => .goto (.finish (post op).body.entry)
  | .guess q => (TeamGuessWord.code q).rename guessPort Label.guess
  | .finish q => ((post op).body.code q).rename id (fun z => z.elim .done Label.finish)
  | .done => .halt true

/-- Entry point for the opcode controller before consuming any guessed old-word bits. -/
def entry (op : Op r) : Label k op := .setup (pre op).body.entry

/-- The real stack machine takes exactly one spelling of the previous word, appends both
physical records, preserves the continuation bits and commits the advertised registers.
The bound includes every instruction of staging, guessing, emission and register writeback. -/
theorem run {hw : 2 ≤ w+1} {pub : Fin k → Word w} {reg : Fin r → Word w} {t : Word w}
    {rs : List (WordRecord (w+1))} {s : Stacks (Port r k)} (op : Op r) (old : Word w) (suffix : List Bool)
    (ready : Ready hw H pub reg t rs s) (free : rs.length+2 ≤ 4*H) :
    ∃ n out, n ≤ 186*w+225 ∧ StackRuns (replay (code op)) n (entry op, (BurstRAM.wordBits old).reverse ++ suffix) s
      (.done,suffix) out ∧ Ready hw H pub (registers op reg old) t (rs++pair op reg t old) out := by
  obtain ⟨a, ha, preRun⟩ := pre_runs op ready
  have hpre := TeamLink.routine_id preRun (code op) Label.setup (.guess .scan) (fun _ => rfl)
  let mid := begun s op
  let bits := BurstRAM.wordBits (reg op.addr)
  have hreg : s (isa (.reg op.addr)) = bits := congrFun ready.registers _
  have hinit : installStacks guessPort mid (TeamGuessWord.bank bits [] []) = mid := by
    apply installStacks_eq guess_inj
    intro p
    cases p <;> simp [mid, begun, guessPort, TeamGuessWord.bank, ready.tmp, hreg]
  have hout : installStacks guessPort mid (TeamGuessWord.bank bits [] (BurstRAM.wordBits old)) = guessed s op old := by
    apply installStacks_frame guess_inj
    · intro p; cases p <;> simp [guessed, begun, guessPort, TeamGuessWord.bank, ready.tmp, hreg]
    · intro p hp
      have ho := Ne.symm (hp .out)
      change p ≠ word .before at ho
      simp [guessed, ho, mid]
  have hguess := TeamGuessWord.replay_runs (code op) guessPort guess_inj Label.guess mid
    (fun q h => by cases q <;> first | rfl | contradiction) bits (BurstRAM.wordBits old) suffix
    (by simp [bits])
  rw [hinit, hout, show bits.length = w from length_wordBits _] at hguess
  have hg : StackRuns (replay (code op)) 1 (.guess .done, suffix) (guessed s op old)
      (.finish (post op).body.entry, suffix) (guessed s op old) := .cons (.goto rfl) (.nil ..)
  obtain ⟨b,out,hb,postRun,houtReady⟩ := post_runs op old ready free
  have hpost := TeamLink.routine_id postRun (code op) Label.finish .done (fun _ => rfl)
  refine ⟨_,out,?_,(((replay_segment hpre _).trans hguess).trans hg).trans (replay_segment hpost suffix),houtReady⟩
  omega

end TeamMemoryCallback

end BorderVNP
end Computability
end OAI
