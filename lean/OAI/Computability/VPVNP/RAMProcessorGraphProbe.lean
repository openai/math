import OAI.Computability.VPVNP.RAMProcessorGraphRuns

/-!
# Native graph transfers for reads, writes and call returns

At an external read the graph copies the old address, consumes a full guessed
word, and only then replaces the destination register. Writes copy both original
register values. Return and acceptance update the persistent state/status used
by the site's iteration test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM

variable {w p r k : ℕ}

private def Snapshot.withProbe (s : Snapshot w p r k) (cfg : LogConfig w p r)
    (choices tag addr value : List Bool) (running : Bool) : Snapshot w p r k :=
  {s with cfg := cfg, choices := choices, tag := tag, address := addr, value := value, running := running}

/-- The record stages the address from before the destination register was
assigned. Thus the address and destination may be the same register. -/
def Snapshot.afterRead (s : Snapshot w p r k) (dst addr : Fin r) (next : Fin p)
    (v : Word w) (tail : List Bool) : Snapshot w p r k :=
  s.withProbe {s.cfg with pc := next, reg := Function.update s.cfg.reg dst v} tail
    (wordBits (Fin.ofNat (2^w) 2)) (wordBits (s.cfg.reg addr)) (wordBits v) s.running

/-- Snapshot after decoding an external write, with the next instruction selected and the write
tag, source address and value staged for recording. -/
def Snapshot.afterWrite (s : Snapshot w p r k) (addr src : Fin r) (next : Fin p) : Snapshot w p r k :=
  s.withProbe {s.cfg with pc := next} s.choices (wordBits (Fin.ofNat (2^w) 3))
    (wordBits (s.cfg.reg addr)) (wordBits (s.cfg.reg src)) s.running

/-- Snapshot after a call returns the designated register as its persistent word and marks the
machine as running. -/
def Snapshot.afterReturn (s : Snapshot w p r k) (src : Fin r) : Snapshot w p r k :=
  s.withProbe {s.cfg with persistent := s.cfg.reg src} s.choices s.tag s.address s.value true

/-- Snapshot after acceptance, with the running flag cleared for the site's next iteration
test. -/
def Snapshot.afterAccept (s : Snapshot w p r k) : Snapshot w p r k :=
  s.withProbe s.cfg s.choices s.tag s.address s.value false

private theorem probe_frame (s : Snapshot w p r k) (cfg : LogConfig w p r)
    (cs t a v : List Bool) (run : Bool) (j : Port r k) (hj : ∀ i, probePorts i ≠ j) :
    (s.withProbe cfg cs t a v run).bank j = s.bank j := by
  cases j with
  | isa i => exact (hj (.inl i) rfl).elim
  | credit i => rfl
  | test i =>
    cases i with
    | choices => exact (hj (.inr .choices) rfl).elim
    | bit b => cases b <;> first | rfl | exact (hj (.inr .running) rfl).elim
    | word f => cases f <;> rfl
    | _ => rfl
  | record i =>
    cases i with
    | field f =>
      fin_cases f <;>
        first | rfl | exact (hj (.inr .tag) rfl).elim | exact (hj (.inr .address) rfl).elim |
          exact (hj (.inr .value) rfl).elim
    | _ => rfl
  | scratch _ => rfl

private theorem read_probe (s : Snapshot w p r k) (dst addr : Fin r) (next : Fin p)
    (v : Word w) (tail : List Bool) :
    (s.afterRead dst addr next v tail).probe =
      {s.probe with
        choices := tail
        value := wordBits v
        tag := wordBits (Fin.ofNat (2^w) 2)
        address := wordBits (s.cfg.reg addr)
        isa := Function.update s.probe.isa (.reg dst) (wordBits v)} := by
  simp only [Snapshot.afterRead, Snapshot.withProbe, Snapshot.probe, ISA.configBank, ISA.bank_updateReg]

private theorem return_probe (s : Snapshot w p r k) (src : Fin r) :
    (s.afterReturn src).probe =
      {s.probe with isa := Function.update s.probe.isa .persistent (wordBits (s.cfg.reg src)), running := [true]} := by
  have he : ISA.configBank s.pub {s.cfg with persistent := s.cfg.reg src} =
      Function.update (ISA.configBank s.pub s.cfg) .persistent (wordBits (s.cfg.reg src)) := by
    funext j
    cases j <;> simp [ISA.configBank, ISA.bank]
  simp only [Snapshot.afterReturn, Snapshot.withProbe, Snapshot.probe, he]

/-- Genuine path on the table from read dispatch to record emission. -/
theorem read_run (T : Template p r k) (s : Snapshot w p r k) (dst addr : Fin r) (next : Fin p)
    (v : Word w) (tail : List Bool) (hs : s.choices = wordBits v ++ tail) :
    StackRuns (table T) (s.value.length+s.tag.length+s.address.length+30*w+13)
      (atLabel T (.read dst addr next)) s.bank (atLabel T (.emit next)) (s.afterRead dst addr next v tail).bank := by
  let out := s.afterRead dst addr next v tail
  have hr := ProbeStages.read_run dst addr (Label.emit (r := r) next) .reject s.probe s.cfg.persistent
    (s.cfg.reg addr) v tail rfl rfl hs
  rw [← read_probe s dst addr next v tail] at hr
  have ht : s.probe.value.length+s.probe.tag.length+s.probe.address.length+(s.probe.isa (.reg dst)).length+29*w+13 =
      s.value.length+s.tag.length+s.address.length+30*w+13 := by
    change _ + (wordBits (s.cfg.reg dst)).length + 29*w + 13 = _
    rw [length_wordBits]
    dsimp only [Snapshot.probe]
    omega
  rw [ht] at hr
  exact ProcessorFlow.run (blocks := blocks T) (l := .read dst addr next)
    (Fragment.runs_framed probePorts_injective hr s.probe_at out.probe_at (probe_frame s _ _ _ _ _ _))

/-- Short read guesses reach the literal rejecting table row. -/
theorem read_short (T : Template p r k) (s : Snapshot w p r k) (dst addr : Fin r) (next : Fin p)
    (hs : s.choices.length < w) :
    RejectRun (table T) (s.value.length+4*s.choices.length+3) (atLabel T (.read dst addr next)) s.bank := by
  obtain ⟨out,hr⟩ := ProbeStages.read_short dst addr (Label.emit (r := r) next) .reject
    s.probe (s.cfg.reg addr) rfl hs
  have hp := Fragment.runs_onPorts probePorts probePorts_injective s.bank hr
  rw [installStacks_eq probePorts_injective s.bank s.probe.stacks s.probe_at] at hp
  exact ⟨atLabel T .reject, _, ProcessorFlow.run (blocks := blocks T) (l := .read dst addr next) hp, rfl⟩

theorem write_run (T : Template p r k) (s : Snapshot w p r k) (addr src : Fin r) (next : Fin p) :
    StackRuns (table T) (s.tag.length+s.address.length+s.value.length+21*w+9)
      (atLabel T (.write addr src next)) s.bank (atLabel T (.emit next)) (s.afterWrite addr src next).bank := by
  let out := s.afterWrite addr src next
  have hr := Fragment.returning_runs (ProbeStages.writePayload_run addr src s.probe s.cfg.persistent
    (s.cfg.reg addr) (s.cfg.reg src) rfl rfl rfl) (Label.emit (r := r) next)
  exact ProcessorFlow.run (blocks := blocks T) (l := .write addr src next)
    (Fragment.runs_framed probePorts_injective hr s.probe_at out.probe_at (probe_frame s _ _ _ _ _ _))

theorem returnState_run (T : Template p r k) (s : Snapshot w p r k) (src : Fin r) :
    StackRuns (table T) (8*w+6) (atLabel T (.callback (.returnState src))) s.bank
      (atLabel T .iteration) (s.afterReturn src).bank := by
  let out := s.afterReturn src
  have hr := Fragment.returning_runs (ProbeStages.returnState_run src s.probe s.cfg.persistent
    (s.cfg.reg src) rfl rfl) (Label.iteration (p := p) (r := r))
  rw [← return_probe s src] at hr
  exact ProcessorFlow.run (blocks := blocks T) (l := .callback (.returnState src))
    (Fragment.runs_framed probePorts_injective hr s.probe_at out.probe_at (probe_frame s _ _ _ _ _ _))

theorem accept_run (T : Template p r k) (s : Snapshot w p r k) :
    StackRuns (table T) 3 (atLabel T (.callback .accept)) s.bank
      (atLabel T .iteration) s.afterAccept.bank := by
  have hr := Fragment.returning_runs (ProbeStages.accept_run s.probe) (Label.iteration (p := p) (r := r))
  exact ProcessorFlow.run (blocks := blocks T) (l := .callback .accept)
    (Fragment.runs_framed probePorts_injective hr s.probe_at s.afterAccept.probe_at (probe_frame s _ _ _ _ _ _))

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
