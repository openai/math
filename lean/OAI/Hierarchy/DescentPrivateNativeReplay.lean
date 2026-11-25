import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentPrivateNativeDate

namespace OAI
/-! # Chronological execution of the private history counter on the issued path -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k j i z₀ D₀ z D wire hist bw a : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}

/-- The order of these programs is indexed by the same selected path as the
coefficient archive. A reset keeps the ordinary word in its fixed header. -/
inductive MeterCalendar (start : Reached W₀ G q ε S k j z₀ D₀ wire hist) (a bw : ℕ) :
    {W : MarkedWorld F d P bits}→{i z D : ℕ}→{source : Reached W G q ε S k i z D wire hist}→
    Path start source→Type 2 where
  | seed : MeterCalendar start a bw .here
  | ordinary {W : MarkedWorld F d P bits} {i z D z' D' : ℕ}
      {source : Reached W G q ε S k i z D wire hist} {p : Path start source}
      («prefix» : MeterCalendar start a bw p) {u : ℝ} {he : 0≤ε} {T : StageInput W G u ε}
      {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
      {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
      (ticket : OrdinaryLink source he T c n target) (port : MeterPort source) (emit : NativePhase bw) :
      MeterCalendar start a bw (p.ordinary ticket)
  | reset {W : MarkedWorld F d P bits} {i z D n h C f g cut tail : ℕ}
      {source : Reached W G q ε S k i z D wire hist} {p : Path start source}
      («prefix» : MeterCalendar start a bw p) {ctl : ResetRates G S k D n h C f g cut tail}
      (closed : ClosedReset source ctl) (emit : NativePhase bw) : MeterCalendar start a bw (p.reset closed)

namespace MeterCalendar
variable {path : Path start source} (calendar : MeterCalendar start a bw path)

/-- This complete finite instruction block includes the seed store, every
geometry phase in order, and one store back to the same header per ordinary date. -/
def program : Procedure bw := by
  induction calendar with
  | seed=>exact DescentPrivateHeader.clearHeader bw a
  | ordinary prev ticket port emit ih=>exact (ih.seq emit.program).seq (MeterPort.program ticket port a bw)
  | reset prev closed emit ih=>exact ih.seq emit.program

/-- The code-size bill uses the actual geometry programs' labels, registers and
literal slots, together with the two lookup tables and fixed counter hardware. -/
def hardware : ℕ := by
  induction calendar with
  | seed=>exact 15
  | ordinary prev ticket port emit ih=>exact (ih+DescentStaticWordColumn.names emit.program)+MeterPort.hardware ticket port
  | reset prev closed emit ih=>exact ih+DescentStaticWordColumn.names emit.program

theorem names_le : DescentStaticWordColumn.names calendar.program≤calendar.hardware := by
  induction calendar with
  | seed=>
    change DescentStaticWordColumn.names (ProtocolRAM.scan bw a 1 (.lit 0))≤15
    rw [DescentStaticWordColumn.names_scan]
    rfl
  | ordinary prev ticket port emit ih=>
    change DescentStaticWordColumn.names ((prev.program.seq emit.program).seq (MeterPort.program ticket port a bw))≤_
    rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq]
    exact Nat.add_le_add (Nat.add_le_add_right ih _) (MeterPort.names_le ticket port a bw)
  | reset prev closed emit ih=>
    change DescentStaticWordColumn.names (prev.program.seq emit.program)≤_
    rw [DescentStaticWordColumn.names_seq]
    exact Nat.add_le_add_right ih _

attribute [local irreducible] ProtocolRAM.CheapCode

theorem cheap : ProtocolRAM.CheapCode calendar.program := by
  induction calendar with
  | seed=>exact DescentPrivateHeader.initialize_cheap bw a
  | ordinary prev ticket port emit ih=>
    exact ProtocolRAM.cheap_seq (ProtocolRAM.cheap_seq ih emit.cheap) (MeterPort.cheap ticket port a bw)
  | reset prev closed emit ih=>exact ProtocolRAM.cheap_seq ih emit.cheap

def ticks : ℕ := by
  induction calendar with
  | seed=>exact 10
  | ordinary prev ticket port emit ih=>exact (ih+emit.ticks)+MeterPort.ticks ticket port a
  | reset prev closed emit ih=>exact ih+emit.ticks

def memory (m : Memory bw) : Memory bw := by
  induction calendar with
  | seed=>exact DescentPrivateHeader.initialized a m
  | ordinary prev ticket port emit ih=>exact MeterPort.image ticket port a (emit.image ih)
  | reset prev closed emit ih=>exact emit.image ih

def price (K : ℕ) : ℕ := by
  induction calendar with
  | seed=>exact 10*bw
  | ordinary prev ticket port emit ih=>exact (ih+emit.ticks*bw)+MeterPort.price ticket port bw K
  | reset prev closed emit ih=>exact ih+emit.ticks*bw

/-- Local source conditions refer to the actual memory left by the prefix.
In particular a step cannot substitute a donor bank from a different execution. -/
def Ready (K : ℕ) (m : Memory bw) : Prop := by
  induction calendar with
  | seed=>exact a+1<2^bw
  | ordinary prev ticket port emit ih=>
    let raw:=prev.memory m
    let out:=emit.image raw
    exact ih ∧ emit.program.Exec raw out emit.ticks ∧ out a=raw a ∧
      MeterPort.Fits ticket port a bw K ∧ MeterPort.Pins ticket port out
  | reset prev closed emit ih=>
    let raw:=prev.memory m
    let out:=emit.image raw
    exact ih ∧ emit.program.Exec raw out emit.ticks ∧ out a=raw a

theorem ready_seed {m : Memory bw} {K : ℕ} (header : a+1<2^bw) :
    (MeterCalendar.seed (start:=start) (a:=a) (bw:=bw)).Ready K m := header

/-- The first phase emits the actual stage geometry and the second gathers
the donor words from that same output memory. -/
theorem ready_ordinary {K : ℕ} {m : Memory bw} (old : calendar.Ready K m)
    {u : ℝ} {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
    {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink source he T c n target) (port : MeterPort source)
    (geometry gather : NativePhase bw) (first : geometry.Runs (calendar.memory m))
    (second : gather.Runs (geometry.image (calendar.memory m)))
    (saved : geometry.image (calendar.memory m) a=calendar.memory m a)
    (kept : gather.image (geometry.image (calendar.memory m)) a=geometry.image (calendar.memory m) a)
    (fit : MeterPort.Fits ticket port a bw K)
    (pins : MeterPort.Pins ticket port (gather.image (geometry.image (calendar.memory m)))) :
    (calendar.ordinary ticket port (geometry.seq gather)).Ready K m :=
  ⟨old,geometry.seq_runs gather _ first second,kept.trans saved,fit,pins⟩

theorem ready_reset {K : ℕ} {m : Memory bw} (old : calendar.Ready K m)
    {n h C f g cut tail : ℕ} {ctl : ResetRates G S k D n h C f g cut tail}
    (closed : ClosedReset source ctl) (phase : NativePhase bw) (write : phase.Runs (calendar.memory m))
    (keep : phase.image (calendar.memory m) a=calendar.memory m a) :
    (calendar.reset closed phase).Ready K m := ⟨old,write,keep⟩

theorem run (K : ℕ) (m : Memory bw) (ready : calendar.Ready K m) :
    calendar.program.Exec m (calendar.memory m) calendar.ticks ∧
      path.Held a (calendar.memory m) ∧ calendar.ticks*bw≤calendar.price K := by
  induction calendar with
  | seed=>
    exact ⟨DescentPrivateHeader.initialize_run a m ready,
      Path.Held.seed _ _ (DescentPrivateHeader.initialized_read a m),le_rfl⟩
  | ordinary prev ticket port emit ih=>
    obtain ⟨old,write,keep,fit,pins⟩:=ready
    obtain ⟨«prefix»,held,price⟩:=ih old
    obtain ⟨step,next,bill,_⟩:=MeterPort.advance ticket port a _ K _ fit pins (held.keep keep)
    refine ⟨?_,next,?_⟩
    · have first : (prev.program.seq emit.program).Exec m (emit.image (prev.memory m)) (prev.ticks+emit.ticks) := by
        intro P₂ R₂ C₂ mach₂ pc₂ reg₂ pub₂ exit₂ rom₂ advice₂ cfg₂ raw₂ enter₂ same₂
        exact Procedure.Exec.then «prefix» write mach₂ pc₂ reg₂ pub₂ exit₂ rom₂ advice₂ cfg₂ raw₂ enter₂ same₂
      intro P₁ R C mach pc reg pub exit rom advice cfg raw enter same
      exact Procedure.Exec.then first step mach pc reg pub exit rom advice cfg raw enter same
    · change ((prev.ticks+emit.ticks)+_)*bw≤(prev.price K+emit.ticks*bw)+_
      rw [Nat.add_mul,Nat.add_mul]
      exact Nat.add_le_add (Nat.add_le_add_right price _) bill
  | reset prev closed emit ih=>
    obtain ⟨old,write,keep⟩:=ready
    obtain ⟨«prefix»,held,cost⟩:=ih old
    refine ⟨?_,Path.Held.reset closed held keep,?_⟩
    · intro P₁ R C mach pc reg pub exit rom advice cfg raw enter same
      exact Procedure.Exec.then «prefix» write mach pc reg pub exit rom advice cfg raw enter same
    · change (prev.ticks+emit.ticks)*bw≤prev.price K+emit.ticks*bw
      rw [Nat.add_mul]
      exact Nat.add_le_add_right cost _

end MeterCalendar
end
end Hierarchy.DescentSixParty.Chronology

end OAI
