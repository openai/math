import OAI.Hierarchy.DescentCommonDateFamily
import OAI.Hierarchy.DescentChronologicalGrains

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k wire hist w : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits} {z₀ D₀ i z D:ℕ}
    {initial:Reached I G q ε S k 0 z₀ D₀ wire hist} {current:Reached W G q ε S k i z D wire hist}
    (path : Path initial current)

/-- A date of one particular selected full history. Both endpoints are the
original reached states and the residual suffix is part of the cut. -/
inductive Path.Event (age : ℕ) : Type 2 where
  | ordinary {U : MarkedWorld F d P bits} {z D z' D' : ℕ} {u : ℝ}
      {src : Reached U G q ε S k age z D wire hist} {he : 0≤ ε}
      {T : StageInput U G u ε} {choice : (T.result he).Choice}
      {normalize : Normalize ((T.result he).state choice)}
      {dst : Reached normalize.result G q ε S k (age+1) z' D' wire hist}
      (before : Path initial src) (ticket : OrdinaryLink src he T choice normalize dst)
      (after : Path dst current) (cut : (before.ordinary ticket).append after=path)
  | reset {U : MarkedWorld F d P bits} {z D n h C f g cut tail : ℕ}
      {src : Reached U G q ε S k age z D wire hist}
      {ctl : ResetRates G S k D n h C f g cut tail} (before : Path initial src)
      (closed : ClosedReset src ctl) (after : Path closed.next current)
      (placed : (before.reset closed).append after=path)

namespace Path.Event
variable {path} {age : ℕ}

def isReset : path.Event age→Bool
  | .ordinary ..=>false
  | .reset ..=>true

omit [Fintype P] in
theorem shown (event : path.Event age) :
    (path.kinds.drop age).head?=some event.isReset :=by
  cases event with
  | ordinary before ticket after cut=>exact ticket.kind_on_cut before after cut rfl
  | reset before closed after cut=>exact reset_kind_on_cut closed before after cut rfl

omit [Fintype P] in
theorem compatible {I' U : MarkedWorld F d P bits} {j z₁ D₁ z₂ D₂ : ℕ}
    {first : Reached I' G q ε S k 0 z₂ D₂ wire hist}
    {r : Reached U G q ε S k j z₁ D₁ wire hist} {p : Path first r}
    (event : path.Event age) (other : p.Event age) (tags : path.kinds=p.kinds) :
    event.isReset=other.isReset :=by
  apply Option.some.inj
  rw [←event.shown,←other.shown,tags]

end Path.Event

structure RunTrace (G : PoweredGadget F) (q ε : ℝ) (S : AtomSchedule) (k wire hist len : ℕ)
    (bits : P→ℕ) (d : ℕ) where
  inputWorld : MarkedWorld F d P bits
  outputWorld : MarkedWorld F d P bits
  firstGrain : ℕ
  firstDegree : ℕ
  lastGrain : ℕ
  lastDegree : ℕ
  first : Reached inputWorld G q ε S k 0 firstGrain firstDegree wire hist
  last : Reached outputWorld G q ε S k len lastGrain lastDegree wire hist
  path : Path first last

namespace RunTrace
variable {C : Type*} {len : ℕ} (trace : C→RunTrace G q ε S k wire hist len bits d)

abbrev Events (age : ℕ) := (c : C) × (trace c).path.Event age

/-- A common program at every date, chosen from an actual named physical
instruction at that age, across all original terminal choices. -/
def machine (code : ∀a,Events trace a→DateCode w) := DateCode.fromCuts (Events trace) code

omit [Fintype P] in
theorem on_branch (code : ∀a,Events trace a→DateCode w)
    (common : ∀a,∀x y : Events trace a,code a x=code a y)
    (c : C) (a : ℕ) (event : (trace c).path.Event a) :
    machine trace code a=code a ⟨c,event⟩ :=DateCode.fromCuts_at _ code common a _

end RunTrace
end
end Hierarchy.DescentSixParty.Chronology

end OAI
