import OAI.Hierarchy.DescentChronologicalLastReset
import OAI.Hierarchy.DescentDatedBranchEvents

namespace OAI
/-! # The posted reset at the final cut of a recorded ballot -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k wire hist : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {I W : MarkedWorld F d P bits} {z₀ D₀ i z D : ℕ}
  {initial : Reached I G q ε S k 0 z₀ D₀ wire hist}
  {current : Reached W G q ε S k i z D wire hist}

/-- Both pieces of the selected ballot's replay certificate, with its original
terminal world retained as an index. -/
inductive Path.FinalReset (p : ℕ) :
    {U : MarkedWorld F d P bits} → {age grain degree : ℕ} →
    {target : Reached U G q ε S k age grain degree wire hist} → Path initial target → Type 2 where
  | posted {U : MarkedWorld F d P bits} {age grain degree n h C f g cut tail : ℕ}
      {source : Reached U G q ε S k age grain degree wire hist}
      {rates : ResetRates G S k degree n h C f g cut tail} (before : Path initial source)
      (B : ClosedReset source rates) («prefix» : before.recorded p) (paid : B.Recorded p) :
      Path.FinalReset p (before.reset B)

def Path.finalReset (path : Path initial current) (p : ℕ) (paid : path.recorded p)
    (ends : path.kinds.getLast?=some true) : Path.FinalReset p path :=
  path.terminal_of_last_reset p paid ends (fun earlier=>Path.FinalReset p earlier)
    (fun before B _ «prefix» last=>.posted before B «prefix» last)

def Path.FinalReset.event {path : Path initial current} {p : ℕ} (last : Path.FinalReset p path) :
    path.Event (i-1) := by
  cases last with
  | posted before B «prefix» paid=>exact .reset before B .here rfl

omit [Fintype P] in
theorem Path.FinalReset.is_reset {path : Path initial current} {p : ℕ} (last : Path.FinalReset p path) :
    last.event.isReset=true := by
  cases last
  rfl

omit [Fintype P] in
theorem Path.FinalReset.succ_age {path : Path initial current} {p : ℕ} (last : Path.FinalReset p path) :
    i-1+1=i := by
  cases last
  omega

end
end Hierarchy.DescentSixParty.Chronology

end OAI
