import OAI.Computability.VPVNP.RAMTapeSiteCore
import OAI.Computability.VPVNP.RAMTapeNamed

/-!
# Compiling the site's counted stack program into a literal two-tape table

The public reader is run once before the shared guard and private choice
tree. Only the bank produced by that deterministic startup enters the
counted computation. The literal table may be supplied as its own input
prefix, since the instruction table is fixed before that input is formed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts
set_option synthInstance.maxSize 10000

open BurstRAM LiveProgram PrivateRAM StackCompiler ProcessorInput

variable {p r k d e w : ℕ}

/-- Sequence deterministic public startup with the site’s guarded, choice-counted verifier. -/
def linked (expr : Fin k → PublicExpr) (T : Template p r k) (start : FiniteRoutine (Port r expr)) :=
  start.followedBy (core r expr T)

/-- Processor port initially containing the raw site input for two-tape compilation. -/
def inputPort (r : ℕ) (expr : Fin k → PublicExpr) := pub r expr ProcessorPublic.rawPort

/-- Compile the linked startup and site verifier to a literal two-tape program with the raw
input at its designated port. -/
noncomputable def table (expr : Fin k → PublicExpr) (T : Template p r k)
    (start : FiniteRoutine (Port r expr)) : UniversalMachine.Program :=
  let rt := (linked expr T start).body
  labeledProgram (inputPort r expr) (rt.close false) (some rt.entry)

theorem linked_stack_count (expr : Fin k → PublicExpr) (T : Template p r k) (start : FiniteRoutine (Port r expr))
    (x : SiteCutBank.Input d e w) (operands : Fin k → Word w) (raw s : Stacks (Port r expr))
    (steps ticks : ℕ) (hstart : start.Runs steps raw s) (hf : Frame r expr x operands s)
    (hblank : ∀ j : SitePost.Port, s (.inr (.inr j)) = []) (ht : coreSteps r x + steps ≤ ticks) :
    let rt := (linked expr T start).body
    stackPaths (rt.close false) ticks (some rt.entry) raw = x.pathCard T operands ∧
      StopsWithin (rt.close false) ticks (some rt.entry) raw := by
  intro rt
  let rem := ticks-steps
  have heq : ticks = rem+steps := by dsimp [rem]; omega
  have hcore := core_spec r expr T x operands s hf hblank rem (by dsimp [rem]; omega)
  constructor
  · rw [Routine.stackPaths_close]
    change (start.body.followedBy (core r expr T).body).count _ ticks raw = _
    rw [Routine.count_followedBy, heq, hstart.count_eq]
    exact hcore.1 _
  · rw [Routine.stopsWithin_close_iff]
    change (start.body.followedBy (core r expr T).body).AllStops _ ticks raw
    rw [Routine.allStops_followedBy, heq, hstart.allStops_iff]
    exact hcore.2 _

theorem table_coefficient (expr : Fin k → PublicExpr) (T : Template p r k)
    (start : FiniteRoutine (Port r expr)) (x : SiteCutBank.Input d e w) (operands : Fin k → Word w)
    (s : Stacks (Port r expr)) (steps ticks : ℕ)
    (fit : Fits (table expr T start) x.n d (2^e) w)
    (hstart : start.Runs steps (labeledInput (inputPort r expr)
      (tape (table expr T start) x.n x.v x.hdr (RAMLayout.incidentBits x.sends x.v))) s)
    (hf : Frame r expr x operands s) (hblank : ∀ j : SitePost.Port, s (.inr (.inr j)) = [])
    (ht : coreSteps r x + steps ≤ ticks)
    (hclock : ticks * (6 * (x.n + (Fintype.card (Port r expr)+1) + ticks) + 4) ≤ x.n^clockExponent) :
    acceptingCount (encode (table expr T start) x.n x.v x.hdr (RAMLayout.incidentBits x.sends x.v) fit) =
      x.pathCard T operands := by
  let rt := (linked expr T start).body
  obtain ⟨count,halt⟩ := linked_stack_count expr T start x operands _ s steps ticks hstart hf hblank ht
  exact (site_count_labeled (inputPort r expr) (rt.close false) (some rt.entry) x.n ticks x.v x.hdr
    (RAMLayout.incidentBits x.sends x.v) fit halt hclock).trans count

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
