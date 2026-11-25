import OAI.Computability.BorderVNP.TeamSiteProcessorEntry
import OAI.Computability.BorderVNP.TeamSiteProcessorRoles

/-! # Execution from the raw n-bit input to a signed processor block

The real parser's time-zero memory initialization is followed by public word loading,
frame measurement and role dispatch. All of these steps use deterministic rows, so the
first block instruction receives exactly the original choice stream.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor

open VPVNP BurstRAM RAMTape Layout TeamPrivateFragment

variable {Q Γ : Type} {p r k a m g w d : ℕ}

private theorem loaded_marks (s : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w)
    (H limit max : Word w) (literalTail wires marks incoming outgoing marks' : List Bool) :
    Function.update (Bank.loaded (d := d) (r := r) s pub H limit max literalTail wires marks incoming outgoing)
      .frameWidth marks' = Bank.loaded s pub H limit max literalTail wires marks' incoming outgoing := by
  funext j
  cases j with
  | work j => cases j <;> rfl
  | route j =>
    rcases j with j | j
    · rfl
    · cases j with
      | entry j =>
        rcases j with j | j
        · cases j with
          | cut i | peek i => cases i <;> rfl
          | _ => rfl
        · rfl
      | _ => rfl
  | _ => rfl

private theorem loaded_staged (s : Stacks TeamTapeInput.Entry.Port) (pub : Fin k → Word w)
    (H limit max : Word w) (literalTail wires marks incoming outgoing lit' wires' in' out' : List Bool) :
    staged (r := r) (m := m) (g := g) (Bank.loaded s pub H limit max literalTail wires marks incoming outgoing)
      lit' wires' in' out' = Bank.loaded s pub H limit max lit' wires' marks in' out' := by
  funext j
  cases j with
  | work j => cases j <;> rfl
  | route j =>
    rcases j with j | j
    · rfl
    · cases j with
      | entry j =>
        rcases j with j | j
        · cases j with
          | cut i | peek i => cases i <;> rfl
          | _ => rfl
        · rfl
      | _ => rfl
  | _ => rfl

/-- Source-stack time for the deterministic prefix, including the actual initialization
run and all role-dependent frame reads. -/
def preludeTime (entryTicks r k w : ℕ) (last : Bool) :=
  entryTicks + ((5*(w+1)+2+2)+((k+8)*(6*w+2)+1)) + ((r+2)*(5*w+2)+1) + roleTime last (frameSize r w)

/-- One actual raw-input initialization run passes through the public loader and both
field cutters. This is valid for all frame bits, regardless of what the subsequent
canonicality and RAM checks decide. -/
theorem prelude_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (raw : List Bool) (s : Stacks TeamTapeInput.Entry.Port) {t : ℕ}
    (init : TeamTapeInput.Entry.program.Runs t (Sum.elim (TeamTapeInput.initial raw) (fun _ => [])) s)
    (pub : Fin k → Word w) (H limit max : Word w) (first last : Bool)
    (ingress egress literalTail wireTail : List Bool) (width : (s (.inr .start)).length = w+1)
    (literal : s (.inl (.peek .input)) =
      TeamPublicWords.bytes (parameters pub H limit max) ++ roleBytes first last ingress literalTail)
    (wires : s (.inl (.cut .incident)) = incidentBytes first last ingress egress wireTail)
    (inSize : ingress.length = frameSize r w) (outSize : last = false → egress.length = frameSize r w) :
    StackRuns (code P lib) (preludeTime t r k w last) start (StackCompiler.labeledInput input raw)
      (beginBlock last) (Bank.loaded s pub H limit max literalTail wireTail
        (List.replicate (frameSize r w) true) ingress (if last then [] else egress)) := by
  let lit := roleBytes first last ingress literalTail
  let route := incidentBytes first last ingress egress wireTail
  let marks := List.replicate (frameSize r w) true
  let initBank := Bank.loaded (r := r) (d := m*g) s pub H limit max lit route [] [] []
  let marked := Bank.loaded (r := r) (d := m*g) s pub H limit max lit route marks [] []
  have parsed :=  initialize_run P lib raw s init
  have words := parameters_run P lib s pub H limit max lit width literal
  rw [wires] at words
  have measure := frameMarks_runs initBank (show (initBank .width).length = w from List.length_replicate)
    (show initBank .frameWidth = [] from rfl) (show initBank .tmp = [] from rfl)
  rw [loaded_marks] at measure
  have linked : StackRuns (code P lib) ((r+2)*(5*w+2)+1)
      (.measure frameMarks.body.entry) initBank .first marked :=
    TeamLink.routine_id measure (code P lib) .measure .first (fun _ => rfl)
  have roles := roles_run P lib marked first last ingress egress literalTail wireTail rfl rfl
    (by rw [inSize]; rfl) (fun hl => (outSize hl).trans inSize.symm) rfl rfl rfl
  rw [inSize,loaded_staged] at roles
  exact ((parsed.trans words).trans linked).trans roles

/-- The complete endpoint path sits inside the assembled signed processor and consumes
exactly the same choice prefix. The record close and sorter receive its actual final bank. -/
theorem endpoint_replay (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    {t q bits localBank q' rest out} (hr : StackRuns (replay (Endpoint.code P lib)) t (q,bits) localBank (q',rest) out)
    (s : Stacks (Layout.Port r k (m*g))) (ready : s ∘ endpoint = localBank) :
    StackRuns (replay (code P lib)) t (.block q,bits) s (.block q',rest) (installStacks endpoint s out) := by
  have h := TeamLink.replay_lift hr (code P lib) endpoint endpoint_injective .block s (by
    intro q hc; cases q <;> first | rfl | simp [Endpoint.code] at hc)
  rwa [installStacks_eq endpoint_injective s localBank (congrFun ready)] at h

/-- The endpoint's successful consistency result enters the shared record closer even
when its accumulated private weight is zero. -/
theorem endpoint_done (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (sg : Option Bool) (s : Stacks (Layout.Port r k (m*g))) (bits : List Bool) :
    StackRuns (replay (code P lib)) 1 (.block (.done sg),bits) s
      (.close sg RecordBuffer.close.body.entry,bits) s := .cons (.goto rfl) (.nil ..)

end TeamSite.Processor

end BorderVNP
end Computability
end OAI
