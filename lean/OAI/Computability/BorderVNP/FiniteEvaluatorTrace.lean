import OAI.Computability.BorderVNP.FiniteProcessorWeightEvents
import OAI.Computability.BorderVNP.RoutingISALink

/-! # The field product of the assembled word evaluator

The fetched program counter identifies the actual routine even when two private
opcodes read identical words and have identical signed outcomes. Recording those
identifiers during the native trace makes field-valued sequence composition exact.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamRAM FieldProcessor
open scoped BigOperators

variable {w p a r k : ℕ} {Q Γ : Type} {m g : ℕ} {F : Type*} [Field F]

/-- A marked event retains the resolved private routine identifier; ordinary
word operations and signs have no identifier. -/
abbrev Mark (a w : ℕ) := Option (Fin a) × TeamRAM.Event w

/-- The routine identifier actually selected by the current register bank. -/
def privateID : TeamOpcode.Exit p r a → Option (Fin a)
  | .call j .. => some j
  | _ => none

/-- Read an exact chronological instruction trace with the fetched private ID
attached to each event. The source machine determines each next PC. -/
def trace (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (mac : TeamOpcode.Macros w a) :
    TeamOpcode.State w p r → List (TeamRAM.Event w) → List (Mark a w)
  | _, [] => []
  | s, e :: es => match (P.fetch pub mac s).advance e.choices e.old with
    | none => []
    | some (z,_) => (privateID (TeamOpcode.prepare P pub s).1,e) :: trace P pub mac z es

/-- Field scalar of the actual selected routine on the true read words and
binary choices, or the ordinary signed field factor of a native operation. -/
noncomputable def value (lib : Fin a → TeamSite.Macro Q Γ m g) (ret : Returns Q Γ F m a) (fuel : ℕ) (x : Mark a w) : F :=
  match x.1 with
  | some j => (returned (lib j) (ret j) fuel x.2).getD 0
  | none => (x.2.sign.value : F)

variable {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w} {mac : TeamOpcode.Macros w a}

/-- Trace attachment commutes with concatenation from the native machine's
actual intermediate control and memory. -/
theorem trace_append {s mem es z mz} (walk : NativePrefix (P.fetch pub mac) s mem es z mz) (rest : List (TeamRAM.Event w)) :
    trace P pub mac s (es++rest) = trace P pub mac s es ++ trace P pub mac z rest := by
  induction walk with
  | nil => rfl
  | cons _ step _ ih => simp only [List.cons_append,trace,step,ih]

/-- The field path product in the assembled program equals the chronological
product of its resolved marks on any native prefix, including a zero private return. -/
theorem trace_value (lib : Fin a → TeamSite.Macro Q Γ m g) (ret : Returns Q Γ F m a) (fuel : ℕ) {s mem es z mz}
    (h : NativePrefix (P.fetch pub (TeamSiteEvents.macros lib fuel)) s mem es z mz) :
    pathProduct P pub lib ret fuel s es = ((trace P pub (TeamSiteEvents.macros lib fuel) s es).map (value lib ret fuel)).prod := by
  induction h with
  | nil => rfl
  | @cons s mem action bits next sg rest z mz _ step _ ih =>
    simp only [pathProduct,foldEvents,trace,step,List.map_cons,List.prod_cons] at ih ⊢
    rw [ih]
    cases tag : (TeamOpcode.prepare P pub s).1 <;> rfl

/-- Forgetting the IDs of a real marked trace recovers every original event. -/
theorem trace_events {s mem es z mz} (h : NativePrefix (P.fetch pub mac) s mem es z mz) :
    (trace P pub mac s es).map Prod.snd = es := by
  induction h with
  | nil => rfl
  | cons _ step _ ih => simp only [trace,step,List.map_cons,ih]

private def burstAction : TeamTranscript.Action (Word w) → Bool
  | .burst .. => true
  | .ordinary .. => false

/-- Whether a real physical event reads a private burst, including length zero. -/
def burst (e : TeamRAM.Event w) : Bool := burstAction e.action

private theorem native_ordinary (a : CallAction w (PrivateRAM.LogConfig w p r)) {x : TeamTranscript.Action (Word w)}
    (ok : (TeamOpcode.nativeAction a).action = some x) : burstAction x = false := by
  cases a with
  | finish z => cases z <;> contradiction
  | reject => contradiction
  | _ => obtain rfl := Option.some.inj ok; rfl

/-- Every actual burst mark has exactly its fetched routine ID. This includes
zero-length private reads, which ordinary charge-based filters would omit. -/
theorem trace_bursts {s mem es z mz} (h : NativePrefix (P.fetch pub mac) s mem es z mz) :
    ∀ x ∈ trace P pub mac s es, x.1.isSome = burst x.2 := by
  induction h with
  | nil => simp [trace]
  | @cons s mem act bs next sg rest z mz action step _ ih =>
    rw [trace,step]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · let e : TeamRAM.Event w := ⟨act,previous mem act,bs,sg⟩
      change (privateID (TeamOpcode.prepare P pub s).1).isSome = burst e
      rw [← TeamOpcode.prepare_action] at action
      cases tag : (TeamOpcode.prepare P pub s).1 with
      | native cb =>
        rw [tag] at action
        exact (native_ordinary (cb.action (TeamOpcode.prepare P pub s).2) action).symm
      | sign b pc =>
        rw [tag] at action
        have eq := Option.some.inj action
        change TeamTranscript.Action.ordinary none = act at eq
        simp only [burst,burstAction,e,← eq,privateID,Option.isSome_none]
      | call j addr len pc =>
        rw [tag] at action
        simp only [TeamOpcode.Exit.action,Instr.action] at action
        split at action <;> try contradiction
        have eq := Option.some.inj action
        simp only [burst,burstAction,e,← eq,privateID,Option.isSome_some]
    · exact ih x hx

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
