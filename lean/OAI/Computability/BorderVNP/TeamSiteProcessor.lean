import OAI.Computability.BorderVNP.TeamSiteLayoutFrames
import OAI.Computability.BorderVNP.TeamSiteEndpoint
import OAI.Computability.BorderVNP.TeamClockedProgram

/-! # A single signed universal program for one processor

The program begins with the raw input alone. It initializes the local memory records,
loads the fixed parameters, extracts the physical handoff fields, and runs the signed
RAM block. On a successful endpoint check it closes the same record buffer and verifies
both sorting lanes that the public metadata assigns to the processor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor

open VPVNP BurstRAM RAMTape Layout

variable {Q Γ : Type} {p r k a m g d : ℕ}

/-- The processor endpoint sees the initializer's record buffer through its normal RAM ports. -/
def endpoint : Endpoint.Port r k d → Layout.Port r k d
  | .site p => site p
  | .incoming => .incoming
  | .outgoing => .outgoing
  | .width => .width
  | .tag => .tag
  | .pc => .pc
  | .tmp => .tmp
  | .payload => .payload

/-- Frame scratch and RAM ports are all distinct after the processor installation. -/
theorem endpoint_injective : Function.Injective (endpoint (r := r) (k := k) (d := d)) := by
  intro i j h
  cases i with
  | site i =>
    cases j with
    | site j => exact congrArg _ (site_injective h)
    | _ =>
      cases i <;> first | contradiction | (rename_i u; cases u <;> first | contradiction |
        (rename_i v; cases v <;> contradiction))
  | _ =>
    cases j <;> first | rfl | contradiction | (rename_i i; cases i <;> first | contradiction |
      (rename_i u; cases u <;> first | contradiction | (rename_i v; cases v <;> contradiction)))

/-- The source of the incoming frame at the given role. -/
abbrev incomingSource (first : Bool) := if first then FrameSource.literal else FrameSource.previous

/-- Every phase and every branch label is independent of the word width and input length. -/
inductive Label (P : TeamOpcode.Program p r k a) (Q : Type) (m g : ℕ) where
  | initialize (q : TeamTapeInput.Entry.program.State)
  | parameters (q : (TeamPublicStartup.program (k+8)).State)
  | measure (q : (frameMarks (r := r) (k := k) (d := m*g)).State)
  | first
  | last (first : Bool)
  | incoming (first last : Bool) (q : (takeFrame (r := r) (k := k) (d := m*g) (incomingSource first)).State)
  | outgoing (q : (takeFrame (r := r) (k := k) (d := m*g) .next).State)
  | block (q : Endpoint.Label P Q m g)
  | close (sign : Option Bool) (q : RecordBuffer.close.State)
  | sort (sign : Option Bool) (q : Option TeamTapeInputRoute.Verify.processor.State)
  | reject

noncomputable instance (P : TeamOpcode.Program p r k a) [Fintype Q] : Fintype (Label P Q m g) := derive_fintype% _

/-- Enter the shared predecessor decoder even on the first site, where the decoded
frame comes from the fixed literal. -/
def beginBlock {P : TeamOpcode.Program p r k a} (last : Bool) : Label P Q m g :=
  .block (.startup last (TeamLocalClock.Startup.entry p r))

/-- After ingress the last owner begins its block directly. Other owners read the outgoing link. -/
def afterReceive {P : TeamOpcode.Program p r k a} (last : Bool) : Label P Q m g :=
  if last then beginBlock true else .outgoing (takeFrame .next).body.entry

/-- A legitimate zero-weight path still executes the physical verifier to its terminal
label. At its accepting sorter row the universal coefficient receives zero. -/
def withWeight {K S : Type} (sg : Option Bool) (C : StackCode K S) : StackCode K S :=
  fun q => match C q with
  | .halt valid => .halt (valid && sg.isSome)
  | op => op

/-- Fixed finite table of the complete local processor. Every sign is read from the
path's actual endpoint result and carried to both physical sorting lanes. -/
noncomputable def code (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) :
    StackCode (Layout.Port r k (m*g)) (Label P Q m g)
  | .initialize q => (TeamTapeInput.Entry.program.body.code q).rename entry
      (fun z => z.elim (.parameters (TeamPublicStartup.program (k+8)).body.entry) .initialize)
  | .parameters q => ((TeamPublicStartup.program (k+8)).body.code q).rename publicPort
      (fun z => z.elim (.measure frameMarks.body.entry) .parameters)
  | .measure q => (frameMarks.body.code q).rename id (fun z => z.elim .first .measure)
  | .first => .pop metadata (fun b => b.elim .reject .last)
  | .last first => .pop metadata (fun b => b.elim .reject (fun last =>
      .incoming first last (takeFrame (incomingSource first)).body.entry))
  | .incoming first last q => ((takeFrame (incomingSource first)).body.code q).rename id
      (fun z => z.elim (afterReceive last) (.incoming first last))
  | .outgoing q => ((takeFrame FrameSource.next).body.code q).rename id
      (fun z => z.elim (beginBlock false) .outgoing)
  | .block (.done sg) => .goto (.close sg RecordBuffer.close.body.entry)
  | .block q => (Endpoint.code P lib q).rename endpoint .block
  | .close b q => (RecordBuffer.close.body.code q).rename buffer
      (fun z => z.elim (.sort b (some TeamTapeInputRoute.Verify.processor.body.entry)) (.close b))
  | .sort b q => (withWeight b TeamTapeInputRoute.Verify.processor.body.standalone q).rename Layout.Port.route (.sort b)
  | .reject => .halt false

/-- The only successful halts lie in the final sorter. Each retains the accumulated sign. -/
def negative {P : TeamOpcode.Program p r k a} : Label P Q m g → Bool
  | .sort b _ => b.getD false
  | _ => false

/-- The raw initialization routine always executes first. -/
def start {P : TeamOpcode.Program p r k a} : Label P Q m g := .initialize TeamTapeInput.Entry.program.body.entry

/-- Signed universal tape program carried by the physical literal itself. -/
noncomputable def machine [Fintype Q] (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) :
    UniversalMachine.Program := TeamClocked.machine input 36 (code P lib) negative start

/-- The whole processor on its own prefix is physically clocked at the paper's
universal bound, even for a malformed register frame or sorting message. -/
theorem eventually_value [Fintype Q] (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ payload : List Bool,
      let raw := UniversalMachine.programPrefix (machine P lib) ++ payload
      raw.length = n → signedCount raw.get =
        TeamStack.paths (code P lib) negative (n^36) start (StackCompiler.labeledInput input raw) :=
  TeamClocked.eventually_prefix_value input 36 (by decide) (by decide) (code P lib) negative start

end TeamSite.Processor

end BorderVNP
end Computability
end OAI
