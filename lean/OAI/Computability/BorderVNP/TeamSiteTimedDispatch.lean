import OAI.Computability.BorderVNP.TeamSiteClockPhases
import OAI.Computability.BorderVNP.TeamSiteTimedMacro
import OAI.Computability.BorderVNP.TeamPrivateMeterCall

/-! # The trusted native macro call inside the actual signed site table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP BurstRAM RAMTape UniversalMachine TeamPrivateFragment TeamPrivateTape

variable {p reg k routines m g : ℕ} {Q Γ : Type}

/-- The ordinary site control and stack bank are widened by the timer's one symbol tape.
Its initial bits are installed only by the private call's trusted reset code. -/
noncomputable def extend (M : Macro Q Γ m g) (mark : Γ) : Macro Q Γ (m+1) g :=
  ⟨M.alphabet,M.digit,M.inputTape.succ,TeamPrivateTimeout.table M.alphabet.blank mark M.table,M.start⟩

/-- The outer site states and the private call's real finite control have distinct labels.
The return state remembers exactly the signed continuation and the post-probe program counter. -/
inductive Label (P : TeamOpcode.Program p reg k routines) (Q : Type) (m g : ℕ) where
  | site (q : Processor.Label P Q (m+1) g)
  | call (last : Bool) (sign : Option Bool) (routine : Fin routines) (pc : Fin p)
      (q : TeamPrivateMeterCall.Control Q m g)

noncomputable instance (P : TeamOpcode.Program p reg k routines) [Fintype Q] : Fintype (Label P Q m g) :=
  derive_fintype% _

variable (P : TeamOpcode.Program p reg k routines) (lib : Fin routines → Macro Q Γ m g)
variable (mark : Fin routines → Γ)

/-- Actual call-site program. The burst callback has already populated its physical input
stack when it reaches `.load .start`. All private returns pass through the original signed
resume code, including timeout and zero-weight results. -/
noncomputable def code : StackCode (TeamClocked.Port (Layout.Port reg k ((m+1)*g))) (Label P Q m g)
  | .site (.block (.loop last (.privateCall sg j pc (.load .start)))) =>
    .goto (.call last sg j pc (.load .start))
  | .site q => (Processor.code P (fun j => extend (lib j) (mark j)) q).rename TeamClocked.Port.user Label.site
  | .call last sg j pc (.result out) => .goto (.site (.block (.loop last (.privateCall sg j pc (.result out)))))
  | .call last sg j pc q => (TeamPrivateMeterCall.code (lib j) (mark j) q).rename
      (TeamPrivateMeterCall.wired reg k m g) (.call last sg j pc)

/-- The finite sign of a completed timed processor, inherited from its real sorter. -/
def negative : Label P Q m g → Bool
  | .site q => Processor.negative q
  | .call .. => false

/-- The fixed universal-machine description actually placed before the processor input.
Its clock preparation reads the word containing this very description. -/
noncomputable def machine [Fintype Q] : Program :=
  TrustedClock.machine Layout.input (code P lib mark) (negative P) (.site Processor.start)

/-- Every ordinary site instruction except entry to a private macro retains its original
continuations and stack actions in the larger physical bank. -/
theorem site_row (q : Processor.Label P Q (m+1) g)
    (ordinary : ∀ last sg j pc, q ≠ .block (.loop last (.privateCall sg j pc (.load .start)))) :
    code P lib mark (.site q) =
      (Processor.code P (fun j => extend (lib j) (mark j)) q).rename TeamClocked.Port.user Label.site := by
  cases q <;> try rfl
  rename_i q
  cases q <;> try rfl
  rename_i last q
  cases q <;> try rfl
  rename_i sg j pc q
  cases q <;> try rfl
  rename_i q
  cases q <;> first | rfl | exact False.elim (ordinary last sg j pc rfl)

/-- At the actual burst continuation the timed dispatcher, loader, native reset,
clocked symbol-table execution and signed return are one replay, including the
private choice suffix and restored unary template. -/
theorem run_call (last : Bool) (sg : Option Bool) (j : Fin routines) (pc : Fin p)
    (bs : List Bool) (N : ℕ) {steps choices out tracks}
    (native : Run (trackTable (lib j).alphabet (TeamPrivateTimeout.table (lib j).alphabet.blank (mark j) (lib j).table))
      steps (lib j).start (TeamPrivateMeterCall.timedInput (lib j) (mark j) bs N) choices out tracks)
    (suffix : List Bool) (base : Stacks (TeamClocked.Port (Layout.Port reg k ((m+1)*g))))
    (ready : ∀ a, base (TeamPrivateMeterCall.wired reg k m g a) = TeamPrivateMeterCall.initial bs N a) :
    StackRuns (replay (code P lib mark)) (TeamPrivateMeterCall.steps bs N steps tracks + 2)
      (.site (.block (.loop last (.privateCall sg j pc (.load .start)))),choices++suffix) base
      (.site (.block (.loop last (.privateCall sg j pc (.result out)))),suffix)
      (installStacks (TeamPrivateMeterCall.wired reg k m g) base (TeamPrivateMeterCall.finished N)) := by
  let label := Label.call (P := P) (Q := Q) (m := m) (g := g) last sg j pc
  have call := TeamPrivateMeterCall.run_wired (lib j) (mark j) bs N native suffix (code P lib mark) label base ready
    (fun q h => by cases q <;> first | rfl | simp [TeamPrivateMeterCall.code] at h)
  have enter : StackStep (replay (code P lib mark))
      (.site (.block (.loop last (.privateCall sg j pc (.load .start)))),choices++suffix) base
      (label (.load .start),choices++suffix) base := .goto rfl
  let endBank := installStacks (TeamPrivateMeterCall.wired reg k m g) base (TeamPrivateMeterCall.finished N)
  have leave : StackStep (replay (code P lib mark)) (label (.result out),suffix) endBank
      (.site (.block (.loop last (.privateCall sg j pc (.result out)))),suffix) endBank := .goto rfl
  exact .cons enter (call.trans (.cons leave (.nil ..)))

/-- All pre-loop physical site steps can be replayed after the native n^25 startup.
The old stack bank is embedded without modifying the trusted template. -/
theorem prelude_run {t q bank} (raw : List Bool)
    (old : StackRuns (Processor.code P (fun j => extend (lib j) (mark j))) t Processor.start
      (StackCompiler.labeledInput Layout.input raw) q bank) (early : ¬ TrustedClock.afterStartup P q) :
    let installed := TrustedClock.installed (Layout.input (r := reg) (k := k) (d := (m+1)*g)) raw
    StackRuns (code P lib mark) t (.site Processor.start) installed (.site q)
      (installStacks TeamClocked.Port.user installed bank) := by
  intro installed
  have run := TrustedClock.lift_prelude P _ (code P lib mark) TeamClocked.Port.user
    (fun _ _ => TeamClocked.Port.user.inj) Label.site installed (fun z hz =>
      site_row P lib mark z fun last sg j pc eq => hz (eq ▸ (by trivial))) old early
  have init := (TrustedClock.installed_fields (Layout.input (r := reg) (k := k) (d := (m+1)*g)) raw).1
  have same := installStacks_eq (ports := TeamClocked.Port.user) (fun _ _ => TeamClocked.Port.user.inj) installed _ (congrFun init)
  rwa [same] at run

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
