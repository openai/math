import OAI.Computability.BorderVNP.TeamSiteTimedDispatch

/-! # The physical private-call input and signed return on the site's ordinary stacks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP BurstRAM RAMTape TeamPrivateFragment
variable {p reg k routines m g : ℕ} {Q Γ : Type}
local notation "Bank" => Stacks (TeamClocked.Port (Layout.Port reg k ((m+1)*g)))

/-- The only additional state needed when a real burst has placed its probe values on
the usual private input stack. The private-template stack is the output of the trusted
site initialization and the three extra scratch stacks start empty. -/
def MeterReady (b : Bank) (N : ℕ) : Prop :=
  b (.tally .fuel) = List.replicate N true ∧ b (.reader .tmp) = [] ∧
    b (.reader .input) = [] ∧ b (.reader .size) = []

/-- Installing ordinary site stacks preserves the clock template and every reset
scratch word. -/
theorem MeterReady.install {b : Bank} {N : ℕ} (ready : MeterReady b N)
    (ordinary : Stacks (Layout.Port reg k ((m+1)*g))) :
    MeterReady (installStacks TeamClocked.Port.user b ordinary) N := by
  simpa [MeterReady,installStacks] using ready

/-- The template and reset scratch are supplied by measuring the entire actual raw word. -/
theorem installed_ready (raw : List Bool) :
    MeterReady (TrustedClock.installed (Layout.input (r := reg) (k := k) (d := (m+1)*g)) raw) (raw.length^25) := by
  have h := TrustedClock.installed_fields (Layout.input (r := reg) (k := k) (d := (m+1)*g)) raw
  exact ⟨h.2.2.1,h.2.2.2 _,h.2.2.2 _,h.2.2.2 _⟩

/-- At the callback, the ordinary burst words and trusted auxiliary state give the
whole input required by the private finite table, even for malformed probe data. -/
theorem ready_of_site {b : Bank} {N : ℕ} (bs : List Bool) (meter : MeterReady b N)
    (native : b ∘ TeamClocked.Port.user ∘ Layout.site ∘ privateTape = TeamPrivateInput.initial bs) :
    ∀ x, b (TeamPrivateMeterCall.wired reg k m g x) = TeamPrivateMeterCall.initial bs N x := by
  rintro (_ | _ | _ | _ | i)
  · exact meter.1
  · exact meter.2.1
  · exact meter.2.2.1
  · exact meter.2.2.2
  · exact congrFun native i

/-- Each actual native return leaves the true per-site template ready for the next
burst and empties the three reset scratch stacks. -/
theorem returned_ready (b : Bank) (N : ℕ) :
    MeterReady (installStacks (TeamPrivateMeterCall.wired reg k m g) b (TeamPrivateMeterCall.finished N)) N := by
  have read := installStacks_at (TeamPrivateMeterCall.wired_injective reg k m g) b (TeamPrivateMeterCall.finished N)
  exact ⟨read .template,read .copyScratch,read .meterRaw,read .meterScratch⟩

/-- All ordinary caller stacks equal the old bank with exactly its private workspace
cleared. This includes the data bit lanes and the timer's symbol lanes. -/
theorem return_user (b : Bank) (N : ℕ) :
    (installStacks (TeamPrivateMeterCall.wired reg k m g) b (TeamPrivateMeterCall.finished N)) ∘
        TeamClocked.Port.user =
      installStacks (Layout.site ∘ privateTape) (b ∘ TeamClocked.Port.user)
        (fun _ : TeamPrivateInput.NativePort (m+1) g => []) := by
  funext p
  by_cases h : ∃ i : TeamPrivateInput.NativePort (m+1) g, Layout.site (privateTape i) = p
  · obtain ⟨i,rfl⟩ := h
    exact (installStacks_at (TeamPrivateMeterCall.wired_injective reg k m g) b (TeamPrivateMeterCall.finished N)
      (.native i)).trans (installStacks_at (Layout.site_injective.comp privateTape_injective)
        (b ∘ TeamClocked.Port.user) (fun _ => []) i).symm
  · have absent : ∀ x, TeamPrivateMeterCall.wired reg k m g x ≠ .user p := by
      rintro (_|_|_|_|i) eq <;> first | exact h ⟨i,TeamClocked.Port.user.inj eq⟩ | cases eq
    have absent' : ∀ i : TeamPrivateInput.NativePort (m+1) g, (Layout.site ∘ privateTape) i ≠ p :=
      fun i eq => h ⟨i,eq⟩
    exact (installStacks_outside b (TeamPrivateMeterCall.finished N) absent).trans
      (installStacks_outside (b ∘ TeamClocked.Port.user) (fun _ => []) absent').symm

/-- A fixed native callback on any actual burst, including malformed words, consumes
a prefix of the supplied private choices, returns within the metered transition count,
and restores the physical clock for subsequent bursts. -/
theorem run_any (P : TeamOpcode.Program p reg k routines) (lib : Fin routines → Macro Q Γ m g)
    (mark : Fin routines → Γ) (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j)
    (last : Bool) (sg : Option Bool) (j : Fin routines) (pc : Fin p) {w : ℕ} (vs : List (Word w))
    (N : ℕ) (supply : TeamSiteChoices.Supply) (suffix : List Bool) (b : Bank) (meter : MeterReady b N)
    (burst : b ∘ TeamClocked.Port.user ∘ Layout.site ∘ privateTape =
      TeamPrivateInput.initial (TeamPrivateCall.inputBits vs)) :
    ∃ used steps, used ≤ steps ∧ steps < N+1 ∧ ∃ (out : Option Bool) (tracks : Fin ((m+1)*g) → TeamPrivateTape.Track),
      (lib j).timedEval (mark j) N vs (TeamSiteChoices.takeBits supply used) = some (TeamPrivateCall.sign out) ∧
      let endBank := installStacks (TeamPrivateMeterCall.wired reg k m g) b (TeamPrivateMeterCall.finished N)
      StackRuns (replay (code P lib mark)) (TeamPrivateMeterCall.steps (m := m) (g := g) (TeamPrivateCall.inputBits vs) N steps tracks+2)
        (.site (.block (.loop last (.privateCall sg j pc (.load .start)))),TeamSiteChoices.takeBits supply used++suffix) b
        (.site (.block (.loop last (.privateCall sg j pc (.result out)))),suffix) endBank ∧ MeterReady endBank N := by
  obtain ⟨u,n,hu,hn,out,tr,run,eval⟩ := (lib j).timed_prefix_run (mark j) (distinct j) N vs supply
  exact ⟨u,n,hu,hn,out,tr,eval,run_call P lib mark last sg j pc (TeamPrivateCall.inputBits vs) N run suffix b
    (ready_of_site _ meter burst), returned_ready b N⟩

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
