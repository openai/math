import OAI.Computability.BorderVNP.TeamSiteTimedBoundary
import OAI.Computability.BorderVNP.TransmissionSiteProcessor

/-! # The timed processor on its real wired slot input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP BurstRAM RAMTape UniversalMachine Filter
open TeamContraction TeamContraction.ProcessorSlots TeamTapeHandoff

variable {pc reg k routines m g R r w a : ℕ} {Q Γ : Type} [Fintype Q]
variable (P : TeamOpcode.Program pc reg k routines) (lib : Fin routines → Macro Q Γ m g) (mark : Fin routines → Γ)
local notation "physical" => machine P lib mark
local notation "body" => code P lib mark
local notation "input" => Layout.input (r := reg) (k := k) (d := (m+1)*g)

/-- The coefficient program compiled before the length and physical data are chosen
uses the true n^25 template and the remaining independently measured processor fuel. -/
theorem physical_value :
    ∀ᶠ n : ℕ in atTop, ∀ payload : List Bool, let raw := programPrefix physical ++ payload
      raw.length = n → signedCount raw.get =
        TeamStack.paths body (negative P) (n^36-TeamClocked.prepSteps 25 n)
          (.site Processor.start) (TrustedClock.installed input raw) :=
  TrustedClock.eventually_value input body (negative P) (.site Processor.start)

/-- The actual wire row, including the program's own description, supplies the complete
native prelude and reaches the first endpoint instruction with the same register, memory,
frame and sorting data as the ordinary site. Its private timer was constructed from
the length of this row, before any untrusted data or call was read. -/
theorem wired_start (S : SiteData R r reg k w a) (d link n e : ℕ)
    (fit : fitsWith physical reg k r w a R link n e) (hw : 0 < w) (hH : 2^e ≤ n)
    (u : Fin (R+1)) (j : Fin r) (pin : Fin d → Bool) (ext : Exterior R r link → Bool)
    (int : Wires.Edge r reg w e (w+1) → Bool) (ib hb sb : ℕ) :
    let G := wiringWith physical P S d link n e fit
    let F := G.processorFields u pin ext ib hb sb
    let data := F.row j
    let stride := entryStride physical (w+1) n (prefixCapacity r k reg w n+1+a) R link
    let base := j.val*stride
    let raw := List.ofFn (G.word pin ext int u j)
    let start := Label.site (P := P) (Q := Q) (m := m) (g := g) Processor.start
    2*(base+data.length) ≤ 2^(w+1) → 2*data.length ≤ 4*(2^e) →
    ∃ ticks bank, ticks ≤ Processor.preludeTime (entryBudget w n e data.length) reg k w (last j) ∧
      let physicalBank := installStacks TeamClocked.Port.user (TrustedClock.installed input raw) bank
      StackRuns (TrustedClock.code input body start) (TeamClocked.prepSteps 25 n+ticks)
        (.inl (TeamClocked.startup input 25).body.entry) (StackCompiler.labeledInput (.user input) raw)
        (.inr (.site (Processor.beginBlock (last j)))) physicalBank ∧
      MeterReady physicalBank (n^25) ∧ physicalBank ∘ TeamClocked.Port.user = bank ∧
      bank ∘ Processor.endpoint ∘ Endpoint.startup = TeamLocalClock.Startup.input
        (S.publicWords u) S.block S.limit S.burst (ingress (S.start P u) int j) ∧
      Work.Ready (by omega : 2 ≤ w+1) (2^e) (TeamTapeInputEmit.records (w+1) base data) (bank ∘ Layout.site) ∧
      Processor.RouteReady n (Wires.edgeEquiv int).2 (Wires.primary j) (Wires.secondary j) bank ∧
      bank .outgoing = egress int j ∧ bank .payload = [] ∧ bank .tmp = [] := by
  intro G F data stride base raw start room capacity
  obtain ⟨t,b,bound,pre,args,work,route,out,buffer,tmp⟩ :=
    sitePreludeWith physical P (fun j => extend (lib j) (mark j)) S d link n e fit hw hH u j pin ext int ib hb sb room capacity
  have earlier : ¬ TrustedClock.afterStartup P (Processor.beginBlock (Q := Q) (m := m+1) (g := g) (last j)) := by
    change ¬ False; exact not_false
  have inside := prelude_run P lib mark raw pre earlier
  let origin := TrustedClock.installed input raw
  have lift := inside.lift id Function.injective_id Sum.inr origin (target := TrustedClock.code input body start)
    (fun _ _ => rfl)
  have eqs (s : Stacks (TeamClocked.Port (Layout.Port reg k ((m+1)*g)))) : installStacks id origin s = s := by
    funext p; exact installStacks_at Function.injective_id origin s p
  simp only [eqs] at lift
  have run := (TrustedClock.prepare input body start raw).trans lift
  have len : raw.length = n := List.length_ofFn
  rw [len] at run
  have ready := (installed_ready (reg := reg) (k := k) (m := m) (g := g) raw).install b
  rw [len] at ready
  exact ⟨t,b,bound,run,ready,funext fun p => installStacks_at (fun _ _ => TeamClocked.Port.user.inj) origin b p,
    args,work,route,out,buffer,tmp⟩

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
