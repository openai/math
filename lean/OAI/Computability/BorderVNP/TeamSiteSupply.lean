import OAI.Computability.BorderVNP.TeamSiteSupplyGuard

/-! # Finite processor executions on arbitrary choice supplies

One local processor follows its signed RAM instructions until acceptance, greedy
handoff or rejection. Every successful instruction reduces the local countdown
by at least one. This gives a finite execution on every infinite choice supply,
including branches of signed private routines that return zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.SupplyRun

open VPVNP RAMTape BurstRAM TeamSiteEvents TeamSiteChoices

variable {Q Γ : Type} {w p r k a m g : ℕ}

/-- End of a processor's local execution. A handoff retains the final state's PC. -/
inductive Verdict where
  | accepted | handoff | reject
  deriving DecidableEq

/-- Exact guarded instruction history for a single processor on one branch supply.
The final state/window are the ones reached after the listed successful events. -/
inductive Run (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) :
    TeamOpcode.State w p r → Window w → Supply → List (TeamRAM.Event w) →
    TeamOpcode.State w p r → Window w → Verdict → Prop
  | accept {s c supply} (terminal : exit P pub s c = .accepted) :
      Run P pub lib fuel s c supply [] s c .accepted
  | handoff {s c supply} (refused : exit P pub s c = .handoff s.pc) :
      Run P pub lib fuel s c supply [] s c .handoff
  | rejectGuard {s c supply} (refused : exit P pub s c = .reject) :
      Run P pub lib fuel s c supply [] s c .reject
  | rejectCallback {s c supply} (admit : exit P pub s c = .callback (TeamOpcode.prepare P pub s).1)
      (failed : decode P pub lib fuel s c supply = none)
      (reason : Invalid (TeamOpcode.prepare P pub s).2 (TeamOpcode.prepare P pub s).1) :
      Run P pub lib fuel s c supply [] s c .reject
  | cons {s c supply z es last fin verdict}
      (admit : exit P pub s c = .callback (TeamOpcode.prepare P pub s).1)
      (decoded : decode P pub lib fuel s c supply = some z)
      (fits : c.Fits z.event.action.extra)
      (tail : Run P pub lib fuel z.state (c.charge z.event.action.extra) (drop supply z.bits.length) es last fin verdict) :
      Run P pub lib fuel s c supply (z.event::es) last fin verdict

/-- The generated prepared event agrees with the original RAM fetch and its advance.
The next processor instruction gets the suffix following the complete event spelling. -/
theorem decode_iff (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (s : TeamOpcode.State w p r) (c : Window w)
    (supply : Supply) (z : Next w p r) :
    decode P pub lib fuel s c supply = some z ↔
      (P.fetch pub (macros lib fuel) s).action = some z.event.action ∧
      (P.fetch pub (macros lib fuel) s).advance z.event.choices z.event.old = some (z.state,z.event.sign) ∧
      z.event.action.extra ≤ c.cap.val ∧ Prefix supply z.bits := by
  rw [decode, generate_iff, TeamOpcode.prepare_action]

/-- Every supplied stream has a finite local execution. The native private clock
is required only on word lists admitted by the processor's burst cap. -/
theorem exists_run (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (s : TeamOpcode.State w p r) (c : Window w)
    (supply : Supply) (safe : c.Safe)
    (bounded : ∀ j vs, vs.length ≤ c.cap.val → (lib j).bounded fuel (vs : List (Word w))) :
    ∃ es last fin verdict, Run P pub lib fuel s c supply es last fin verdict := by
  cases hg : exit P pub s c with
  | accepted => exact ⟨_,_,_,_,.accept hg⟩
  | reject => exact ⟨_,_,_,_,.rejectGuard hg⟩
  | handoff pc => obtain rfl := handoff_pc P pub s c pc hg; exact ⟨_,_,_,_,.handoff hg⟩
  | callback out =>
    obtain ⟨rfl, fits, _⟩ := callback_info P pub s c out hg
    cases hd : decode P pub lib fuel s c supply with
    | none => exact ⟨_,_,_,_,.rejectCallback hg hd (invalid_of_none P pub lib fuel s c supply hg hd bounded)⟩
    | some z =>
      obtain ⟨ha,_,_,_⟩ := (decode_iff ..).mp hd
      rw [opcodeBurst_eq P pub (macros lib fuel) s z.event.action ha] at fits
      have charged := c.charged_values z.event.action.extra safe fits
      obtain ⟨es,last,fin,v,tail⟩ := exists_run P pub lib fuel z.state (c.charge z.event.action.extra)
        (drop supply z.bits.length) charged.2.2.2 bounded
      exact ⟨_,last,fin,v,.cons hg hd fits tail⟩
termination_by c.block.val
decreasing_by
  rw [charged.1]
  have := fits.1
  omega

variable {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w} {lib : Fin a → Macro Q Γ m g}
  {fuel : ℕ} {s last : TeamOpcode.State w p r} {c fin : Window w} {supply : Supply}
  {es : List (TeamRAM.Event w)} {verdict : Verdict}

/-- The events before the terminal verdict form a genuine guarded signed RAM chunk. -/
theorem Run.chunk (run : Run P pub lib fuel s c supply es last fin verdict) :
    Chunk (P.fetch pub (macros lib fuel)) s c es last fin := by
  induction run with
  | accept | handoff | rejectGuard | rejectCallback => exact .nil ..
  | cons _ decoded fits _ ih =>
    obtain ⟨ha,hn,hcap,_⟩ := (decode_iff ..).mp decoded
    exact .cons ha hn fits hcap ih

/-- The successful instruction history consumes exactly one finite initial segment.
The terminating refusal or failure consumes no additional choices. -/
theorem Run.prefix (run : Run P pub lib fuel s c supply es last fin verdict) :
    Prefix supply (chunkBits es) := by
  induction run with
  | accept | handoff | rejectGuard | rejectCallback => rfl
  | cons _ decoded _ _ ih =>
    exact (prefix_append ..).mpr ⟨((decode_iff ..).mp decoded).2.2.2,ih⟩

end TeamSite.SupplyRun

end BorderVNP
end Computability
end OAI
