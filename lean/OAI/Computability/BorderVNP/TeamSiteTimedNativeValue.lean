import OAI.Computability.BorderVNP.TeamNativeNonzeroCongr
import OAI.Computability.BorderVNP.TeamSiteTimedReplay
import OAI.Computability.BorderVNP.TeamSiteEvents
import OAI.Computability.BorderVNP.TeamSiteConsistencyPaths

/-! # Equality of the metered and original signed RAM values on every initialized header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Macro

open VPVNP BurstRAM TeamRAM TeamContraction
variable {w p r k a m g : ℕ} {Q Γ : Type}

/-- Substituting the trusted timed library in the actual ISA fetch preserves every
nonzero advance, including on old words guessed from a malformed interval. -/
theorem timedFetch_agreement (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → TeamSite.Macro Q Γ m g) (mark : Fin a → Γ)
    (hmark : ∀ j, (lib j).alphabet.blank ≠ mark j) (N : ℕ) (s : TeamOpcode.State w p r) :
    (P.fetch pub (fun j => (lib j).timedEval (mark j) N) s).NonzeroAgreement
      (P.fetch pub (TeamSiteEvents.macros lib (N+1)) s) := by
  rw [← TeamOpcode.prepare_action,← TeamOpcode.prepare_action]
  cases (TeamOpcode.prepare P pub s).1 with
  | native cb | sign b pc => exact ⟨Iff.rfl,rfl,fun _ _ _ _ _ => Iff.rfl⟩
  | call j addr len pc =>
    refine ⟨by simp [TeamOpcode.Exit.action],rfl,?_⟩
    intro bs vs next sign hn
    simp only [TeamOpcode.Exit.action,Instr.advance]
    split
    · simp only [Option.map_eq_some_iff,Prod.mk.injEq]
      constructor <;> rintro ⟨sg,hval,hnext,rfl⟩
      · exact ⟨sg,((lib j).timedEval_signed (mark j) (hmark j) N vs bs sg hn).mp hval,hnext,rfl⟩
      · exact ⟨sg,((lib j).timedEval_signed (mark j) (hmark j) N vs bs sg hn).mpr hval,hnext,rfl⟩
    · rfl

/-- For every common input, initial state and chronological resource cutoff, the actual
timed library has the original native value at the inclusive private deadline. -/
theorem nativeValue_timed (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → TeamSite.Macro Q Γ m g) (mark : Fin a → Γ)
    (hmark : ∀ j, (lib j).alphabet.blank ≠ mark j) (N : ℕ)
    (start : TeamOpcode.State w p r) (size : ℕ) (header : ℕ → Word w) (ticks burst clock : ℕ) :
    nativeValue ⟨P.fetch pub (fun j => (lib j).timedEval (mark j) N),start,size,header⟩ ticks burst clock =
      nativeValue ⟨P.fetch pub (TeamSiteEvents.macros lib (N+1)),start,size,header⟩ ticks burst clock := by
  apply nativeValue_congr_nonzero <;> try rfl
  exact timedFetch_agreement P pub lib mark hmark N

/-- Applied to the actual processor memory image, both sides use the same flattened
input rows and the same generated header, logical ticks, burst cap and private-choice bound. -/
theorem nativeValue_setup_timed {teams e : ℕ} (G : TeamSiteConsistency.Setup teams w p r k a e)
    (lib : Fin a → TeamSite.Macro Q Γ m g) (mark : Fin a → Γ)
    (hmark : ∀ j, (lib j).alphabet.blank ≠ mark j) (N : ℕ)
    (hlib : G.lib = fun j => (lib j).timedEval (mark j) N) :
    nativeValue G.machine G.limit.val G.cap.val G.privateClock =
      nativeValue {G.machine with program := G.program.fetch G.pub (TeamSiteEvents.macros lib (N+1))}
        G.limit.val G.cap.val G.privateClock := by
  apply nativeValue_congr_nonzero <;> try rfl
  intro s
  change (G.program.fetch G.pub G.lib s).NonzeroAgreement _
  rw [hlib]
  exact timedFetch_agreement G.program G.pub lib mark hmark N s

end TeamSite.Macro

end BorderVNP
end Computability
end OAI
