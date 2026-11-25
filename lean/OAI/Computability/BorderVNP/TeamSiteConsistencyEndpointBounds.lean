import OAI.Computability.BorderVNP.TeamSiteConsistencyExits
import OAI.Computability.BorderVNP.TeamSiteEvents

/-! # Bounds forced by each real processor's charged events

Every private read passes the burst cap before emitting. Every choice list in a private
call is the exact native run prefix, while a native branch takes one bit. These give the
burst and private-choice bounds needed to interpret physical histories as native paths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteConsistency

open VPVNP RAMTape TeamRAM TeamSite TeamTapeHandoff
open BurstRAM (Word)
variable {Q Γ : Type} {w p r k a m g d : ℕ}

/-- An admitted chunk checked the true read length at every instruction. -/
theorem chunk_bursts {P : TeamOpcode.State w p r → Instr w (TeamOpcode.State w p r)}
    {s z : TeamOpcode.State w p r} {c fin : Window w} {es : List (Event w)} (run : Chunk P s c es z fin) :
    ∀ e ∈ es, e.action.extra ≤ c.cap.val := by
  induction run with
  | nil => simp
  | cons _ _ _ hb _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | ht
    · exact hb
    · exact ih _ ht

/-- The cap survives all genuine physical handoffs and is checked on every real event. -/
theorem endpoint_bursts {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w} {lib : TeamOpcode.Macros w a}
    {H limit cap : Word w} {f : Frame w r} {rows : List (List (Event w))} {fs : List (Frame w r)}
    (h : EndpointRows P pub lib H limit cap f rows fs) :
    ∀ e ∈ rows.flatten, e.action.extra ≤ cap.val := by
  induction rows generalizing f fs with
  | nil => simp
  | cons es rows ih =>
    cases fs with
    | nil => exact False.elim h
    | cons out fs =>
      intro e he
      rcases List.mem_append.mp he with head | tail
      · have one := h.1
        cases f with
        | accepted elapsed => obtain ⟨rfl,_,_⟩ := one; contradiction
        | live word regs elapsed =>
          obtain ⟨_,pc,z,fin,_,run,_⟩ := one
          exact chunk_bursts run e head
      · exact ih h.2 _ tail

private theorem native_choices {T : TeamPrivateTape.Table Q d} {n state tapes bits result u}
    (run : TeamPrivateFragment.Run T n state tapes bits result u) : bits.length ≤ n := by
  induction run with
  | stop => simp
  | one _ _ ih => omega
  | two _ _ _ ih => simpa using ih

private theorem at_exit (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (bank : BurstRAM.PrivateRAM.LogConfig w p r)
    (out : TeamOpcode.Exit p r a) (bs : List Bool) (vs : List (Word w))
    {st : TeamOpcode.State w p r} {sg : Sign}
    (go : (out.action (TeamSiteEvents.macros lib fuel) bank).advance bs vs = some (st,sg)) :
    bs.length ≤ max 1 (fuel-1) := by
  cases out with
  | sign b pc => cases bs <;> cases vs <;> first | contradiction | simp
  | native cb =>
    cases cb <;> cases bs with
    | nil => simp
    | cons b bs => cases bs <;> cases vs <;> first | exact le_max_left _ _ | contradiction
  | call j addr len pc =>
    change (if vs.length = (bank.reg len).val then
      ((lib j).eval fuel vs bs).map (fun x => ((⟨pc,bank.reg⟩ : TeamOpcode.State w p r),x)) else none) = some _ at go
    split at go <;> try contradiction
    obtain ⟨out,he,_⟩ := Option.map_eq_some_iff.mp go
    obtain ⟨n,hn,_,_,run,_⟩ := ((lib j).eval_iff ..).mp he
    exact (native_choices run).trans ((show n ≤ fuel-1 by omega).trans (le_max_right _ _))

/-- The actual native clock bounds the exact choice tape of every ordinary or private
instruction on every locally replayed path. -/
theorem local_choice_bounds_pred (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) {start : TeamOpcode.State w p r} {es : List (Event w)}
    (path : Local (P.fetch pub (TeamSiteEvents.macros lib fuel)) start es) :
    ∀ e ∈ es, e.choices.length ≤ max 1 (fuel-1) := by
  induction es generalizing start with
  | nil => simp
  | cons e es ih =>
    obtain ⟨_,next,go,rest⟩ := path
    intro f hf
    rcases List.mem_cons.mp hf with rfl | ht
    · rw [← TeamOpcode.prepare_action] at go
      exact at_exit lib fuel _ _ _ _ go
    · exact ih rest _ ht

/-- The same private-prefix bound expressed directly in the evaluator's fuel. -/
theorem local_choice_bounds (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) {start : TeamOpcode.State w p r} {es : List (Event w)}
    (path : Local (P.fetch pub (TeamSiteEvents.macros lib fuel)) start es) :
    ∀ e ∈ es, e.choices.length ≤ max 1 fuel :=
  fun e he => (local_choice_bounds_pred P pub lib fuel path e he).trans (by omega)

end TeamSiteConsistency

end BorderVNP
end Computability
end OAI
