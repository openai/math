import OAI.Computability.BorderVNP.DiagonalNativeUnitStartup
import OAI.Computability.BorderVNP.FiniteProcessorWeightEvents

/-! # The field product along the zero-tag unit trace of Lemma 8.3

A successful unit trace consists only of ordinary word instructions. In particular
it cannot visit even a private call of length zero. Thus arbitrary terminal values
of the private routines make no contribution to this branch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamRAM FieldProcessor
open scoped Classical

variable {w : ℕ}

/-- The architectural action of every event in a deterministic fragment is ordinary. -/
theorem ordinary_of_deterministic {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (r : Runs pub mac c s m es t mt) (hd : c.deterministic = true) :
    ∀ e ∈ es, ∃ probe, e.action = .ordinary probe := by
  induction r with
  | @atom c s m a t sg bits hc ha step =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    change ∃ probe, a = .ordinary probe
    cases c <;> try cases hc <;> try cases hd <;> try exact ⟨_,(Option.some.inj ha).symm⟩
    case atom.binary.refl.refl op dst x y =>
      by_cases hz : (op = .div ∨ op = .mod) ∧ s y = 0 <;> simp [Code.atom,hz,Instr.action] at ha
      exact ⟨_,ha.symm⟩
  | seq first second ih ih' =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hd
    intro e he
    exact (List.mem_append.mp he).elim (ih ha e) (ih' hb e)
  | ifEq h ih | ifLt h ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hd
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨none, rfl⟩
    · exact ih (by split <;> assumption) e he
  | choose => contradiction
  | whileDone h =>
    intro e he
    obtain rfl := List.mem_singleton.mp he
    exact ⟨none,rfl⟩
  | whileStep guard body tail ih ih' =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨none,rfl⟩
    · exact (List.mem_append.mp he).elim (ih hd e) (ih' hd e)

variable {Q Γ : Type} {F : Type*} [Field F] {p r k a m g : ℕ}

/-- On a positive ordinary chronological path, the adaptive path product over a
field is one, regardless of the library of terminal field returns. -/
theorem pathProduct_ordinary_positive (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m a) (fuel : ℕ)
    (s : TeamOpcode.State w p r) (es : List (TeamRAM.Event w))
    (steps : Local (P.fetch pub (TeamSiteEvents.macros lib fuel)) s es)
    (ordinary : ∀ e ∈ es, ∃ probe, e.action = .ordinary probe)
    (positive : ∀ e ∈ es, e.sign = .plus) :
    pathProduct P pub lib ret fuel s es = 1 := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨act, next, adv, rest⟩ := steps
    obtain ⟨pr,hpr⟩ := ordinary e List.mem_cons_self
    have hs := positive e List.mem_cons_self
    have tail := ih next rest (fun v hv => ordinary v (List.mem_cons_of_mem _ hv))
      (fun v hv => positive v (List.mem_cons_of_mem _ hv))
    change foldEvents P pub lib fuel (eventWeight lib ret fuel) next es = 1 at tail
    simp only [pathProduct,foldEvents,adv,tail,mul_one]
    cases tag : (TeamOpcode.prepare P pub s).1 with
    | native | sign => simp [eventWeight, hs, Sign.value]
    | call j address length pc =>
      rw [← TeamOpcode.prepare_action,tag,hpr] at act
      simp only [TeamOpcode.Exit.action, Instr.action] at act
      split at act <;> simp at act

/-- On a genuine zero reference tag, the native field weight of every accepting
trace of the assembled program is the unit of the field. -/
theorem startup_unit_pathProduct (eval : Code) {pub : Arg → Word w} {s mm es t mt}
    (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ)
    (run : Runs pub (TeamSiteEvents.macros lib fuel) (withStartup eval) s mm es t mt)
    (unitRun : Runs pub (TeamSiteEvents.macros lib fuel) (withStartup unit) s mm es t mt) :
    pathProduct (withStartup eval).program pub lib ret fuel ⟨0,s⟩ es = 1 :=
  pathProduct_ordinary_positive _ _ _ _ _ _ _ (execute_spec run.execute).1
    (ordinary_of_deterministic unitRun (by decide)) (fun e he => (unitRun.unsigned_events (by decide) e he).2)

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
