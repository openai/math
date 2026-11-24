import OAI.Computability.VPVNP.RegisterTable
import OAI.Computability.VPVNP.RoutineSpace

/-! # Calling a register table as a returning bit-stack routine

An `accept` opcode returns normally to the caller after completing the final
instruction dispatch. The return changes no register or stack, and the bound
on transient stack height also holds after linking.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.RegisterTable

open BurstRAM PrivateRAM UniversalCountStack

variable {w p r k : ℕ}

private def normal (T : Template p r k) (q : ISA.State T) : Bool :=
  match ISA.resume? T q with
  | some .accept => true
  | _ => false

/-- Run a register table from its entry label as a bit-stack subroutine that returns on its
accept callback. -/
def routine (T : Template p r k) : FiniteRoutine (ISA.Port r k) :=
  FiniteRoutine.ofStackCode (code T) id (ISA.entry T T.entry) (normal T)

private theorem normal_halts (T : Template p r k) (q : ISA.State T) (h : normal T q = true) :
    (code T q).returns = true := by
  rcases q with pc | sub | pc | cb <;> try contradiction
  cases cb <;> first | rfl | contradiction

private theorem accept_run (T : Template p r k) (pc : Fin p) (hpc : T.code pc = .accept)
    (pub : Fin k → Word w) (persistent : Word w) (reg : Fin r → Word w) :
    ∃ t ≤ ISA.prepareBound w 0+2,
      StackRuns (code T) t (ISA.entry T pc) (bank pub persistent reg)
        (ISA.callback T .accept) (bank pub persistent reg) := by
  let c : LogConfig w p r := ⟨pc,persistent,reg,[]⟩
  obtain ⟨t,ht,hr⟩ := ISA.dispatch_step T pub c
  have hl := hr.lift id Function.injective_id id (bank pub persistent reg) (target := code T)
    (by intro q hq; simp only [id_eq, code, ISA.resume_none_of_continuing T q hq]; cases ISA.code T q <;> rfl)
  have install (s : Stacks (ISA.Port r k)) : installStacks id (bank pub persistent reg) s = s := by
    funext a; exact installStacks_at Function.injective_id ..
  simp only [id_eq, install] at hl
  exact ⟨t, ht, by simpa [c, hpc, ISA.exitFor, ISA.post, ISA.configBank, bank] using hl⟩

/-- Add the final dispatch to a bounded run which reached an `accept` instruction. -/
theorem return_run {T : Template p r k} {n : ℕ} {pc : Fin p} (hpc : T.code pc = .accept)
    {pub : Fin k → Word w} {persistent : Word w} {R R' : Fin r → Word w}
    (hr : SpaceRun (code T) (w+(ISA.prepareBound w 0+3)) n (ISA.entry T T.entry)
      (bank pub persistent R) (ISA.entry T pc) (bank pub persistent R')) :
    ∃ t ≤ n+(ISA.prepareBound w 0+2), (routine T).BoundedRun (w+(ISA.prepareBound w 0+3)) t
      (bank pub persistent R) (bank pub persistent R') := by
  obtain ⟨m,hm,ht⟩ := accept_run T pc hpc pub persistent R'
  have bound := spaceRun_of_steps ht fun a => Nat.add_le_add (bank_length_le _ _ _ a)
    (hm.trans (Nat.le_succ _))
  let labels (q : ISA.State T) : Option (ISA.State T) := if normal T q then none else some q
  have hc (q : ISA.State T) (hq : (code T q).returns = false) :
      (routine T).body.standalone (labels q) = (code T q).rename id labels := by
    have hn : normal T q = false := by
      cases hh : normal T q with
      | false => rfl
      | true => exact Bool.noConfusion ((normal_halts T q hh).symm.trans hq)
    simp [labels, routine, FiniteRoutine.ofStackCode, FiniteRoutine.ofRoutine, Routine.standalone, Routine.close, hn]
  let s := bank pub persistent R
  have hl := (hr.trans bound).lift id Function.injective_id labels s
    (fun a outside => (outside a rfl).elim) hc
  have install (u : Stacks (ISA.Port r k)) : installStacks id s u = u := by
    funext a; exact installStacks_at Function.injective_id ..
  refine ⟨n+m, Nat.add_le_add_left hm _, ?_⟩
  change @SpaceRun (ISA.Port r k) (Option (ISA.State T)) _ (routine T).body.standalone _ (n+m) (some (ISA.entry T T.entry)) _ none _
  simpa only [install, labels, normal, ISA.resume_callback, ISA.resume_entry, Bool.false_eq_true,
    ite_false, ite_true] using hl

end RAMTape.RegisterTable

end VPVNP
end Computability
end OAI
