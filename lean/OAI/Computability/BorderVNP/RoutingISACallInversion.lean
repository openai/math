import OAI.Computability.BorderVNP.RoutingISACallModel

/-! # Inverting private call instructions and directory tests -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- A successful structured sequence has a split into its exact component histories. -/
theorem seq_split {a b : Code} {s m es t mt}
    (h : Runs pub macros (.seq a b) s m es t mt) :
    ∃ gs u mu hs, es = gs ++ hs ∧ Runs pub macros a s m gs u mu ∧ Runs pub macros b u mu hs t mt := by
  cases h with
  | atom ha _ _ => cases ha
  | seq first second => exact ⟨_,_,_,_,rfl,first,second⟩

/-- The equality test consumes exactly one tick and runs its actual branch. -/
theorem eq_split {x y : Reg} {a b : Code} {s m es t mt}
    (h : Runs pub macros (.ifEq x y a b) s m es t mt) :
    ∃ gs, es = tick w :: gs ∧ Runs pub macros (if s x = s y then a else b) s m gs t mt := by
  cases h with
  | atom ha _ _ => cases ha
  | ifEq hr => exact ⟨_,rfl,hr⟩

/-- Running the private-call opcode neither writes memory nor alters its bank.
It records exactly one accepting path of the addressed private computation. -/
theorem private_iff {j : Macro} {a l : Reg} {s m es t mt} :
    Runs pub macros (.call j a l) s m es t mt ↔
      let act : TeamTranscript.Action (Word w) := .burst (s a).val (s l).val
      (s a).val + (s l).val ≤ 2^w ∧ t = s ∧ mt = m ∧ ∃ o : Outcome,
        macros j (TeamRAM.previous m act) o.1 = some o.2 ∧
        es = [⟨act, TeamRAM.previous m act, o.1, o.2⟩] := by
  dsimp only
  constructor
  · intro run
    cases run with
    | @atom _ _ _ act t sign bits _ ha hs =>
      simp only [Code.atom, TeamRAM.Instr.action] at ha
      split at ha
      next fits =>
        cases Option.some.inj ha
        simp only [TeamRAM.Instr.advance, Code.atom, TeamRAM.previous, List.length_ofFn,
          ite_true, Option.map_eq_some_iff] at hs
        obtain ⟨o,ho,h⟩ := hs
        cases h
        exact ⟨fits,rfl,rfl,⟨bits,_⟩,ho,rfl⟩
      next => contradiction
  · rintro ⟨fits,rfl,rfl,⟨bits,sign⟩,ho,rfl⟩
    apply Runs.atom rfl
    · simp [Code.atom, TeamRAM.Instr.action, fits]
    · simp [Code.atom, TeamRAM.Instr.advance, TeamRAM.previous] at ho ⊢
      exact ho

/-- For a true guard a returned loop trace splits into one body and its tail. -/
theorem while_next {x y : Reg} {body : Code} {s m es t mt}
    (run : Runs pub macros (.whileLt x y body) s m es t mt) (guard : s x < s y) :
    ∃ gs u mu hs, es = tick w :: (gs ++ hs) ∧ Runs pub macros body s m gs u mu ∧
      Runs pub macros (.whileLt x y body) u mu hs t mt := by
  cases run with
  | atom ha _ _ => cases ha
  | whileDone => contradiction
  | whileStep _ first tail => exact ⟨_,_,_,_,rfl,first,tail⟩

/-- A false guard ends the loop immediately with a single unsigned tick. -/
theorem while_last {x y : Reg} {body : Code} {s m es t mt}
    (run : Runs pub macros (.whileLt x y body) s m es t mt) (guard : ¬ s x < s y) :
    es = [tick w] ∧ t = s ∧ mt = m := by
  cases run with
  | atom ha _ _ => cases ha
  | whileDone => exact ⟨rfl,rfl,rfl⟩
  | whileStep => contradiction

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
