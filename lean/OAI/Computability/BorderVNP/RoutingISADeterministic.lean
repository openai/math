import OAI.Computability.BorderVNP.RoutingISARuns

/-! # Unique execution of deterministic structured instruction fragments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- These fragments contain neither a private call nor a branch guess. -/
def Code.deterministic : Code → Bool
  | .choose .. | .call .. => false
  | .seq a b | .ifEq _ _ a b | .ifLt _ _ a b => a.deterministic && b.deterministic
  | .whileLt _ _ a => a.deterministic
  | _ => true

private theorem deterministic_atom_bits {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s t : Bank w} {bs : List Bool} {v : List (Word w)} {z : TeamRAM.Sign}
    (h : c.deterministic = true) (ha : (c.atom pub macros s).advance bs v = some (t,z)) : bs = [] := by
  by_contra hn
  obtain ⟨b,bs,rfl⟩ := List.exists_cons_of_ne_nil hn
  cases c <;> simp [Code.atom, TeamRAM.Instr.advance, Code.deterministic] at h ha
  case binary op dst x y =>
    by_cases hz : (op = .div ∨ op = .mod) ∧ s y = 0 <;> simp [hz] at ha

/-- The full event trace and both return values of deterministic assembly are unique.
The claim includes loops whose bounds are held in registers. -/
theorem Runs.unique_of_deterministic {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (r : Runs pub macros c s m es t mt) (hc : c.deterministic = true)
    {fs u mu} (r' : Runs pub macros c s m fs u mu) : es = fs ∧ t = u ∧ mt = mu := by
  induction r generalizing fs u mu with
  | @atom c s m a t z bs atomic action advance =>
    cases r' with
    | @atom _ _ _ a' t' z' bs' _ action' advance' =>
      have he := Option.some.inj (action.symm.trans action')
      subst a'
      have hb := deterministic_atom_bits hc advance
      have hb' := deterministic_atom_bits hc advance'
      subst bs
      subst bs'
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (advance.symm.trans advance'))
      exact ⟨rfl,rfl,rfl⟩
    | _ => contradiction
  | seq first second ih₁ ih₂ =>
    obtain ⟨hd,he⟩ := Bool.and_eq_true_iff.mp hc
    cases r' with
    | atom ha _ _ => cases ha
    | seq a b =>
      obtain ⟨rfl,rfl,rfl⟩ := ih₁ hd a
      obtain ⟨rfl,rfl,rfl⟩ := ih₂ he b
      exact ⟨rfl,rfl,rfl⟩
  | ifEq branch ih =>
    obtain ⟨hd,he⟩ := Bool.and_eq_true_iff.mp hc
    cases r' with
    | atom ha _ _ => cases ha
    | ifEq other =>
      obtain ⟨rfl,rfl,rfl⟩ := ih (by split <;> assumption) other
      exact ⟨rfl,rfl,rfl⟩
  | ifLt branch ih =>
    obtain ⟨hd,he⟩ := Bool.and_eq_true_iff.mp hc
    cases r' with
    | atom ha _ _ => cases ha
    | ifLt other =>
      obtain ⟨rfl,rfl,rfl⟩ := ih (by split <;> assumption) other
      exact ⟨rfl,rfl,rfl⟩
  | choose => contradiction
  | whileDone guard =>
    cases r' with
    | atom ha _ _ => cases ha
    | whileDone => exact ⟨rfl,rfl,rfl⟩
    | whileStep => contradiction
  | whileStep guard first next ih₁ ih₂ =>
    cases r' with
    | atom ha _ _ => cases ha
    | whileDone => contradiction
    | whileStep _ a b =>
      obtain ⟨rfl,rfl,rfl⟩ := ih₁ hc a
      obtain ⟨rfl,rfl,rfl⟩ := ih₂ hc b
      exact ⟨rfl,rfl,rfl⟩

end RoutingISA

end BorderVNP
end Computability
end OAI
