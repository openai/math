import OAI.Computability.BorderVNP.TransmissionPins
import OAI.Computability.BorderVNP.RoutingISARuns

/-! # Signs of the physical pin-handling branches -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Assembly whose returning instructions always contribute sign plus, even along private bit choices. -/
def Code.positive : Code → Bool
  | .call .. | .sign true => false
  | .seq a b | .choose a b | .ifEq _ _ a b | .ifLt _ _ a b => a.positive && b.positive
  | .whileLt _ _ a => a.positive
  | _ => true

private theorem positive_atom {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s t : Bank w} {c : Code} {sgn : TeamRAM.Sign} {bs : List Bool} {old : List (Word w)}
    (hn : c.positive = true) (hc : c.isAtom = true)
    (ha : (c.atom pub macros s).advance bs old = some (t,sgn)) : sgn = .plus := by
  cases c <;> simp only [Code.positive, Code.isAtom, Bool.false_eq_true] at hc hn <;> try contradiction
  all_goals simp only [Code.atom] at ha
  case' binary => split at ha
  case' sign b => cases b <;> simp only [Code.positive, Bool.false_eq_true] at hn
  all_goals
    cases bs <;> cases old with
    | nil => simp_all [TeamRAM.Instr.advance]
    | cons a as => cases as <;> simp_all [TeamRAM.Instr.advance]

/-- Every recorded event of positive assembly contributes the multiplicative unit to its path weight. -/
theorem Runs.positive {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m es t mt c} (r : Runs pub macros c s m es t mt) (hn : c.positive = true) :
    ∀ e ∈ es, e.sign = .plus := by
  induction r with
  | atom hc _ ha => simpa using positive_atom hn hc ha
  | seq _ _ a b =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hn
    exact fun e he => (List.mem_append.mp he).elim (a ha e) (b hb e)
  | ifEq _ ih | ifLt _ ih | choose _ _ ih =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hn
    have h := ih (by split <;> assumption)
    simp_all [tick, choiceTick]
  | whileDone => simp [tick]
  | whileStep _ _ _ a b =>
    have h := a hn
    have j := b hn
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact (List.mem_append.mp he).elim (h e) (j e)

namespace Pins

/-- All chronological events in the preparation branch have positive sign. The fresh
guess for each index bit contributes unit weight. -/
theorem preparePins_positive {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m es t mt} (r : Runs pub macros preparePins s m es t mt) : ∀ e ∈ es, e.sign = .plus :=
  r.positive (by decide)

/-- All chronological events in the live-index equality test contribute unit weight. -/
theorem identityPins_positive {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m es t mt} (r : Runs pub macros checkIdentityPins s m es t mt) : ∀ e ∈ es, e.sign = .plus :=
  r.positive (by decide)

end Pins

end RoutingISA

end BorderVNP
end Computability
end OAI
