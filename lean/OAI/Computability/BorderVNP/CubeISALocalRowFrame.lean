import OAI.Computability.BorderVNP.CubeISALocalRowCode

/-! # Control and register preservation of the native per-role declaration checks

The inner tallies retain the outer loop cursors, both saved addresses, and the
fixed data used by the following comparison. The full row verifiers include
the header installation and restore the caller's vertex cursor before returning.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open Constants

/-- Fixed arithmetic literals only write register 58. -/
private theorem literalKeeps (bits : List Bool) (k : Reg) (ne : k ≠ 58) : (literal bits).keeps k = true := by
  induction bits with
  | nil => simp [literal,Code.keeps,ne]
  | cons b bs ih => cases b <;> simp [literal,Code.keeps,ne,ih]

private theorem detOfUnsigned (c : Code) (h : c.unsigned = true) : c.deterministic = true := by
  induction c <;> simp_all [Code.unsigned,Code.deterministic]

private theorem candidatesKeep (n : ℕ) (k : Reg) (hk : k ∈ ([0,1,5,9,22,23,59,61] : List Reg)) :
    (Owned.packetCandidate n).keeps k = true ∧ (Owned.singleCandidate n).keeps k = true := by
  induction n with
  | zero =>
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  | succ n ih =>
    have unfoldCandidate :
        (Owned.packetCandidate (n+1)).keeps k = ((Owned.packetCandidate n).keeps k && true) ∧
        (Owned.singleCandidate (n+1)).keeps k = (Owned.singleCandidate n).keeps k := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hk
      rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨rfl,rfl⟩
    simp only [unfoldCandidate.1,unfoldCandidate.2,Bool.and_true,ih,and_self]

/-- Each scalar orientation preserves the row verifier's persistent word registers. -/
theorem diagonalTally_keeps (n : ℕ) (k : Reg) (hk : k ∈ ([0,1,5,9,22,23,59,61] : List Reg)) :
    (SingleTally.oriented n).keeps k = true := by
  have h := (candidatesKeep n k hk).2
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals change ((Owned.singleCandidate n).keeps _ && true) = true
  all_goals simpa only [Bool.and_true] using h

/-- The packet loop and both scalar orientations preserve all the words needed
at the final comparison, including the saved claim address and vertex cursor. -/
theorem strictTally_keeps (n : ℕ) (k : Reg) (hk : k ∈ ([0,1,5,9,22,23,59,61] : List Reg)) :
    (DeclaredRow.strict n).keeps k = true := by
  have p := (candidatesKeep n k hk).1
  have s := diagonalTally_keeps n k hk
  have expand : (DeclaredRow.strict n).keeps k =
      (((Owned.packetCandidate n).keeps k && true) &&
        ((SingleTally.oriented n).keeps k && (SingleTally.oriented n).keeps k)) := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  simp only [expand,p,s,Bool.and_true]

private theorem setupKeeps (n b h K s : ℕ) (k : Reg) (hk : k = 22 ∨ k = 23) :
    (setup n b h K s).keeps k = true := by
  rcases hk with rfl|rfl
  all_goals
    simp (config := {decide := true}) [setup,prime,metadata,OwnedRowSetup.parameters,pushLiteral,
      Code.block,Code.keeps,literalKeeps]

/-- The complete strict-row verifier never assigns either outer unordered-pair loop register. -/
theorem strictChecked_keeps (n b h K s : ℕ) (k : Reg) (hk : k = 22 ∨ k = 23) :
    (strictChecked n b h K s).keeps k = true := by
  have su := setupKeeps n b h K s k hk
  have t := DeclaredRow.strict_keeps n k hk
  rcases hk with rfl|rfl
  all_goals change ((setup n b h K s).keeps _ && (true && ((DeclaredRow.strict n).keeps _ && true))) = true
  all_goals simp only [su,t,Bool.and_true]

/-- The complete diagonal-row verifier preserves the same outer cursor and bound. -/
theorem diagonalChecked_keeps (n b h K s : ℕ) (k : Reg) (hk : k = 22 ∨ k = 23) :
    (diagonalChecked n b h K s).keeps k = true := by
  have su := setupKeeps n b h K s k hk
  have t := DeclaredRow.diagonal_keeps n k hk
  rcases hk with rfl|rfl
  all_goals change ((setup n b h K s).keeps _ && (true && ((SingleTally.oriented n).keeps _ && true))) = true
  all_goals simp only [su,t,Bool.and_true]

private theorem candidates (n : ℕ) :
    (Owned.packetCandidate n).unsigned = true ∧ (Owned.singleCandidate n).unsigned = true ∧
    (Owned.packetCandidate n).withoutAccept = true ∧ (Owned.singleCandidate n).withoutAccept = true := by
  induction n with
  | zero => decide
  | succ n ih =>
    change ((Owned.packetCandidate n).unsigned && true) = true ∧ (Owned.singleCandidate n).unsigned = true ∧
      ((Owned.packetCandidate n).withoutAccept && true) = true ∧ (Owned.singleCandidate n).withoutAccept = true
    simpa only [Bool.and_true] using ih

/-- The singleton tally uses positive, choice-free instructions. -/
theorem diagonalTally_unsigned (n : ℕ) : (SingleTally.oriented n).unsigned = true := by
  change ((Owned.singleCandidate n).unsigned && true) = true
  simp [(candidates n).2.1]

/-- The complete strict tally uses positive, choice-free instructions. -/
theorem strictTally_unsigned (n : ℕ) : (DeclaredRow.strict n).unsigned = true := by
  change (((Owned.packetCandidate n).unsigned && true) &&
    ((SingleTally.oriented n).unsigned && (SingleTally.oriented n).unsigned)) = true
  simp [(candidates n).1,diagonalTally_unsigned]

/-- Every returning execution of the singleton tally is deterministic. -/
theorem diagonalTally_deterministic (n : ℕ) : (SingleTally.oriented n).deterministic = true :=
  detOfUnsigned _ (diagonalTally_unsigned n)

/-- Every returning execution of the strict tally is deterministic. -/
theorem strictTally_deterministic (n : ℕ) : (DeclaredRow.strict n).deterministic = true :=
  detOfUnsigned _ (strictTally_unsigned n)

private theorem diagonalTallyReturns (n : ℕ) : (SingleTally.oriented n).withoutAccept = true := by
  change ((Owned.singleCandidate n).withoutAccept && true) = true
  simp [(candidates n).2.2.2]

private theorem strictTallyReturns (n : ℕ) : (DeclaredRow.strict n).withoutAccept = true := by
  change (((Owned.packetCandidate n).withoutAccept && true) &&
    ((SingleTally.oriented n).withoutAccept && (SingleTally.oriented n).withoutAccept)) = true
  simp [(candidates n).2.2.1,diagonalTallyReturns]

private theorem setupUnsigned (n b h K s : ℕ) : (setup n b h K s).unsigned = true := by
  simp (config := {decide := true}) [setup,prime,metadata,pushLiteral,OwnedRowSetup.parameters_unsigned,
    Code.block,Code.unsigned,(literal_unsigned _).1]

private theorem setupReturns (n b h K s : ℕ) : (setup n b h K s).withoutAccept = true := by
  simp (config := {decide := true}) [setup,prime,metadata,pushLiteral,OwnedRowSetup.parameters,
    Code.block,Code.withoutAccept,(literal_unsigned _).2]

/-- The complete strict-row verifier emits only unsigned, choice-free events. -/
theorem strictChecked_unsigned (n b h K s : ℕ) : (strictChecked n b h K s).unsigned = true := by
  change ((setup n b h K s).unsigned && (true && ((DeclaredRow.strict n).unsigned && true))) = true
  simp [setupUnsigned,strictTally_unsigned]

/-- The complete diagonal-row verifier emits only unsigned, choice-free events. -/
theorem diagonalChecked_unsigned (n b h K s : ℕ) : (diagonalChecked n b h K s).unsigned = true := by
  change ((setup n b h K s).unsigned && (true && ((SingleTally.oriented n).unsigned && true))) = true
  simp [setupUnsigned,diagonalTally_unsigned]

/-- The whole strict role returns to its continuation on a successful execution. -/
theorem strictChecked_withoutAccept (n b h K s : ℕ) : (strictChecked n b h K s).withoutAccept = true := by
  change ((setup n b h K s).withoutAccept && (true && ((DeclaredRow.strict n).withoutAccept && true))) = true
  simp [setupReturns,strictTallyReturns]

/-- The whole diagonal role returns to its continuation on a successful execution. -/
theorem diagonalChecked_withoutAccept (n b h K s : ℕ) : (diagonalChecked n b h K s).withoutAccept = true := by
  change ((setup n b h K s).withoutAccept && (true && ((SingleTally.oriented n).withoutAccept && true))) = true
  simp [setupReturns,diagonalTallyReturns]

/-- The complete strict-row verifier has at most one returning execution. -/
theorem strictChecked_deterministic (n b h K s : ℕ) : (strictChecked n b h K s).deterministic = true :=
  detOfUnsigned _ (strictChecked_unsigned n b h K s)

/-- The complete diagonal-row verifier has at most one returning execution. -/
theorem diagonalChecked_deterministic (n b h K s : ℕ) : (diagonalChecked n b h K s).deterministic = true :=
  detOfUnsigned _ (diagonalChecked_unsigned n b h K s)

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
