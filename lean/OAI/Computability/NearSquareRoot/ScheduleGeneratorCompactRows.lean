import OAI.Computability.NearSquareRoot.ScheduleGeneratorCompactRanks
import Batteries.Tactic.OpenPrivate

/-! # The effective row function for the public block decoder -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.CompactRows

open IntegerMultiplication CommonAlphabet Numbering
open private ops from OAI.Computability.NearSquareRoot.CommonAlphabetIO

private theorem addTwoZero (n : ℕ) : n+2 ≠ 0 := by omega
private theorem addTwoOne (n : ℕ) : n+2 ≠ 1 := by omega

private theorem leftRank : (Numbering.move.equiv TM.Move.left).val = 0 := rfl
private theorem stayRank : (Numbering.move.equiv TM.Move.stay).val = 1 := rfl
private theorem rightRank : (Numbering.move.equiv TM.Move.right).val = 2 := rfl

private theorem command_eq (s d : Public.Letter) (i k : TM.Move) :
    ((bool.arrow (publicLetter.prod Numbering.move)).equiv (ops (s,i) (d,k))).val =
      operations (rankLetter s) (rankLetter d) (Numbering.move.equiv i).val (Numbering.move.equiv k).val :=
  operations_eq _

/-- An encoded decoder first classifies a completely read ternary block. The remaining
operations only involve bounded buffer updates and the two physical tape instructions. -/
theorem row_eq {A : Type} (c : Code A) (decode : A → Option Bool) (classify : ℕ → ℕ)
    (correct : ∀ b : Letters c.width, classify (rankBuf b) = rankTernary (decode (c.dec b)))
    (s : Compact.Phase c.width) (h : Bool → Public.Letter) :
    row c.width classify (rankState s,((bool.arrow publicLetter).equiv h).val) =
      (Compact.rule c Option.join decode Public.bit Option.isNone s h).map fun z =>
        (rankState z.1, ((bool.arrow (publicLetter.prod Numbering.move)).equiv z.2).val) := by
  have src : digit 4 ((bool.arrow publicLetter).equiv h).val 0 = rankLetter (h false) :=
    digit_arrow bool publicLetter h false
  have dst : digit 4 ((bool.arrow publicLetter).equiv h).val 1 = rankLetter (h true) :=
    digit_arrow bool publicLetter h true
  unfold row
  simp only [src,dst]
  cases s with
  | prev =>
    simp only [rank_prev, Compact.rule, ↓reduceIte, rank_blank]
    cases h true with
    | none =>
      simp [command_eq, stayRank, rightRank]
    | some v =>
      simp [command_eq, stayRank, leftRank, CommonAlphabet.first]
  | done =>
    simp [Compact.rule,rank_done]
  | scan v j =>
    let d := (h false).join
    let b := Function.update v j d
    let t := j.val + c.width*rankBuf v
    have bound : t < scanCount c.width := (((buffer c.width).prod (fin c.width)).equiv (v,j)).isLt
    have quot : t / c.width = rankBuf v := by
      rw [show t = _ from rfl, Nat.add_mul_div_left _ _ c.pos, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have mod : t % c.width = j.val := by simpa [t] using Nat.mod_eq_of_lt j.isLt
    have code : storeDigit c.width (rankBuf v) j.val (rankLetter (h false)-1) = rankBuf b := by
      rw [rank_join]
      exact store_eq v j d
    simp only [rank_scan, scanState]
    dsimp only [t] at bound quot mod
    simp only [addTwoZero, addTwoOne, ↓reduceIte, Nat.add_sub_cancel, bound, mod, quot, code]
    change some ((if j.val+1<c.width then scanState _ (rankBuf b) _ else emitState _ (classify (rankBuf b))),
      operations _ _ 2 1) = _
    rw [correct]
    by_cases more : j.val+1 < c.width
    · simp [Compact.rule,atIndex,more,command_eq,rightRank,stayRank,b,d]
    · simp [Compact.rule,atIndex,more,command_eq,rightRank,stayRank,b,d]
  | emit d =>
    have bd : rankTernary d < 3 := (ternary.equiv d).isLt
    have hg : ¬scanCount c.width + rankTernary d < scanCount c.width := by omega
    simp only [rank_emit, emitState, addTwoZero, addTwoOne, ↓reduceIte,
      Nat.add_sub_cancel, hg, Nat.add_sub_cancel_left, bd]
    cases d with
    | none =>
      have zn : rankTernary none = 0 := rfl
      simp [Compact.rule,command_eq,leftRank,stayRank,zn,CommonAlphabet.first]
    | some d =>
      have nz : rankTernary (some d) ≠ 0 := by cases d <;> decide
      have rb : rankLetter (Public.bit d) = rankTernary (some d)+1 := rank_public_some _
      simp [Compact.rule,command_eq,rightRank,stayRank,rank_start,nz,rb]
  | back j =>
    have hg : ¬scanCount c.width + (3+j.val) < scanCount c.width := by omega
    have he : ¬3+j.val < 3 := by omega
    simp only [rank_back, backState,addTwoZero,addTwoOne,↓reduceIte,
      Nat.add_sub_cancel,hg,Nat.add_sub_cancel_left,he,Compact.rule,Option.map_some,
      command_eq, leftRank,stayRank]
    by_cases more : j.val+1 < c.width <;> simp [atIndex,more,backState]

end Generator.CompactRows

end NearSquareRoot
end Computability
end OAI
