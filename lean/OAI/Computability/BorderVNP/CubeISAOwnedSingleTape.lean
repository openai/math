import OAI.Computability.BorderVNP.CubeISAOwnedScatterSingleRow
import OAI.Computability.BorderVNP.CubeScatterChoiceTape
import OAI.Computability.BorderVNP.CubeISAOwnedScatterRealization

/-! # Encoding a singleton row's local bit fields from a chronological tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.SingleRowData

open RoutingISA RoutingISA.Owned Physical Physical.Owned VPVNP.BurstRAM DiagonalResidueRAM

variable {n d len w : ℕ} (D : SingleRowData n d len)

/-- The diagonal singleton loop consumes one private bit at each used slot, while the
off-diagonal loop has only shared loads. -/
theorem localBits_eq (t : Fin (singlePairTrials n d)) :
    D.localBits t = if D.left = D.right then D.bits t else [] := by
  unfold localBits positions
  generalize D.bits t = bs
  by_cases eqn : D.left = D.right <;> simp only [eqn,decide_true,decide_false,Bool.false_eq_true,ite_true,ite_false,singlePositions]
  all_goals induction bs <;> simp_all only [List.map_nil,List.map_cons,List.flatMap_nil,List.flatMap_cons,
    Position.digit,Digit.choices,List.singleton_append,List.nil_append]

/-- Predicted number of private bits at this trial. -/
def privateWidth (t : Fin (singlePairTrials n d)) :=
  if D.selected t ∧ D.left = D.right then len else 0

/-- Replace only the singleton values at a diagonal grouping pair, by the successive tape bits
of the corresponding label trial. Every off-diagonal source bit is left in place. -/
def withTape (tape : ℕ → Bool) : SingleRowData n d len :=
  let draw (p : Label (n+1) d × Label (n+1) d) (j : Fin len) :=
    if h : D.left = D.right ∧ p.1 D.axis = D.left ∧ p.2 D.axis = D.right then
      let t := (singleOrderedPairs D.axis D.left D.right).symm ⟨p,h.2⟩
      tape (ChoiceTape.offset D.privateWidth t.val + j.val)
    else D.value p j
  {D with value := draw}

/-- Original values are retained on every crossing singleton and every label pair outside
the visited diagonal row. -/
theorem withTape_exterior (tape : ℕ → Bool) (p : Label (n+1) d × Label (n+1) d)
    (outside : ¬(D.left = D.right ∧ p.1 D.axis = D.left ∧ p.2 D.axis = D.right)) :
    (D.withTape tape).value p = D.value p := by
  funext j
  simp only [withTape,outside,dite_false]

/-- The recovered fields give the specified consecutive bit slice at a selected diagonal trial. -/
theorem withTape_diagonal (tape : ℕ → Bool) (same : D.left = D.right) (t : Fin (singlePairTrials n d)) :
    (D.withTape tape).bits t = ChoiceTape.segment tape (ChoiceTape.offset D.privateWidth t.val) len := by
  let p := (singleOrderedPairs D.axis D.left D.right) t
  have yes : D.left = D.right ∧ p.val.1 D.axis = D.left ∧ p.val.2 D.axis = D.right := ⟨same,p.property⟩
  have back : (singleOrderedPairs D.axis D.left D.right).symm ⟨p.val,yes.2⟩ = t := Equiv.symm_apply_apply ..
  apply List.ext_getElem (by simp [bits,ChoiceTape.segment])
  intro j hj _
  simp only [bits,List.getElem_ofFn]
  change (D.withTape tape).value p.val _ = _
  simp only [withTape,dite_eq_left yes,back,ChoiceTape.segment,List.getElem_map,List.getElem_range',Nat.one_mul]

/-- The starting crossing address does not depend on private diagonal singleton values. -/
theorem withTape_cursor (tape : ℕ → Bool) (m : Memory w) (k : ℕ) :
    ((D.withTape tape).before m k).1 = (D.before m k).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < singlePairTrials n d
    · let t : Fin (singlePairTrials n d) := ⟨k,hk⟩
      by_cases yes : D.selected t
      · rw [(D.withTape tape).before_visit m t yes,D.before_visit m t yes]
        exact congrArg (· + D.crossWords) ih
      · rw [(D.withTape tape).before_skip m t yes,D.before_skip m t yes]
        exact ih
    · simpa only [before,hk,dite_false] using ih

/-- The guessed singleton values can be replaced while retaining every routed-source requirement. -/
theorem prepared_withTape {src : Set ℕ} (tape : ℕ → Bool) (m : Memory w) (ready : D.PreparedRow src m) :
    (D.withTape tape).PreparedRow src m := by
  intro t ok
  rw [D.withTape_cursor]
  apply (ready t ok).of_routed
  change (singlePositions (decide (D.left=D.right)) (D.bits t)).map Position.routed =
    (singlePositions (decide (D.left=D.right)) ((D.withTape tape).bits t)).map Position.routed
  by_cases same : D.left = D.right
  · simp [same,singlePositions,bits,Function.comp_def,Position.routed]
  · have keep := D.withTape_exterior tape (D.pair t) (by simp [same])
    change _ = (singlePositions _ (List.ofFn ((D.withTape tape).value (D.pair t)))).map _
    rw [keep]
    rfl

/-- The full native row consumes exactly the initial slice predicted by its fixed trial widths. -/
theorem withTape_choices (tape : ℕ → Bool) :
    rowChoices (D.withTape tape).selected (D.withTape tape).localBits =
      ChoiceTape.segment tape 0 (ChoiceTape.offset D.privateWidth (singlePairTrials n d)) := by
  apply ChoiceTape.row_segment
  intro t
  change (if D.selected t then (D.withTape tape).localBits t else []) = _
  by_cases valid : D.selected t <;> by_cases same : D.left = D.right
  · rw [ite_eq_left valid,localBits_eq,ite_eq_left (show (D.withTape tape).left = (D.withTape tape).right from same),D.withTape_diagonal tape same t]
    simp [privateWidth,same,valid]
  · rw [ite_eq_left valid,localBits_eq,ite_eq_right (show (D.withTape tape).left ≠ (D.withTape tape).right from same)]
    simp [privateWidth,same,ChoiceTape.segment]
  all_goals simp [valid,privateWidth,ChoiceTape.segment]

end Cube.Scatter.SingleRowData

end BorderVNP
end Computability
end OAI
