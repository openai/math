import OAI.Computability.NearSquareRoot.CRTPositionCompilation

/-! # Evaluation of emitted swaps and the two reflected matching rounds -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionPreparation

open IntegerMultiplication.Code Reflections

private def transposition {k : ℕ} (q : Pair) (w : Fin k → Bool) (x : Fin k) : Bool :=
  if h : q.1.length < k ∧ q.2.length < k then
    w (Equiv.swap ⟨q.1.length,h.1⟩ ⟨q.2.length,h.2⟩ x)
  else w x

private def runTail {k : ℕ} (swaps : List Pair) (w : Fin k → Bool) : Fin k → Bool :=
  swaps.foldr transposition w

private theorem runTail_image {k : ℕ} (p : Equiv.Perm (Fin k)) (t : List (Fin k))
    (w : Fin k → Bool) (x : Fin k) :
    runTail (t.map (fun j => (tally j.val,tally (p j).val))) w x =
      w (t.foldl (fun y j => Equiv.swap j (p j) y) x) := by
  induction t generalizing x with
  | nil => rfl
  | cons j t ih =>
    change transposition (tally j.val,tally (p j).val)
      (runTail (t.map _) w) x = w (t.foldl _ (Equiv.swap j (p j) x))
    simpa only [transposition,tally_length,j.isLt,(p j).isLt,and_self,↓reduceDIte] using
      ih (Equiv.swap j (p j) x)

/-- Decode a full-width round by applying the emitted transpositions and
giving the bulk interpreter exactly the three contiguous chunks. -/
def executeRound (bulkRun : {k : ℕ} → RoundTables → (Fin k → Bool) → Fin k → Bool)
    {k : ℕ} (code : RoundCode) (w : Fin k → Bool) (x : Fin k) : Bool :=
  let n := 3*(k/3)
  let h : n ≤ k := by dsimp [n]; omega
  let v := runTail code.2 w
  if hx : x.val < n then bulkRun code.1 (fun j : Fin n => v (Fin.castLE h j)) ⟨x.val,hx⟩ else v x

theorem executeRound_value (bulkRun : {k : ℕ} → RoundTables → (Fin k → Bool) → Fin k → Bool)
    (good : ∀ {m : ℕ} (p : Equiv.Perm (Fin (3*m))), Function.Involutive p → ∀ w,
      bulkRun (roundTables (tally m,table p)) w = w ∘ p)
    {k : ℕ} (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) (w : Fin k → Bool) :
    executeRound @bulkRun (roundSpec p hp) w = w ∘ p := by
  let m := k/3
  let n := 3*m
  let h : n ≤ k := by dsimp [n,m]; omega
  let v := TailTable.residual p h hp
  have inv : Function.Involutive v := TailTable.bulkVal_involutive p h hp
  let t := TailTable.owners (n := n) p
  let word := runTail (t.map (fun j => (tally j.val,tally (p j).val))) w
  have bulk := congrFun (good v inv (fun j => word (Fin.castLE h j)))
  funext x
  change (if hx : x.val < n then bulkRun (roundTables (tally m,table v))
    (fun j : Fin n => word (Fin.castLE h j)) ⟨x.val,hx⟩ else word x) = w (p x)
  have target := congrArg w (TailTable.run_owners (n := n) p hp x)
  by_cases hx : x.val < n
  · rw [dite_eq_left hx,bulk]
    let j : Fin n := ⟨x.val,hx⟩
    have ext := TailTable.extended_bulk p h j hp
    change word (Fin.castLE h (v j)) = _
    rw [← ext]
    exact (runTail_image p t w _).trans target
  · rw [dite_eq_right hx]
    rw [TailTable.extended_tail p x (Nat.le_of_not_lt hx)] at target
    exact (runTail_image p t w _).trans target

end Controlled.PositionPreparation

end NearSquareRoot
end Computability
end OAI
