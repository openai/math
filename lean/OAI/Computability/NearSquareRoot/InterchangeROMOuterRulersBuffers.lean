import OAI.Computability.NearSquareRoot.InterchangeROMOuterNative

/-! # Physical sizes of the unbanked and grouped center packets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeROMRecursion NearSquareRoot.InterchangeROMExpose

def bufferCost (W cell : ℕ) := (W+2)*(cell+3)

private theorem strip_count {A : Type} (i : Input) (s : Series A) (k cell : ℕ)
    (v : A → Tree) (hs : s.count ≤ i.req.rows.count)
    (small : ∀ x, (v x).count ≤ cell*(i.req.recordWidth+1)) :
    (stripe s v).count ≤ (cell+2)*(localMass i.req k+1) := by
  let N := i.req.rows.count
  let L := i.req.recordWidth
  let V := localMass i.req k+1
  have p : 1 ≤ (i.req.header.count+1)^k := Nat.one_le_pow _ _ (by omega)
  have occupied : N*(L+1) ≤ V := by
    apply (Nat.mul_le_mul_left N (Nat.add_le_add_left p L)).trans
    exact Nat.le_succ _
  have occupied' : s.count*(L+1) ≤ V := (Nat.mul_le_mul_right _ hs).trans occupied
  have r1 : s.count ≤ V := (Nat.le_mul_of_pos_right _ (Nat.succ_pos L)).trans occupied'
  have bnd := stripe_size s v _ small
  have vpos : 1 ≤ V := Nat.succ_pos _
  have cs := Nat.mul_le_mul_left cell occupied'
  change _ ≤ (cell+2)*V
  change (stripe s v).count ≤ s.count*(cell*(L+1)+1)+1 at bnd
  rw [Nat.mul_add,Nat.mul_one,Nat.mul_left_comm] at bnd
  rw [Nat.add_mul]; omega

theorem buffers (i : Input) (W k cell : ℕ) (hW : 3 ≤ W) (hw : W ≤ i.b)
    (small : ∀ j, (i.req.contents j).count ≤ cell*(i.req.recordWidth+1)) :
    let V := localMass i.req k+1
    (∀ ψ, (stripe (centerRows i) (centerValues i ∘ ψ)).count ≤ bufferCost W cell*V) ∧
    ∀ σ, (stream i W σ).count ≤ bufferCost W cell*V := by
  intro V
  have z : 1 ≤ V := Nat.succ_pos _
  have bound : cell+2 ≤ bufferCost W cell :=
    (show cell+2 ≤ cell+3 by omega).trans (Nat.le_mul_of_pos_left _ (by omega))
  constructor
  · intro ψ
    exact (strip_count i _ k cell _ (row_counts i).2.2.le (fun _ => small _)).trans
      (Nat.mul_le_mul_right _ bound)
  · intro σ
    have shrink := (grouped_counts i W hW hw).1
    have one (u : Fin W) : (stripe (groupedRows i W) (paddedRow i u ∘ σ)).count ≤ (cell+2)*V :=
      strip_count i _ k cell _ (by omega) (fun _ => small _)
    have total := stripe_size (Series.natural W) _ _ one
    rw [Series.count_natural] at total
    change (stream i W σ).count ≤ _ at total
    apply total.trans
    have le : (cell+2)*V+1 ≤ (cell+3)*V := by rw [show (cell+3)*V=(cell+2)*V+V by ring]; omega
    have oneMore : 1 ≤ (cell+3)*V := z.trans (Nat.le_mul_of_pos_left _ (by omega))
    change _ ≤ (W+2)*(cell+3)*V
    rw [Nat.mul_assoc,Nat.add_mul W 2]
    exact Nat.add_le_add (Nat.mul_le_mul_left W le) (by omega)

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
