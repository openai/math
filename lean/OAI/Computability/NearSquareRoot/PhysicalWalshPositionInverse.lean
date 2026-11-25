import OAI.Computability.NearSquareRoot.CRTPositionDescriptorEval
import OAI.Computability.NearSquareRoot.PhysicalWalshPositionPass

/-! # Reversing the position table supplied to a physical record router

The cycle compiler produces two reflections. Since both are involutions,
a lookup in their reverse composition gives the inverse position. Only the
small unary table is processed by the polynomial-time controller.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.Reflections

open IntegerMultiplication Code Space FixedPoint

def inverseTable (t : Table) : Table := polyPush next (prepare t)

@[fun_prop] theorem poly_inverseTable : Poly inverseTable :=
  poly_prepare.compose (Poly.push [] [] poly_next)

theorem inverseTable_correct {k : ℕ} (p : Equiv.Perm (Fin k)) :
    inverseTable (table p) = table p.symm := by
  simp only [inverseTable,prepare_spec,polyPush]
  change (table (second p)).map (fun i => next (table (first p),i)) = table p.symm
  unfold table
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  change next (table (first p),tally (second p j).val) = _
  rw [next_table]
  have e := congrArg (fun v : Equiv.Perm (Fin k) => v.symm j) (factor p)
  exact congrArg (fun i : Fin k => tally i.val) e

theorem inverseTable_volume {I : Type} (k : I → ℕ) (p : (i:I) → Equiv.Perm (Fin (k i))) :
    BoundedTask (PhysicalWalsh.Odd.volume ∘ k) (PhysicalWalsh.Odd.volume ∘ k)
      (fun i => send (table (p i))) (fun i => send (table (p i).symm)) := by
  have width : Dom k (fun i => size (table (p i))) := ⟨2,2,fun i => table_size (p i)⟩
  obtain ⟨b,hb,cmd⟩ := poly_inverseTable.on (q := fun i => table (p i)) width
  simp only [inverseTable_correct] at cmd
  obtain ⟨d,C,h⟩ := width.add hb
  obtain ⟨D,bound⟩ := polynomial_le_multiple_array_length d
  have estimate i : size (table (p i))+b i ≤ C*D*PhysicalWalsh.Odd.volume (k i) := by
    have hi := (h i).trans (Nat.mul_le_mul_left C (bound (k i)))
    rw [← Nat.mul_assoc] at hi
    exact hi.trans (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  apply (BoundedTask.of_time cmd).bound (C*D+1) (C*D+1) <;> intro i
  all_goals
    have hi := estimate i
    unfold size at hi
    dsimp only [Function.comp_apply]
    rw [Nat.succ_mul,Nat.mul_add,Nat.mul_one]
    omega

end Controlled.Reflections

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code Space FixedPoint Controlled.Reflections

/-- The native router's inverse-pullback convention, written on ordinary
ordered records. -/
def PositionPushRuns (ρ : ℝ) (K : ℕ := 0) :=
  BoundedTask (fun q : {v : PositionInput // K ≤ v.k} => Pieces.sparseTime ρ q.val.k)
    (fun q => Pieces.sparseSpace q.val.k)
    (fun q => send (table q.val.positions,Odd.words q.val.row))
    (fun q => send (Odd.words (q.val.row ∘ BoxFin.bitAddress q.val.positions)))

/-- Adapt between native router and selected transform conventions while
paying for physical inversion of the supplied table. -/
theorem positionRuns_of_push {ρ : ℝ} {K : ℕ} (hr : 0 ≤ ρ) (route : PositionPushRuns ρ K) :
    PositionRuns ρ K := by
  let swap (q : {v : PositionInput // K ≤ v.k}) : {v : PositionInput // K ≤ v.k} :=
    ⟨⟨q.val.k,q.val.positions.symm,q.val.row⟩,q.property⟩
  have prep := (inverseTable_volume (fun q : {v : PositionInput // K ≤ v.k} => q.val.k)
    (fun q => q.val.positions)).left (fun q => send (Odd.words q.val.row))
  have routed := route.on swap
  have run := prep.compose routed
  apply run.bound 1000 1000 <;> intro i
  all_goals
    have row := row_volume i.val.row
    have vol := Pieces.odd_volume_le i.val.k
    have dom := Pieces.space_le_clock hr i.val.k
  · change Odd.volume i.val.k+Pieces.sparseTime ρ i.val.k+1 ≤ _
    omega
  · change max (Odd.volume i.val.k+size (Odd.words i.val.row)) (Pieces.sparseSpace i.val.k)+1 ≤ _
    omega

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
