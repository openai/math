import OAI.Computability.NearSquareRoot.PhysicalWalshGatherProgram
import OAI.Computability.NearSquareRoot.PhysicalWalshGroupedRate
import OAI.Computability.NearSquareRoot.SynchronizedBitAddress

/-! # Applying a uniform physical bit-position router in both directions

One call interprets the original bit-to-packed-position table. The same
command on the inverse table returns the rounded records to original order.
The runtime includes both table calls, full stream scans and the output.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code Space FixedPoint KernelPass Controlled.Reflections

structure PositionInput where
  k : ℕ
  positions : Equiv.Perm (Fin k)
  row : Fin (2^k) → Record k

/-- Physical record-level endpoint of the bit-position permutation compiler.
At packed output address `z`, the source address has bit `i` from bit
`positions i` of `z`, as in position-table compilation. -/
def PositionRuns (ρ : ℝ) (K : ℕ := 0) :=
  BoundedTask (fun q : {v : PositionInput // K ≤ v.k} => Pieces.sparseTime ρ q.val.k)
    (fun q => Pieces.sparseSpace q.val.k)
    (fun q => send (table q.val.positions,Odd.words q.val.row))
    (fun q => send (Odd.words (q.val.row ∘ (BoxFin.bitAddress q.val.positions).symm)))

/-- Use an arbitrary pair of physical forward/inverse position lookup tables
and the uniform grouped program, with both directions paid at the sparse rate. -/
theorem selectedFromTables {I : Type} {ρ : ℝ} {K : ℕ} (hr : 0 ≤ ρ) (route : PositionRuns ρ K)
    (k s : I → ℕ) (large : ∀ i,K≤k i) (sel : ∀ i,s i≤k i) (g : (i : I) → Equiv.Perm (Fin (k i)))
    (x y : (i : I) → Fin (2^k i) → Record (k i))
    (inner : BoundedTask (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send ((tally (k i),tally (s i)),Odd.words (x i ∘ (BoxFin.bitAddress (g i)).symm)))
      (fun i => send (Odd.words (y i)))) :
    BoundedTask (Pieces.sparseTime ρ ∘ k) (Pieces.sparseSpace ∘ k)
      (fun i => send (control (s i) (g i),Odd.words (x i))) (fun i => send (Odd.words (y i ∘ BoxFin.bitAddress (g i)))) := by
  let f (i : I) : {v : PositionInput // K ≤ v.k} := ⟨⟨k i,g i,x i⟩,large i⟩
  let u (i : I) : {v : PositionInput // K ≤ v.k} := ⟨⟨k i,(g i).symm,y i⟩,large i⟩
  have pre := route.on f
  have post := route.on u
  have run := conjugate k s sel g x (fun i => x i ∘ (BoxFin.bitAddress (g i)).symm) y
    (fun i => y i ∘ BoxFin.bitAddress (g i)) _ _ _ _ pre inner post
  apply run.bound 6 5 <;> intro i
  all_goals
    have v := Pieces.odd_volume_le (k i)
    have t := Pieces.space_le_clock hr (k i)
  · change Pieces.sparseTime ρ (k i)+Pieces.sparseTime ρ (k i)+Odd.volume (k i)+1 ≤ _
    dsimp only [Function.comp_apply]; omega
  · change max (Pieces.sparseSpace (k i)) (Pieces.sparseSpace (k i))+Odd.volume (k i)+1 ≤ _
    dsimp only [Function.comp_apply]; omega

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
