import OAI.Optimization.LinearProgramming.Lattice.OracleQuerySize
import OAI.Optimization.LinearProgramming.Lattice.ShortSelector
import OAI.Optimization.LinearProgramming.Lattice.QueryWire

/-! Reachable direction bases in the finite rounding controller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
open WithLp

/-- A reachable outer state consists of an independent basis of short integer rows,
with remaining iterations and stored directions together bounded by the ambient dimension. -/
structure DigitInvariant {p : ℕ} (M left : ℕ) (old : List (Fin p→ℤ)) : Prop where
  count : old.length+left≤p
  independent : LinearIndependent ℝ (fun i : Fin old.length => toLp 2 (realCoordinates (old.get i)))
  digits : ∀ z∈old,∀ i, (z i).natAbs ≤ searchDenominator p M^(p+1)+1

theorem DigitInvariant.initial (p M : ℕ) : DigitInvariant (p:=p) M p [] := by
  let : IsEmpty (Fin ([] : List (Fin p→ℤ)).length) := inferInstanceAs (IsEmpty (Fin 0))
  exact ⟨by simp,linearIndependent_empty_type,by simp⟩

/-- A nonzero residual together with the actual LLL selector gives the next bounded,
independent basis row. This is the invariant consumed by the encoded projection. -/
theorem DigitInvariant.next {p M fuel : ℕ} (hp : 0<p) (hM : 0<M) (v : Fin p→ℝ)
    (o : (Fin p→ℤ)→Bool) (hO : ∀ a, o a = true ↔ 0≤formValue a v)
    (old : List (Fin p→ℤ)) (hold : DigitInvariant M (fuel+1) old) (u : Fin p→ℚ)
    (hu : SignQueries.run o (probeRowsQ (residualTableMatrix old) (searchPrecision p M)) = some u) :
    DigitInvariant M fuel ((lllShortSelector M u).2 :: old) := by
  let probe zs := SignQueries.run o (probeRowsQ (rationalResidualMatrix zs) (searchPrecision p M))
  have hu' : probe old=some u := by simpa only [residualTableMatrix_eq] using hu
  let z := (lllShortSelector M u).2
  have hnext : selectedDirection probe (lllShortSelector M) old = some z := by simp [selectedDirection,hu',z]
  have hx := selectedDirection_correct hp hM v probe (lllShortSelector M)
    (fun zs => (residualProbe_correct (M:=M) v o hO zs).1)
    (fun zs => (residualProbe_correct (M:=M) v o hO zs).2)
    (lllShortSelector_correct hp hM) old z hnext
  refine ⟨by simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hold.count,
    integerDirectionList_independent_cons old z hold.independent hx.2.1,?_⟩
  intro a ha i
  rcases List.mem_cons.mp ha with rfl | hr
  · exact_mod_cast (show ((z i).natAbs : ℤ) ≤ ((searchDenominator p M^(p+1)+1 : ℕ):ℤ) from
      by simpa only [Int.natCast_natAbs] using hx.1 i)
  · exact hold.digits a hr i

def wordQueries {p : ℕ} {α : Type*} (o : (Fin p→ℤ)→Bool) (t : SignQueries p α) : List OracleSpec.Word :=
  (SignQueries.history o t).reverse.map signRowWord

@[simp] theorem wordQueries_done {p : ℕ} {α : Type*} (o : (Fin p→ℤ)→Bool) (v : α) :
    wordQueries o (.done v) = [] := rfl

@[simp] theorem wordQueries_bind {p : ℕ} {α β : Type*} (o : (Fin p→ℤ)→Bool) (t : SignQueries p α)
    (c : α→SignQueries p β) : wordQueries o (t.bind c) = wordQueries o t ++ wordQueries o (c (SignQueries.run o t)) := by
  simp [wordQueries]

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
