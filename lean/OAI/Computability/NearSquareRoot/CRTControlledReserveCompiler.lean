import OAI.Computability.NearSquareRoot.CRTControlledReserveFactor
import OAI.Computability.NearSquareRoot.CRTControlledReserveMoves

/-! # Uniform four-stage position descriptors with logarithmic reserves

One pass of the P192 metadata compiler produces the exact exchange list and
the local image table for each of the four matchings.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open NearSquareRoot.Controlled.Reflections (Pair Table table)

abbrev Descriptor := List Pair × Table
abbrev Source := Tally × Tally × Table

def encode {k lo hi : ℕ} (s : ReserveStage k lo hi) : Descriptor :=
  (encodedMoves s.moves, table s.inner)

def stage (z : Source) : Descriptor :=
  let moves := gather z
  (moves, ReserveMiddle.crop (z.1, z.2.1, conjugate (moves,z.2.2)))

@[fun_prop] theorem stage_poly : Poly stage := by
  unfold stage
  fun_prop

theorem stage_value {k lo hi : ℕ} (p : Equiv.Perm (Fin k)) (fit : lo+hi ≤ k)
    (free : lo+hi ≤ (fixedPositions p).card) :
    stage (tally lo,tally hi,table p) = encode (ReserveStage.ofPerm p fit free) := by
  rw [stage,gather_value,conjugate_value]
  exact congrArg (Prod.mk _) (ReserveMiddle.crop_table (reservedMatching p lo hi) lo hi
    (reservedMatching_fixed p fit free))

def compiler (z : Source) : List Descriptor :=
  polyPush (fun t : (Tally × Tally) × Table => stage (t.1.1,t.1.2,t.2))
    ((z.1,z.2.1), ReserveShort.fourTables z.2.2)

@[fun_prop] theorem compiler_poly : Poly compiler :=
  (show Poly (fun z : Source => ((z.1,z.2.1),ReserveShort.fourTables z.2.2)) by fun_prop).compose
    (Poly.push ([],[]) [] (show Poly (fun t : (Tally × Tally) × Table =>
      stage (t.1.1,t.1.2,t.2)) by fun_prop))

theorem compiler_value {k lo hi : ℕ} (p : Equiv.Perm (Fin k)) (cap : lo+hi ≤ k/2-2) :
    compiler (tally lo,tally hi,table p) = (ReserveStage.four p cap).map encode := by
  simp only [compiler,polyPush,ReserveShort.fourTables_table,List.map_map,ReserveStage.four]
  conv_lhs => rw [← List.attach_map_subtype_val (ReserveShort.four p), List.map_map]
  apply List.map_congr_left
  intro q _
  exact stage_value q.val (by omega) (cap.trans (ReserveShort.four_short p q.val q.property).2.2)

theorem compiler_uniform {X : Type*} {r : Regime X} (k lo hi : X → ℕ)
    (p : ∀ x, Equiv.Perm (Fin (k x))) (cap : ∀ x, lo x+hi x ≤ k x/2-2)
    (low : r.Has (fun x => tally (lo x))) (high : r.Has (fun x => tally (hi x)))
    (tab : r.Has (fun x => table (p x))) :
    r.Has (fun x => (ReserveStage.four (p x) (cap x)).map encode) := by
  simpa only [fun x => compiler_value (p x) (cap x)] using
    (low.pair (high.pair tab)).thenDo compiler_poly

/-- Compilation uses polynomial time in the address width on an actual coded
tape with both reserve widths and the image table. -/
theorem compiler_task {X : Type} (k lo hi : X → ℕ) (p : ∀ x, Equiv.Perm (Fin (k x)))
    (cap : ∀ x, lo x+hi x ≤ k x/2-2) :
    Task.BT k (fun x => send (tally (lo x),tally (hi x),table (p x)))
      (fun x => send ((ReserveStage.four (p x) (cap x)).map encode)) := by
  have src : Dom k (fun x => size (tally (lo x),tally (hi x),table (p x))) := by
    refine ⟨2,8,fun x => ?_⟩
    simp only [size_prod,size_tally,tally_length]
    have hx := cap x
    have ht := Reflections.table_size (p x)
    have hx' : lo x+hi x ≤ k x := by omega
    nlinarith
  simpa only [fun x => compiler_value (p x) (cap x)] using compiler_poly.on src

end Controlled.ReserveProgram

end NearSquareRoot
end Computability
end OAI
