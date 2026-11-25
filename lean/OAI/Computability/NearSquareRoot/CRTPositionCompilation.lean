import OAI.Computability.NearSquareRoot.CRTPositionPreparation
import OAI.Computability.NearSquareRoot.CRTPositionTailTable

/-! # Uniform preparation of both bit-position routing rounds

The sole input is the position-image table. Each output round contains the
six pairs' XOR read tables and the individual transpositions involving the
remainder positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionPreparation

set_option synthInstance.maxSize 5000

open IntegerMultiplication.Code Reflections

abbrev RoundCode := RoundTables × List Reflections.Pair

def completeRound (z : Tally × Table) : RoundCode :=
  let cut := TailTable.prepare (twice z.1 ++ z.1,z.2)
  (roundTables (z.1,cut.1),cut.2)

@[fun_prop] theorem poly_completeRound : Poly completeRound := by
  have join : Poly (fun q : Tally × Tally => q.1 ++ q.2) := Easy.append.poly
  have triple := ((show Poly (fun z : Tally × Table => twice z.1) by fun_prop).pair Easy.fst.poly).compose join
  have cut : Poly (fun z : Tally × Table => TailTable.prepare (twice z.1 ++ z.1,z.2)) :=
    (triple.pair Easy.snd.poly).compose TailTable.poly_prepare
  exact ((Easy.fst.poly.pair cut.fstCompose).compose poly_roundTables).pair cut.sndCompose

def compilePositions (t : Table) : RoundCode × RoundCode :=
  let m := third (ruler t)
  let f := Reflections.prepare t
  (completeRound (m,f.1),completeRound (m,f.2))

@[fun_prop] theorem poly_compilePositions : Poly compilePositions := by
  have m := (show Easy (ruler (X := Tally)) by fun_prop).poly.compose poly_third
  exact ((m.pair poly_prepare.fstCompose).compose poly_completeRound).pair
    ((m.pair poly_prepare.sndCompose).compose poly_completeRound)

def roundSpec {k : ℕ} (f : Equiv.Perm (Fin k)) (hf : Function.Involutive f) : RoundCode :=
  let m := k/3
  let v := TailTable.residual f (show 3*m ≤ k by omega) hf
  (roundTables (tally m,table v),
    (TailTable.owners (n := 3*m) f).map (fun j => (tally j.val,tally (f j).val)))

theorem completeRound_value {k : ℕ} (f : Equiv.Perm (Fin k)) (hf : Function.Involutive f) :
    completeRound (tally (k/3),table f) = roundSpec f hf := by
  have n : twice (tally (k/3)) ++ tally (k/3) = tally (3*(k/3)) := by
    rw [← recover_tally (twice (tally (k/3)) ++ tally (k/3))]
    apply congrArg tally
    simp [twice]
    omega
  simp only [completeRound,n,TailTable.prepare_spec f (show 3*(k/3) ≤ k by omega) hf,roundSpec]

theorem compilePositions_value {k : ℕ} (p : Equiv.Perm (Fin k)) :
    compilePositions (table p) =
      (roundSpec (first p) (forwardMirror_involutive p), roundSpec (second p) (shiftedMirror_involutive p)) := by
  have r : ruler (table p) = tally k := by rw [← recover_tally (ruler (table p)),ruler_length,table,List.length_ofFn]
  simp only [compilePositions,r,third_tally,prepare_spec,completeRound_value (first p) (forwardMirror_involutive p),
    completeRound_value (second p) (shiftedMirror_involutive p)]

/-- A single charged P192 command prepares all the matching read maps and residual
swaps from the original permutation table, uniformly in the address width. -/
theorem compilePositions_uniform {X : Type} (k : X → ℕ) (p : (x : X) → Equiv.Perm (Fin (k x))) :
    Task.BT k (fun x => send (table (p x))) (fun x => send
      (roundSpec (first (p x)) (forwardMirror_involutive (p x)),
       roundSpec (second (p x)) (shiftedMirror_involutive (p x)))) := by
  simpa only [compilePositions_value] using poly_compilePositions.on (q := fun x => table (p x)) (p := k)
    (show Dom k (fun x => size (table (p x))) from ⟨2,2,fun x => table_size (p x)⟩)

end Controlled.PositionPreparation

end NearSquareRoot
end Computability
end OAI
