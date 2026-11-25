import OAI.Computability.NearSquareRoot.SynchronizedPermutationSeed
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEmit

/-! # Generating permutation headers with the reserve exponent supplied in unary -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader

open IntegerMultiplication Code Staff Strip Carry ShortFourier.BatchWord Controlled

/-- Compute the low payload cutoff from two unary arguments, including the
reserve exponent supplied by the selected candidate. -/
theorem jointLow_poly : Poly (fun z : Tally × Tally => tally (payloadBits z.1.length z.2.length)) := by
  let r : Regime (Tally × Tally) := ⟨Code.size,send,Dom.base _⟩
  have d : Realizes r (fun z => z.1.length) := by
    change Poly (fun z : Tally × Tally => tally z.1.length)
    simpa only [recover_tally] using (Poly.identity (X := Tally × Tally)).fstCompose
  have k : Realizes r (fun z => z.2.length) := by
    change Poly (fun z : Tally × Tally => tally z.2.length)
    simpa only [recover_tally] using (Poly.identity (X := Tally × Tally)).sndCompose
  exact d.times (Figure.of_spoken (k.plus (.fix 1))).short_log

/-- Generate the common pass parameters, row table and active block indices. -/
theorem jointRowSeed_poly : Poly (fun z : Tally × RowPass => rowSeed z.1.length z.2) := by
  have k : Poly (fun z : Tally × RowPass => z.2.1.2.1) := by fun_prop
  have d : Poly (fun z : Tally × RowPass => z.1) := by fun_prop
  have side : Poly (fun z : Tally × RowPass => z.2.2.1) := by fun_prop
  have dirs := (show Poly (fun z : Tally × RowPass => z.2.1) by fun_prop).compose
    PermDirectory.directory_poly
  have ids := (show Poly (fun z : Tally × RowPass => (z.2.1,z.2.2.2,z.2.2.1.2)) by fun_prop).compose
    FieldDirectory.activeRow_poly
  exact (side.pair ((((d.pair k).compose jointLow_poly).pair (k.compose stride_poly)).pair k)).pair
    (dirs.pair ids)

/-- One physical header compiler for all unary exponents and all row passes. -/
theorem jointFullHeader_poly : Poly (fun z : Tally × RowPass => fullHeader z.1.length z.2) :=
  jointRowSeed_poly.compose prepare_poly

end Benes.PackedBatchHeader

namespace ShortFourier.BatchWord.PermDirectory

open IntegerMultiplication Code

/-- Reuse the unary exponent and the row query at every element of the chronological pass list. -/
theorem emittedWith_poly {H : Type} [Codec H] [Inhabited H]
    (key : Tally × (Query × BatchTicket) → H) (hk : Poly key) :
    Poly (fun z : Tally × Query => emitted (fun pass => key (z.1,pass)) z.2) := by
  have jobs : Poly (fun z : Tally × Query => passOrder z.2.2.1) := (show Poly (fun z : Tally × Query => z.2.2.1) by fun_prop).compose passOrder_poly
  have one : Poly (fun z : (Tally × Query) × BatchTicket => key (z.1.1,z.1.2,z.2)) := (show Poly (fun z : (Tally × Query) × BatchTicket => (z.1.1,z.1.2,z.2)) by fun_prop).compose hk
  have step := Poly.push (default : Tally × Query) (default : BatchTicket) one
  have result := ((Poly.identity (X := Tally × Query)).pair jobs).compose step
  exact result

end ShortFourier.BatchWord.PermDirectory

end NearSquareRoot
end Computability
end OAI
