import OAI.Computability.NearSquareRoot.PrecisionMaskedCarry
import OAI.Computability.NearSquareRoot.PrecisionGridQuantization
import OAI.Computability.NearSquareRoot.PrecisionDigitInput
import OAI.Computability.NearSquareRoot.BoundedProgram

/-! # Computing the square-root normalization from the input length

The box generator writes its ordered list of axis widths and moduli. A header
program converts the moduli to binary, multiplies them, and runs the fixed-point
square-root routine on the resulting integer.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Code Carry Staff Strip Brief DigitPacking

private def volumeWord (axes : List (Tally × Tally)) : Bits.Word :=
  Carry.count [true] (axes.map fun p => born p.2.length)

private theorem volumeWord_poly : Poly volumeWord := by
  have moduli : Easy (fun p : Tally × Tally => born p.2.length) := Easy.snd.compose easy_chart
  exact ((Code.Poly.const ([true] : Bits.Word)).pair moduli.mapping.poly).compose countPoly

/-- Generate the binary occupied volume from the address width. The polynomial
setup bounds the length of the binary integer even when the volume is exponential. -/
theorem directoryVolumeFigure {I : Type} {r : Regime I} {k : I → ℕ} (K : Realizes r k) :
    Figure r (fun i => directoryVolume (k i)) := by
  have ruler : r.Has (fun i => tally (k i)) := K
  have dirs := ruler.thenDo BoxProgram.encoded_poly
  refine ⟨_, dirs.thenDo volumeWord_poly, fun i => ?_⟩
  change Bits.value (volumeWord (BoxProgram.encoded (tally (k i)))) = directoryVolume (k i)
  simp [volumeWord, countVal, BoxProgram.encoded, List.map_map, Function.comp_def, birthValue,
    directoryVolume, boxVolume, BoxFin.prod_modulus]

/-- Compute the final real scale record from a single unary input length. The
cost of the box and arithmetic setup is absorbed by the binary header budget. -/
theorem directorySqrtTask {I : Type} (n : I → ℕ) (_hn : ∀ i, 2 ≤ n i)
    (hv : ∀ i, ValidDirectory (addressBits (n i))) :
    Space.BoundedTask n n (fun i => send (tally (n i)))
      (fun i => send (Dusk.mark (sqrtRecord (fractionBits (addressBits (n i)))
        (componentBits (addressBits (n i))) (directoryVolume (addressBits (n i)))))) := by
  let k := addressBits ∘ n
  have w : Figure (city n) (width ∘ n) := Figure.of_spoken (guide_city n).amount_.short_log
  have digits : Figure (city n) (DigitPacking.count ∘ n) :=
    ((((guide_city n).amount_.added w).subtracted (.natural 1)).quotients w)
  have K : Realizes (city n) k := ((Figure.natural 4).multiplied digits).short_log
  have p : Realizes (city n) (fun i => fractionBits (k i)) :=
    ((Realizes.fix 70).times K).plus (Realizes.fix 1)
  have widthRuler : Realizes (city n) (fun i => componentBits (k i)) :=
    ((Realizes.fix 96).times K).plus (Realizes.fix 4)
  have record := sqrtRecord_has (k := k) p widthRuler (directoryVolumeFigure K)
    (fun i => boxVolume_le (hv i)) (fun i => by unfold fractionBits componentBits; omega)
  have make := Regime.Small.cooked (wealthy n) record
  have binaryHeader := make.times (here n) 8 (fun i => by
    have u := Param.load_below (n i)
    have v := Param.amount_l (n i)
    change ((Param.load (n i) : ℕ) : ℝ) ≤ (8 : ℝ)*((n i : ℝ)+1)
    exact_mod_cast (by omega : Param.load (n i) ≤ 8*(n i+1)))
  have start : Volume (measure n) (fun i => send (tally (n i))) := by
    refine ⟨2, fun i => ?_⟩
    change (size (tally (n i)) : ℝ) ≤ 2 * ((n i : ℝ)+1)
    rw [size_tally, tally_length]
    push_cast
    linarith
  have load := Carries.func (y := fun i => tally (n i)) (here n) start _ easy_chart
  have pipeline := (show Carries (measure n) (fun i => send (tally (n i))) ((city n).header) from
    by
      change Carries _ _ (fun i => send (born (n i)))
      simpa only [tally_length] using load).chain binaryHeader
  have run : Task (fun i => n i + 1) (fun i => send (tally (n i)))
      (send ∘ fun i => Dusk.mark (sqrtRecord (fractionBits (k i))
        (componentBits (k i)) (directoryVolume (k i)))) := by
    simpa only [Brief.measure, ← Nat.cast_add_one, Nat.ceil_natCast] using pipeline.runs.release
  change Space.BoundedTask n n (fun i => send (tally (n i)))
    (send ∘ fun i => Dusk.mark (sqrtRecord (fractionBits (k i))
      (componentBits (k i)) (directoryVolume (k i))))
  apply (Space.BoundedTask.of_time run).bound 2 5
  · intro i; omega
  · intro i
    change size (tally (n i)) + _ + 1 ≤ _
    rw [size_tally, tally_length]
    omega

end FixedPoint

end NearSquareRoot
end Computability
end OAI
