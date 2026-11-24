import OAI.Computability.VPVNP.AffinePinCoefficient
import OAI.Computability.VPVNP.PolynomialBounds

/-! # Polynomial time, space and advice for the physical pin query -/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Query

open PolynomiallyBounded

private theorem reader_polynomial {i s : ℕ → ℕ} (hi : PolynomiallyBounded i) (hs : PolynomiallyBounded s) :
    PolynomiallyBounded (fun n => Reader.cost (i n) (s n)) := by
  exact ((((hi.mul (((const 5).mul hs).add (const 6))).add (const 2)).add
    (((const 5).mul hs).add (const 2))).add
    ((((const 5).mul (hi.mul hs)).add ((const 8).mul hs)).add (const 4)))

private theorem addCall_polynomial {e v : ℕ → ℕ} (he : PolynomiallyBounded e) (hv : PolynomiallyBounded v) :
    PolynomiallyBounded (fun n => SliceArithmetic.AddCall.callCap (e n) (v n)) := by
  have init := ((const 10).mul (((const 5).mul (he.add hv)).add (const 2))).add (const 1)
  have body := (((const 200).mul ((hv.add (const 1)).pow 2)).add ((const 17).mul hv)).add (const 8)
  have rows := ((he.mul body).add ((const 2).mul (he.mul hv))).add (const 2)
  exact (init.add rows).add (((const 9).mul (hv.add (const 1))).add (const 1))

theorem resources {t e w v : ℕ → ℕ} (ht : PolynomiallyBounded t) (he : PolynomiallyBounded e)
    (hw : PolynomiallyBounded w) (hv : PolynomiallyBounded v) :
    PolynomiallyBounded (fun n => cost (t n) (e n) (w n) (v n)) ∧
    PolynomiallyBounded (fun n => space (t n) (e n) (w n) (v n)) ∧
    PolynomiallyBounded (fun n => t n + t n * (e n * v n)) := by
  have scalar := he.mul hv
  have row := ht.mul hw
  have decode := (((const 7).mul ht).add ((const 6).mul hw)).add (const 2)
  have offset := (ht.mul (((const 5).mul hw).add (const 6))).add (const 2)
  have scan := ((const 2).mul row).add (const 5)
  have stage := ((((decode.add offset).add scan).add (reader_polynomial ht (const 1))).add
    (reader_polynomial ht scalar)).add (ht.add (const 1))
  have output := ((((const 8).mul scalar).add (const 5)).add (addCall_polynomial he hv)).add (const 3)
  have clock := stage.add output
  have storage := (((((((hw.add hv).add ht).add row).add (ht.mul scalar)).add scalar).add he).add (const 1))
  exact ⟨clock,storage.add clock,ht.add (ht.mul scalar)⟩

end AffinePin.Query

end VPVNP
end Computability
end OAI
