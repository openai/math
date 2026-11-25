import OAI.Computability.NearSquareRoot.InterchangeROMExpose
import Mathlib.Computability.Partrec

/-! # Size of the header for the center field interchange -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangeAddress InterchangeFrame InterchangeROMExpose

/-- A uniform bound on the center header per occupied row. -/
def header_coefficient (_b _n : ℕ) : ℕ := 18

theorem computable_header_coefficient {X : Type} [Primcodable X] (b n : X → ℕ) :
    Computable (fun x => header_coefficient (b x) (n x)) :=
  Computable.const 18

/-- Collapsing the center lanes to a single field preserves the row count.
Its longer unary width bounds the physical encoding of the center header. -/
theorem center_count (i : Input) :
    (send (centerHeader i)).count ≤ header_coefficient i.b i.n * i.req.rows.count := by
  let P := pre i.b 1 i.req.before
  let G := gap i.b 1 (rem i) i.req.between
  let B := post i.b (rem i) i.req.after_
  let r : Request i.b := ⟨P,G,B,i.n * f i,1,fun _ => .atom false⟩
  have valid : r.Admissible := Request.admissible_center 1 (rem i) i.radix i.valid
  have h := uniform_header_count r i.radix valid
  have fieldCount : (threads (line i.b (f i)) (ord i)).count = (line i.b (i.n * f i)).count := by
    have flat : Nonempty (Adopt (threads (line i.b (f i)) (ord i)) (line i.b (i.n * f i))) := by
      unfold line
      rw [← rack_eq]
      exact ⟨undye (line i.b (f i)) (ord i) (Adopt.same _)⟩
    exact (Classical.choice flat).cost
  have counts : (centerRows i).count = r.rows.count := by
    simp only [centerRows,r,Request.rows,arrays,stock,Loom.Path,Series.count_cart,fieldCount,P,G,B]
  have widthLe : f i ≤ i.n * f i := Nat.le_mul_of_pos_left _ i.slots
  calc
    (send (centerHeader i)).count ≤ r.header.count := by
      change size (tally (f i),shape P,shape G,shape B) ≤ size (tally (i.n*f i),shape P,shape G,shape B)
      simp only [size_prod,size_tally,tally_length]
      omega
    _ ≤ 18 * r.rows.count := h
    _ = _ := by rw [← counts,(row_counts i).2.2]; rfl

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
