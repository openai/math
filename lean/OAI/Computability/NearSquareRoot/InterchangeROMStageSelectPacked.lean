import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectBudget
import OAI.Computability.NearSquareRoot.InterchangePackedRequest

/-! # The child domain of the selected address program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.Template.Data

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeAddress InterchangeROMTable

/-- At the recursive ABI the payload order is the declared finite stripe. Every
request emitted on a valid native geometry is therefore packed at that exact
width over the original finite ground-field alphabet. -/
theorem packed_of_opcode_valid {x : Data} [NeZero x.b] {j threshold : ℕ}
    (h : Valid j threshold x) {f N width : ℕ} (hf : 0<f) {P G S : Tape}
    (ok : ∀ k∈P++G++S, 2≤k ∧ k≤x.b) {q : Request x.b}
    (valid : OpcodeProgram.Valid f N width P G S (x.recordGood (Series.natural width)) q) :
    q.Packed (fun a : x.Ground => numeral a.val) ∧ q.width=f ∧ q.recordWidth=width ∧ q.rows.count=N := by
  rcases valid with ⟨⟨qw,qn,qr⟩,data,shape⟩
  refine ⟨⟨Request.admissible_inherited (radix_gt_one h) ok shape,by omega,?_⟩,qw,qr,qn⟩
  intro k
  rw [qr]
  exact data k

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
