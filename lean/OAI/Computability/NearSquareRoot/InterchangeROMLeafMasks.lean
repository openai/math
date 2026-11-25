import OAI.Computability.NearSquareRoot.InterchangeROMLeafMasksNative
import OAI.Computability.NearSquareRoot.InterchangeROMLeafMasksBank

/-! # The fixed leaf mask-bank compiler on mixed-radix request headers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMLeafMasks.Instance
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMLeafMasksShape

/-- Only the active field range enters the polynomial multiplying the number
of rows. Parsing the descriptor is charged once. -/
def work (k : ℕ) (i : Instance) :=
  (i.D+1)^k*i.N + (size (descriptor i.req)+1)^2

/-- The same command parses every radix and every leaf header, enumerates
all ordered pairs of ranks, and writes the complete bank of native masks. -/
theorem bank : ∃ k : ℕ, Space.BoundedTask (work k) (work k)
    (fun i => Tree.fork (send (tally i.radix)) i.req.header)
    (fun i => send ((InterchangeROMLeaf.batch i.req).colors.map (InterchangeROMLeaf.batch i.req).masks)) := by
  have sh := InterchangeROMLeafMasksShape.prepare Instance.radix Instance.req
    (fun i => i.property.1) (fun i => i.property.2)
  obtain ⟨k,build⟩ := InterchangeROMLeafMasksBank.prepare
  let c (i : Instance) := InterchangeROMLeafMasksBank.cost k (rulers i.req)
  have mid : Space.BoundedTask c c (fun i => send (rulers i.req)) (fun i => send i.descs) := by
    apply (build.on (fun i : Instance => rulers i.req)).conform
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    intro i
    let out (d : ℕ) := send ((InterchangeROMLeaf.ranks d).tab (fun z =>
      ((rulers i.req,tally z.1.val,tally z.2.val),(rulers i.req,tally z.2.val,tally z.1.val))))
    change out (tally i.D).length = out i.D
    exact congrArg out (tally_length _)
  let T (i : Instance) := (i.D+1)^(k+2)*i.N
  have b₁ (i : Instance) : i.N ≤ T i :=
    Nat.le_mul_of_pos_left _ (pow_pos (Nat.succ_pos _) _)
  have b₂ (i : Instance) : (i.D+1)^2*i.N ≤ T i :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  have b₃ (i : Instance) : c i ≤ 20*T i := by
    have b := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 0 < i.D+1)
      (by omega : k ≤ k+2)) (size_rulers i)
    simpa only [c,InterchangeROMLeafMasksBank.cost,InterchangeROMLeafMasksShape.rulers,tally_length,
      T,Nat.mul_left_comm,Nat.mul_assoc,D] using b
  refine ⟨k+2,((sh.compose mid).compose materialize).bound 23 23 ?_ ?_⟩
  · intro i
    change i.N + (size (descriptor i.req)+1)^2 + c i + (i.D+1)^2*i.N+1 ≤
      23*(T i + (size (descriptor i.req)+1)^2+1)
    have := b₁ i
    have := b₂ i
    have := b₃ i
    omega
  · intro i
    change max (max (i.N + (size (descriptor i.req)+1)^2) (c i)) ((i.D+1)^2*i.N)+1 ≤
      23*(T i + (size (descriptor i.req)+1)^2+1)
    have := b₁ i
    have := b₂ i
    have := b₃ i
    omega

end InterchangeROMLeafMasks.Instance

end NearSquareRoot
end Computability
end OAI
