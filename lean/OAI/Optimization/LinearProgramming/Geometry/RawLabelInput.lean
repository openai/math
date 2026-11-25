import OAI.Optimization.LinearProgramming.Geometry.RawLabelPlacement
import OAI.Optimization.LinearProgramming.Geometry.LabelHeader

/-! The ordinary unpadded entry executes tape placement and the relocatable header code. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelInput

open RAM Matrix
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r s n : ℕ}

/-- The ordinary entry takes `[r,s,n,i]` on the dimension tape. The scalar tape contains
row-major D, row-major E and the n scalar prices. The loader computes all table locations. -/
def rawHeader : Block := .seq placeInputs prepareHeader

theorem rawHeader_spec (P : K → Prop) (p0 : P 0) (D : Matrix (Fin r) (Fin n) K) (E : Matrix (Fin s) (Fin n) K)
    (price : Fin n → K) (i : Fin n) (pd : ∀ a b, P (D a b)) (pe : ∀ a b, P (E a b)) (pp : ∀ b, P (price b)) :
    let x := standardBuffers r s n
    let m := (start [r,s,n,i.val] (rawTape D E price)).memory
    ∃ t c, c ≤ 10000*(r+s+n+1)^3 ∧ Block.Eval (Memory.AllData P) rawHeader m c t ∧
      Header x D E price i t ∧ (∀ a, a≠0 → (a<x.dual ∨ x.free≤a) → t.data a=m.data a) ∧
      ∀ a, 256≤a → t.index a=m.index a := by
  let x := standardBuffers r s n
  let m := (start [r,s,n,i.val] (rawTape D E price)).memory
  change ∃ t c, _ ∧ Block.Eval _ _ m c t ∧ Header x D E price i t ∧ _
  have hm : m.AllData P := rawTape_safe P p0 D E price pd pe pp
  obtain ⟨u,c1,h1,e1,p,df,ifrm⟩ := placeInputs_spec P m hm D E price i rfl rfl rfl rfl
    (fun a b => by
      change ((rawTape D E price)[a.val*n+b.val]?).getD 0=D a b
      rw [rawTape_primal,Option.getD_some])
    (fun a b => by
      change ((rawTape D E price)[r*n+(a.val*n+b.val)]?).getD 0=E a b
      rw [rawTape_dual,Option.getD_some])
    (fun b => by
      change ((rawTape D E price)[r*n+(s*n+b.val)]?).getD 0=price b
      rw [rawTape_price,Option.getD_some])
  obtain ⟨t,c2,h2,e2,out,hd,hi⟩ := prepareHeader_spec P u e1.safe_end x D E price i p
  refine ⟨t,c1+c2,?_,e1.seq e2,out,?_,?_⟩
  · have hc := Nat.pow_le_pow_left (by omega : r+n+1≤r+s+n+1) 3
    have hq : (r+s+n+1)^2 ≤ (r+s+n+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
    omega
  · intro a ha hf
    rw [hd,df _ ha hf]
  · intro a ha
    have ok : a ∉ modifiedHeaderRegisters := by simp [modifiedHeaderRegisters]; omega
    rw [hi _ ok,ifrm _ ha]

end LabelInput
end Geometry
end LinearProgramming
end Optimization
end OAI
