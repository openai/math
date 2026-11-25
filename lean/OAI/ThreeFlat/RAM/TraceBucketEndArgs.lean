import OAI.ThreeFlat.RAM.TraceBucketOperands
import OAI.ThreeFlat.Diagonal.TraceBucketRelayFit

namespace OAI
/-! # Numerical parameters of the relay bank and hidden-padding rows -/

namespace ThreeFlat.RAM.TraceBucketAtom

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr
open Diagonal.TraceSourceOwner
open scoped Fin.CommRing
variable {W : ℕ}

theorem relayArgs_value (s : Layout) (v : Fin 4→Word W) (data : Fin 1→Word W) (m : Memory W)
    (header : s.shape.header<2^W) (extent : s.pinLow (v 2).val+2*s.lowRows<2^W) :
    let extra := if (v 3).val=0 then s.pinCount (v 2).val else 0
    let args := Diagonal.TraceBucketRelay.arguments s.arcs s.tags s.per s.depth s.low (v 3).val extra s.equalId (v 0).val (v 1).val
    (∀ l, args l<2^W) → operands (relayArgs s) data m v=args := by
  intro extra args small
  have he := ext_value s v data m header extent
  have eqb : Comparison.eq.test (v 3) 0 = decide ((v 3).val=0) := by
    change decide (v 3=0)=decide ((v 3).val=0)
    by_cases equal : v 3=0
    · have zero : (v 3).val=0 := congrArg Fin.val equal
      simp only [equal,Fin.val_zero,decide_true]
    · have nz : (v 3).val≠0 := fun h=>equal (Fin.ext h)
      simp only [equal,nz,decide_false]
  have choose : (Term.select .eq (.result 3) (.literal 0) (ext s) (.literal 0)).eval data m v=(extra : Word W) := by
    simp only [Term.eval_select,Term.eval_literal,Term.eval,eqb,he]
    by_cases h : (v 3).val=0 <;> simp [extra,h]
  funext t
  have hword : ((relayArgs s t : Term W 1 4)).eval data m v=(args t : Word W) := by
    fin_cases t
    · exact (show (↑(v 0).val : Word W) = v 0 by simp).symm
    · exact (show (↑(v 1).val : Word W) = v 1 by simp).symm
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (show (↑(v 3).val : Word W) = v 3 by simp).symm
    · exact choose
    · rfl
  exact (congrArg Fin.val hword).trans (Fin.val_cast_of_lt (small t))

def holeInputs (s : Layout) (lane row field : ℕ) : Fin 7→ℕ :=
  let j := row-(s.relays+s.gates+s.tags)
  let site := lane*s.lowRows+j/s.shape.stride
  ![field,s.pinCount lane,s.bank+s.bank,j,(decode s.shape site (j%s.shape.stride)).isSome.toNat,s.zeroId,s.unitId]

private theorem vector_eval_seven {A B C : Type*} (f : A→C) (g : B→C)
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : A) (b₀ b₁ b₂ b₃ b₄ b₅ b₆ : B)
    (h₀ : f a₀ = g b₀) (h₁ : f a₁ = g b₁) (h₂ : f a₂ = g b₂)
    (h₃ : f a₃ = g b₃) (h₄ : f a₄ = g b₄) (h₅ : f a₅ = g b₅)
    (h₆ : f a₆ = g b₆) (i : Fin 7) :
    f (![a₀,a₁,a₂,a₃,a₄,a₅,a₆] i) = g (![b₀,b₁,b₂,b₃,b₄,b₅,b₆] i) := by
  fin_cases i <;> first | exact h₀ | exact h₁ | exact h₂ | exact h₃ | exact h₄ | exact h₅ | exact h₆

set_option maxHeartbeats 1600000 in
theorem holeArgs_value (s : Layout) (v : Fin 4→Word W) (data : Fin 1→Word W) (m : Memory W) (cap : ℕ) :
    let q := (v 0).val-(s.relays+s.gates+s.tags)
    let a := (v 2).val*s.lowRows+q/s.shape.stride
    let j := q%s.shape.stride
    s.relays+s.gates+s.tags≤(v 0).val → s.shape.stride<2^W → s.shape.header<2^W →
    s.pinLow (v 2).val+2*s.lowRows<2^W → a<s.shape.rows → j<s.shape.stride →
    (∀ i,TraceOwnerFormula.vars s.shape 1 a j i<2^cap) → s.shape.count+s.shape.rows*s.shape.stride+1≤2^cap →
    5*cap+128≤W →
    (∀ t, holeInputs s (v 2).val (v 0).val (v 1).val t<2^W) →
    operands (holeArgs s) data m v=holeInputs s (v 2).val (v 0).val (v 1).val := by
  intro q a j after stride hdr extent row slot initial capacity margin words
  let ix : Term W 1 4 := Term.binary .sub (.result 0) (.literal ((s.relays+s.gates+s.tags : ℕ):Word W))
  let ixSlot := Term.binary .mod ix (.literal s.shape.stride)
  let ixSite := Term.binary .add (laneBase s) (Term.binary .div ix (.literal s.shape.stride))
  have small : q<2^W := (Nat.sub_le _ _).trans_lt (v 0).isLt
  have hi : ix.eval data m v=(q : Word W) := by
    simpa [ix,q,Term.eval,natOp] using PhysicalPinsExpr.op_cast (w:=W) .sub (v 0).val (s.relays+s.gates+s.tags) after
  have hj : ixSlot.eval data m v=(j : Word W) := by
    simpa only [ixSlot,Term.eval_binary,Term.eval_literal,hi,j,natOp] using
      PhysicalPinsExpr.op_cast (w:=W) .mod q s.shape.stride ⟨small,stride⟩
  have ha : ixSite.eval data m v=(a : Word W) := by
    simp only [ixSite,Term.eval_binary,laneBase_value,Term.eval_literal,hi,
      PhysicalPinsExpr.op_cast .div q s.shape.stride ⟨small,stride⟩,natOp,a]
    simp [BinaryOp.eval]
  have hv := TraceOwnerFormula.validSlot_eval_rect s.shape 1 a j ixSite ixSlot data m v ha hj initial row slot capacity margin
  have hx := ext_value s v data m hdr extent
  funext t
  have hword : ((holeArgs s t : Term W 1 4)).eval data m v=(holeInputs s (v 2).val (v 0).val (v 1).val t : Word W) :=
    vector_eval_seven (fun e : Term W 1 4=>e.eval data m v) (fun y : ℕ=>(y:Word W))
      (.result 1) (ext s) (.literal ((s.bank+s.bank:ℕ):Word W)) ix (TraceOwnerFormula.validSlot s.shape 1 ixSite ixSlot)
      (.literal (s.zeroId:ℕ)) (.literal (s.unitId:ℕ))
      (v 1).val (s.pinCount (v 2).val) (s.bank+s.bank) q (decode s.shape a j).isSome.toNat s.zeroId s.unitId
      (by change v 1=((v 1).val:Word W); simp) hx rfl hi hv rfl rfl t
  exact (congrArg Fin.val hword).trans (Fin.val_cast_of_lt (words t))

end ThreeFlat.RAM.TraceBucketAtom

end OAI
