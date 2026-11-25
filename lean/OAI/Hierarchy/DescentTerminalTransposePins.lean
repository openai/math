import OAI.Hierarchy.DescentTerminalCandidateType
import OAI.Hierarchy.DescentTerminalScalarTransposes
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.ThreeFlat.Diagonal.TraceBanks

namespace OAI
/-! # Four literal word columns share two Boolean transpose proposals -/
namespace Hierarchy.DescentTerminalChipPins
open DescentTerminalScalarTransposes DescentTerminalBinReaddress
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.Diagonal TraceBanks
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {K W q p w : ℕ}
local notation "N" => K*W
def planes (z : Inputs K W q p→Bool) (which : Bool) : Proposal K W q p :=
  fun b pos j=>z (which,b,pos,j)
def join (x y : Proposal K W q p) : Inputs K W q p→Bool :=
  fun b=>if b.1 then y b.2.1 b.2.2.1 b.2.2.2 else x b.2.1 b.2.2.1 b.2.2.2
theorem planes_join (x y : Proposal K W q p) : planes (join x y) false=x ∧ planes (join x y) true=y := by
  constructor <;>funext b s j <;>simp [planes,join]
theorem join_planes (z : Inputs K W q p→Bool) : join (planes z false) (planes z true)=z := by
  funext i;rcases i with ⟨b,i,a,j⟩;cases b <;>rfl

def shape (W q p : ℕ) (slice : Bool) := if slice then sliceWidth W q p else q*(W*p)

def socket (slice : Bool) (i : Fin N) : Fin (shape W q p slice)→Bit K W q p := by
  let a : Fin K×Fin W:=finProdFinEquiv.symm i
  cases slice
  · intro j
    let t : Fin q×Fin (W*p):=finProdFinEquiv.symm j
    exact (a.1,(a.2,t.1),t.2)
  · intro j
    exact (a.1,(transpose W q p).symm (a.2,j))

def word (x : Proposal K W q p) (slice : Bool) (i : Fin N) : Word (shape W q p slice) :=
  match slice with
  | false=>rowWord x i
  | true=>chunks x i

theorem socket_bit (x : Proposal K W q p) (slice : Bool) (i : Fin N) (j : Fin (shape W q p slice)) :
    wordBits _ (word x slice i) j=x (socket slice i j).1 (socket slice i j).2.1 (socket slice i j).2.2 := by
  cases slice with
  | false=>
    exact congrFun ((wordBits (q*(W*p))).apply_symm_apply
      (fun j=>x (finProdFinEquiv.symm i).1 ((finProdFinEquiv.symm i).2,(finProdFinEquiv.symm j).1)
        (finProdFinEquiv.symm j).2)) j
  | true=>exact gather_bits _ _ _

/-- Both columns for a proposal refer to the same input pin names. A short
last column and the high safety bit are wired to literal zero. -/
def pin (which slice : Bool) (i : ℕ) (b : Fin (w+1)) : Inputs K W q p⊕Bool :=
  if valid : i<N then
    if low : b.val<shape W q p slice then .inl (which,socket slice ⟨i,valid⟩ ⟨b.val,low⟩) else .inr false
  else .inr false

def column (z : Inputs K W q p→Bool) (which slice : Bool) (i : ℕ) : Word w :=
  if valid : i<N then ((word (planes z which) slice ⟨i,valid⟩).val:Word w) else 0

theorem pin_read (room : q*(W*p)≤w) (z : Inputs K W q p→Bool) (which slice : Bool) (i : ℕ)
    (b : Fin (w+1)) : (pin which slice i b).elim z id=TraceWords.bits (TraceBanks.wide (column z which slice i)) b := by
  have small : shape W q p slice ≤ w := by cases slice <;>simpa [shape,sliceWidth_eq] using room
  by_cases valid : i<N
  · let v:=word (planes z which) slice ⟨i,valid⟩
    have bound:=v.isLt.trans_le (Nat.pow_le_pow_right (by decide) small)
    simp only [pin,dite_eq_left valid,column,TraceWords.bits,TraceBanks.wide]
    change _=(v.val%2^w).testBit b.val
    rw [Nat.mod_eq_of_lt bound]
    by_cases lo : b.val<shape W q p slice
    · rw [dite_eq_left lo]
      have eqn:=socket_bit (planes z which) slice (⟨i,valid⟩:Fin N) (⟨b.val,lo⟩:Fin _)
      exact eqn.symm.trans (Computability.VPVNP.LiveHeader.testBit_wordBits v ⟨b.val,lo⟩).symm
    · rw [dite_eq_right lo]
      exact (Nat.testBit_lt_two_pow (v.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt lo)))).symm
  · simp [pin,column,valid,TraceWords.bits,TraceBanks.wide]

theorem width_price : Fintype.card (Inputs K W q p)=2*(K*W)*(q*(W*p)) := by
  simp [Inputs,Bit,Slot,Fintype.card_prod];ring

end
end Hierarchy.DescentTerminalChipPins

end OAI
