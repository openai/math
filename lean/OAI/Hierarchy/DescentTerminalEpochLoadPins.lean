import OAI.Hierarchy.DescentTerminalEpochHeader
import OAI.ThreeFlat.Diagonal.TraceBanks

namespace OAI
/-! # Physical bit projection on the fixed profile shelves -/
namespace Hierarchy.DescentTerminalEpochHeader
open DescentTerminalEpochBits DescentTerminalEpochChart Computability.VPVNP.BurstRAM
open ThreeFlat.Diagonal
open scoped Classical
noncomputable section
variable {A : Type}

theorem raw_digit {C n : ℕ} (z : Pins C n→Bool) (i : Fin n) (j : Fin (width C)) :
    (raw z i).testBit j.val=z (i,j) :=
  congrFun ((wordBits (width C)).apply_symm_apply (fun b=>z (i,b))) j

def loadPin (w : ℕ) : List (Source A) → ℕ → Fin (w+1) → A ⊕ Bool
  | [],_,_=>.inr false
  | a::ts,i,b=>if i < DescentDyadicSpan.span a.seats then
      if live : i < a.seats then
        if bit : b.val < width a.C then .inl (a.pin (⟨i,live⟩,⟨b.val,bit⟩)) else .inr false
      else .inr false
    else loadPin w ts (i-DescentDyadicSpan.span a.seats) b

theorem load_pin (w : ℕ) (ts : List (Source A)) (z : A→Bool) (wide : ∀a∈ts,width a.C ≤ w)
    (i : ℕ) (b : Fin (w+1)) :
    (loadPin w ts i b).elim z id=TraceWords.bits (TraceBanks.wide (load w z ts i)) b := by
  induction ts generalizing i with
  | nil=>simp [loadPin,load,TraceWords.bits,TraceBanks.wide]
  | cons a ts ih=>
    by_cases own : i < DescentDyadicSpan.span a.seats
    · simp only [loadPin,load,ite_eq_left own]
      by_cases live : i < a.seats
      · let j : Fin a.seats := ⟨i,live⟩
        have value : (header w a.C a.seats (z∘a.pin) i).val=raw (z∘a.pin) j :=
          header_word w (wide a (by simp)) _ j
        change _=(header w a.C a.seats (z∘a.pin) i).val.testBit b.val
        rw [value,dite_eq_left live]
        by_cases bit : b.val < width a.C
        · simpa [bit,j] using (raw_digit (z∘a.pin) j ⟨b.val,bit⟩).symm
        · simp only [dite_eq_right bit,Sum.elim_inr,id_eq]
          symm
          have size : raw (z∘a.pin) j < 2^width a.C := ((wordBits _).symm _).isLt
          exact Nat.testBit_lt_two_pow (size.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
      · simp [live,header,TraceWords.bits,TraceBanks.wide]
    · simpa only [loadPin,load,ite_eq_right own] using ih (fun a h=>wide a (by simp [h])) _

end
end Hierarchy.DescentTerminalEpochHeader

end OAI
