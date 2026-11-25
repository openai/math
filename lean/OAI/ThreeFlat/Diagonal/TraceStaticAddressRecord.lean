import OAI.ThreeFlat.Diagonal.TraceStaticRecordData
import OAI.ThreeFlat.Diagonal.TraceStaticPorts

namespace OAI
/-! # The row controls of the static trace as physical source addresses -/

namespace ThreeFlat.Diagonal.TraceAddressRecord

open Computability.VPVNP TraceRows TraceRowPackets TraceStaticRow RAM.BitLayout
variable {w p r k d S f : ℕ}

@[simp] theorem interval_eval (a b l h v : ℕ) :
    (interval a b l h).eval v = (decide (l ≤ a*v+b ∧ a*v+b < h)).toNat := by
  by_cases guard : l ≤ a*v+b ∧ a*v+b < h <;>
    simp [interval,Record.eval,Record.test,Record.result,Record.numerator,guard]

@[simp] theorem digit_eval (a b s j v : ℕ) :
    (digit a b s j).eval v = ((b+a*v-s).testBit j).toNat := by
  simp [digit,Record.eval,Record.test,Record.result,Record.numerator]

private theorem decideNat {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (decide P).toNat = (decide Q).toNat := by
  by_cases hp : P
  · simp [hp,h.mp hp]
  · have hq : ¬Q := fun e => hp (h.mpr e)
    simp [hp,hq]

theorem initial_eval (S f : ℕ) (v : Fin (2^d)) (c : InitControl w) :
    (initial S f c).eval v.val = (initControlAt S f v c).toNat := by
  rcases c with ⟨s,b | ⟨b,j⟩⟩ <;> cases b
  · simp only [initial,interval_eval,initControlAt,slotAddress]
    apply decideNat; omega
  · simp only [initial,interval_eval,initControlAt,slotAddress]
    apply decideNat
    split_ifs <;> omega
  · simp [initial,initControlAt,slotAddress,Nat.add_comm]
  · simp [initial,initControlAt,slotAddress,Nat.add_comm]

theorem sort_eval (v : Fin (2^d)) (c : TraceMemoryCircuit.MemoryControl d (w+1)) :
    (sort d c).eval v.val = (TraceMemoryCircuit.controlsAt (w:=w+1) v c).toNat := by
  rcases c with ⟨j,s⟩ | u <;>
    simp [sort,TraceMemoryCircuit.controlsAt,Nat.add_comm]

theorem outer_eval (base S f : ℕ) (v : Fin (2^d)) (c : Outer w p k) :
    (outer d base S f c).eval v.val = (outerAt base S f v c).toNat := by
  rcases c with s | (s | (b | j))
  · simp only [outer,interval_eval,outerAt,slotAddress]
    apply decideNat; omega
  · simp only [outer,interval_eval,outerAt,slotAddress]
    apply decideNat
    split_ifs <;> omega
  · cases b
    · simp only [outer,interval_eval,outerAt,Nat.one_mul,Nat.add_zero]
      apply decideNat; omega
    · simp [outer,outerAt]
  · simp only [outer,interval_eval,outerAt,Nat.one_mul,Nat.add_zero]
    apply decideNat; omega

theorem staticPort_eval (hw : 3≤w+1) (hs : S≤2^w) (hf : f≤2^(w+1)) (base : ℕ)
    (v : Fin (2^d)) (z : TraceStaticRow.Port w p r k d) :
    (staticPort hw base S f z).eval v.val = sourceAddress (portSource hw hs hf base v z) := by
  rcases z with a | ((a | a) | a)
  · exact portRecord_eval _ _ _ _ _
  · exact initial_eval _ _ _ _
  · exact sort_eval (w:=w) _ _
  · exact outer_eval _ _ _ _ _

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
