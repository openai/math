import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRouteIO
import OAI.Computability.NearSquareRoot.PrecisionFlatWalshChildKernel
import OAI.Computability.NearSquareRoot.CRTControlledPositions

/-! # Address bits of an aligned column XOR

The active axis slots occupy consecutive equal-width windows in MSF order.
Their low-to-high offsets are independent of the two spectator ranges. A
column XOR consequently copies an entire masked integer window into another
by bitwise XOR and preserves all other positions, including prefix bits.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode
namespace XorBits
open IntegerMultiplication KernelPass KernelScaleLayout FlatWalshKernel

/-- Little-endian position of the lowest bit of an axis. -/
def offset {a : ℕ} (L : ℕ) (i : Fin (a+1)) := (a-i.val)*L

/-- Apply the lower `width` bits of the source window to the destination. -/
def window (src dst width n : ℕ) := n ^^^ ((n/2^src)%2^width*2^dst)

theorem window_bit (src dst w n i : ℕ) :
    (window src dst w n).testBit i = if dst ≤ i ∧ i < dst+w then
      Bool.xor (n.testBit i) (n.testBit (i-dst+src)) else n.testBit i := by
  simp only [window, Nat.testBit_xor,Nat.testBit_mul_two_pow,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  by_cases lo : dst ≤ i
  · by_cases hi : i < dst+w
    · simp [lo,hi,show i-dst < w by omega]
    · simp [lo,hi,show ¬ i-dst < w by omega]
  · simp [lo]

theorem offset_apart {a : ℕ} {i j : Fin (a+1)} (h : i ≠ j) (L : ℕ) :
    offset L i + L ≤ offset L j ∨ offset L j + L ≤ offset L i := by
  have hi := i.isLt
  have hj := j.isLt
  have nh : i.val ≠ j.val := fun h' => h (Fin.ext h')
  unfold offset
  simp only [← Nat.succ_mul]
  rcases lt_or_gt_of_ne nh with less|more
  · exact Or.inr (Nat.mul_le_mul_right L (by omega))
  · exact Or.inl (Nat.mul_le_mul_right L (by omega))

def little {h : ℕ} (t : Fin h) (b : Fin 2) : Fin (2*h) :=
  ⟨2*h-1-(2*t.val+b.val), by have := t.isLt; omega⟩

theorem slots_offset {a h : ℕ} (j : Fin (a+1)) (t : Fin h) (b : Fin 2) :
    (slots a h (j,t,b)).val = offset (2*h) j + (little t b).val := by
  rw [slots_val, Nat.succ_mul]
  have hs : (a-j.val)*(2*h)+j.val*(2*h) = a*(2*h) := by
    rw [← Nat.add_mul, show a-j.val+j.val = a by omega]
  have lt : 2*t.val+b.val < 2*h := by omega
  dsimp only [little,offset]; omega

private theorem zadd (x y : ZMod 2) : decide (x+y=1) = Bool.xor (decide (x=1)) (decide (y=1)) := by
  fin_cases x <;> fin_cases y <;> decide

/-- Retrieve each bit from its physical source without unpacking the kernel
matrix or enumerating masks. -/
theorem rank_window {a h : ℕ} (g : Fin (a+1) × Fin (a+1)) (ne : g.1 ≠ g.2) (x : Addr (a+1) h) :
    (rank (xorColumn g ∘ x)).val = window (offset (2*h) g.2) (offset (2*h) g.1) (2*h) (rank x).val := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [window_bit]
  by_cases inside : i < (a+1)*(2*h)
  · obtain ⟨⟨j,t,b⟩,eq⟩ := (slots a h).surjective ⟨i,inside⟩
    have he : i = (slots a h (j,t,b)).val := (congrArg Fin.val eq).symm
    rw [he,testBit_rank,testBit_rank]
    have off := slots_offset j t b
    have small := (little t b).isLt
    by_cases target : j = g.1
    · subst j
      have trueSlot : offset (2*h) g.1 ≤ (slots a h (g.1,t,b)).val ∧
          (slots a h (g.1,t,b)).val < offset (2*h) g.1 + 2*h := by omega
      have select : (slots a h (g.1,t,b)).val - offset (2*h) g.1 + offset (2*h) g.2 = (slots a h (g.2,t,b)).val := by
        rw [off,slots_offset]; omega
      simp only [trueSlot,ite_true,select,testBit_rank,Function.comp_apply,xorColumn,ne,ne_eq,not_false_eq_true,true_and,ite_true,zadd]
    · have gaps := offset_apart target (2*h)
      have falseSlot : ¬(offset (2*h) g.1 ≤ (slots a h (j,t,b)).val ∧
          (slots a h (j,t,b)).val < offset (2*h) g.1 + 2*h) := by omega
      simp [falseSlot,Function.comp_apply,xorColumn,target]
  · have limit : offset (2*h) g.1+2*h ≤ (a+1)*(2*h) := by
      unfold offset; rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    have no : ¬(offset (2*h) g.1 ≤ i ∧ i < offset (2*h) g.1 + 2*h) := by omega
    rw [ite_eq_right no]
    have power := Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt inside)
    rw [Nat.testBit_eq_false_of_lt ((rank _).isLt.trans_le power), Nat.testBit_eq_false_of_lt ((rank _).isLt.trans_le power)]

/-- One invocation of a packed position gate. Position `u` inside each slot is
numbered from the least significant end, exactly as in `window`. -/
def gate {A L : ℕ} (dst src : Fin A) (ne : dst ≠ src) : Controlled.PositionXor (Fin A) (Fin L) :=
  ⟨src,dst,ne.symm,some,by intro i j _ hi hj; exact (Option.some.inj hi).trans (Option.some.inj hj).symm⟩

def read {a : ℕ} (L n : ℕ) (pos : Fin (a+1) × Fin L) : Bool := n.testBit (offset L pos.1+pos.2.val)

theorem gate_window {a L : ℕ} (dst src : Fin (a+1)) (ne : dst ≠ src) (n : ℕ) :
    (gate dst src ne).act (read L n) = read L (window (offset L src) (offset L dst) L n) := by
  funext p
  obtain ⟨i,j⟩ := p
  by_cases hi : i = dst
  · subst i
    simp [gate,Controlled.PositionXor.act,read,window_bit,Nat.add_comm]
  · have sep := offset_apart hi L
    have falseSlot : ¬(offset L dst ≤ offset L i+j.val ∧ offset L i+j.val < offset L dst+L) := by omega
    simp [gate,Controlled.PositionXor.act,read,window_bit,hi,falseSlot]

/-- Spectator bits above the active span are preserved even for a prefix range
whose size is not a power of two. -/
theorem window_mod {src dst L K : ℕ} (hsrc : src+L ≤ K) (hdst : dst+L ≤ K) (n : ℕ) :
    n/2^K*2^K + window src dst L (n%2^K) = window src dst L n := by
  have mask (v : ℕ) : (v/2^src)%2^L*2^dst < 2^K := by
    have h := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt (v/2^src) (Nat.two_pow_pos L)) (Nat.two_pow_pos dst)
    rw [← pow_add] at h
    exact h.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have field : window src dst L (n%2^K) < 2^K :=
    Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) (mask _)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm (n/2^K), Nat.testBit_two_pow_mul_add _ field, window_bit]
  by_cases hi : i<K
  · rw [ite_eq_left hi,window_bit]
    by_cases active : dst ≤ i ∧ i < dst+L
    · have low : i-dst+src < K := by omega
      simp [active,Nat.testBit_mod_two_pow,hi,low]
    · simp [active,hi]
  · have inactive : ¬(dst ≤ i ∧ i < dst+L) := by omega
    simp [hi,inactive,window_bit,Nat.testBit_div_two_pow,Nat.sub_add_cancel (Nat.le_of_not_gt hi)]

/-- Full physical source ordinal. The leading range is retained inside the
quotient, and the possibly nonbinary suffix is restored by multiplication
and remainder after the packed bit operation. -/
theorem xorIndex_eq {a : ℕ} (g : Fin (a+1) × Fin (a+1)) (ne : g.1 ≠ g.2) (s : Shape) (n : ℕ) :
    let L := grow (a+1) (s.level-1)
    xorIndex a g s n = window (offset L g.2) (offset L g.1) L (n/s.suff)*s.suff+n%s.suff := by
  intro L
  let h := (a+1)^(s.level-1)
  let K := (a+1)*(2*h)
  let u := n/s.suff
  let r : Fin (2^K) := ⟨u%2^K,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have within (i : Fin (a+1)) : offset (2*h) i+2*h ≤ K := by
    unfold offset K;rw [← Nat.succ_mul];exact Nat.mul_le_mul_right _ (by omega)
  change (u/2^K*2^K+(rank (xorColumn g ∘ address a h r)).val)*s.suff+n%s.suff =
    window (offset (2*h) g.2) (offset (2*h) g.1) (2*h) u*s.suff+n%s.suff
  rw [rank_window g ne,rank_address]
  rw [show r.val=u%2^K from rfl, window_mod (within g.2) (within g.1)]

/-- A single source bit conditionally toggles a single destination bit. -/
def single (src dst j n : ℕ) := if n.testBit (src+j) then n ^^^ 2^(dst+j) else n

theorem single_bit (src dst j n i : ℕ) :
    (single src dst j n).testBit i = if i=dst+j then
      Bool.xor (n.testBit i) (n.testBit (src+j)) else n.testBit i := by
  cases h : n.testBit (src+j) <;> by_cases he : i=dst+j <;>
    simp [single,h,he,eq_comm]

/-- A step on the current record maps its ordinal back through this single
toggle and then through the earlier low positions. -/
theorem window_single {src dst L j : ℕ} (disjoint : src+L ≤ dst ∨ dst+L ≤ src) (bound : j<L) (n : ℕ) :
    window src dst j (single src dst j n) = window src dst (j+1) n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [window_bit,window_bit,single_bit,single_bit]
  by_cases same : i=dst+j
  · subst i
    simp [Nat.add_comm]
  · by_cases lo : dst ≤ i ∧ i<dst+j
    · have hi : dst ≤ i ∧ i<dst+(j+1) := by omega
      have clean : i-dst+src ≠ dst+j := by omega
      simp [same,clean,lo,hi]
    · have hi : ¬(dst ≤ i ∧ i<dst+(j+1)) := by omega
      simp [same,lo,hi]

@[simp] theorem window_zero (src dst n : ℕ) : window src dst 0 n = n := by simp [window,Nat.mod_one]

end XorBits
end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
