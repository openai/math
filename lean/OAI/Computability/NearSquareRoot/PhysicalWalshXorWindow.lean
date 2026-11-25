import OAI.Computability.NearSquareRoot.PhysicalWalshXorSweep
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeXorBits
import OAI.Computability.NearSquareRoot.SynchronizedBitAddress
import OAI.Computability.NearSquareRoot.CRTControlledFlatNumber
import OAI.Computability.NearSquareRoot.CRTControlledPrefixStage

/-! # Numeric address of the emitted aligned XOR window

The low third of the native window is a scratch chunk. The high third is the
source and the middle third is the destination. The enclosing stream may have
arbitrary positive spectator strides and any number of leading rows.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorSweep

open Controlled Controlled.PositionProgram Controlled.PositionPreparation PhysicalWalshNode

/-- The actual emitted gate reads one aligned window in little-endian order.
When `k` is not a multiple of three, its remaining high bits stay fixed. -/
theorem directed_bits (k n : ℕ) :
    directed (gate (k/3)) (fun i : Fin k => n.testBit i.val) =
      fun i => (XorBits.window (2*(k/3)) (k/3) (k/3) n).testBit i.val := by
  funext i
  obtain ⟨v,rfl⟩ := (threeChunksWithTail k).symm.surjective i
  rcases v with ⟨c,j⟩|j
  · have hj := j.isLt
    fin_cases c
    · simp [gate,directed,threeChunksWithTail_bulk,XorBits.window_bit,show ¬ k/3 ≤ j.val by omega]
    · have h1 : k/3 ≤ j.val+k/3 ∧ j.val+k/3 < k/3+k/3 := by omega
      simp [gate,directed,chunkWord,xorFrom,threeChunksWithTail_bulk,XorBits.window_bit,h1,Nat.mul_comm 2]
    · have h : ¬ (j.val+(k/3)*2 < k/3+k/3) := by omega
      simp [gate,directed,threeChunksWithTail_bulk,XorBits.window_bit,h]
  · have h : ¬ (3*(k/3)+j.val < k/3+k/3) := by omega
    simp [directed,threeChunksWithTail_tail,XorBits.window_bit,h]

/-- Address of one labeled coordinate of the source, destination, or scratch
group. The Walsh kernel numbers these groups in MSF order. -/
def windowSlot (L : ℕ) (p : Fin 3 × Fin L) : Fin (3*L) :=
  ⟨XorBits.offset L p.1 + p.2.val, by
    have upper := Nat.mul_le_mul_right L (Nat.sub_le 2 p.1.val)
    have low := p.2.isLt
    unfold XorBits.offset
    omega⟩

theorem directed_gate_window (L n : ℕ) :
    directed (gate L) (fun i : Fin (3*L) => n.testBit i.val) ∘ windowSlot L =
      (XorBits.gate (1:Fin 3) 0 (by decide)).act (XorBits.read L n) := by
  funext p
  rw [XorBits.gate_window]
  have e := congrFun (directed_bits (3*L) n) (windowSlot L p)
  simpa [Function.comp_def,windowSlot,XorBits.read,XorBits.offset] using e

/-- Source ordinal read by the emitted gate on one native row. -/
def directedIndex (k : ℕ) (i : Fin (2^k)) : Fin (2^k) :=
  (BoxFin.addressDigits k).symm (directed (gate (k/3)) (BoxFin.addressDigits k i))

theorem directedIndex_window (k : ℕ) (i : Fin (2^k)) : (directedIndex k i).val =
    XorBits.window (2*(k/3)) (k/3) (k/3) i.val := by
  have mask := Nat.mul_lt_mul_of_pos_right (Nat.mod_lt (i.val/2^(2*(k/3))) (Nat.two_pow_pos (k/3))) (Nat.two_pow_pos (k/3))
  rw [←pow_add] at mask
  have fit : XorBits.window (2*(k/3)) (k/3) (k/3) i.val < 2^k := Nat.xor_lt_two_pow i.isLt
    (mask.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  apply congrArg Fin.val (a₂ := (⟨_,fit⟩ : Fin (2^k)))
  apply (BoxFin.addressDigits k).injective
  rw [directedIndex,Equiv.apply_symm_apply]
  exact directed_bits k i.val

/-- Restrict a flat address to its window, preserving the full leading
ordinal and the low spectator remainder in the reconstructed read address. -/
def directedRead (L suffix n : ℕ) : ℕ :=
  ((n/suffix/2^(3*L))*2^(3*L) +
    (directedIndex (3*L) ⟨n/suffix%2^(3*L),Nat.mod_lt _ (Nat.two_pow_pos _)⟩).val)*suffix+n%suffix

theorem directedRead_window (L suffix n : ℕ) :
    directedRead L suffix n = XorBits.window (2*L) L L (n/suffix)*suffix+n%suffix := by
  unfold directedRead
  rw [directedIndex_window,show (3*L)/3 = L by omega,XorBits.window_mod (by omega) (by omega)]

/-- In the packed array, pulling back a native row holds its high ordinal
and its low spectator fixed. The spectator stride can be nonbinary. -/
theorem directedRead_at (L S pref : ℕ) (i : Fin (2^(3*L))) (low : Fin S) :
    directedRead L S ((pref*2^(3*L)+i.val)*S+low.val) =
      (pref*2^(3*L)+(directedIndex (3*L) i).val)*S+low.val := by
  have quotient (A : ℕ) (z : Fin A) (x : ℕ) : (x*A+z.val)/A = x := by
    rw [Nat.mul_comm x,Nat.mul_add_div z.pos,Nat.div_eq_of_lt z.isLt,Nat.add_zero]
  have residue (A : ℕ) (z : Fin A) (x : ℕ) : (x*A+z.val)%A = z.val := by
    rw [Nat.mul_comm x,Nat.mul_add_mod,Nat.mod_eq_of_lt z.isLt]
  simp only [directedRead,quotient,residue]

/-- Flat record ordinal of the high row, native Boolean address, and spectator. -/
def wordAddress (L S pref : ℕ) (low : Fin S) (w : Fin (3*L) → Bool) : ℕ :=
  (pref*2^(3*L)+((BoxFin.addressDigits (3*L)).symm w).val)*S+low.val

theorem wordAddress_directed (L S pref : ℕ) (low : Fin S) (w : Fin (3*L) → Bool) :
    wordAddress L S pref low (directed (gate L) w) =
      directedRead L S (wordAddress L S pref low w) := by
  unfold wordAddress
  rw [directedRead_at]
  simp [directedIndex]

open IntegerMultiplication.Adic IntegerMultiplication.Packed

/-- The actual P192 binary row in the flat stream has precisely the ordinal
used for the native Boolean input to the emitted opcode interpreter. -/
theorem wordAddress_prefix {P L S : ℕ} (pref : Block 2 P) (b : Block 2 (3*L)) (low : Fin S) :
    wordAddress L S (number pref) low (prefixBit b) =
      number ((prefixView rfl).cast (pref,b))*S+low.val := by
  have bits : (BoxFin.addressDigits (3*L)).symm (prefixBit b) = flatAddress 2 (3*L) b := by
    apply (BoxFin.addressDigits (3*L)).injective
    rw [Equiv.apply_symm_apply]
    funext i
    change prefixBit b i = (flatAddress 2 (3*L) b).val.testBit i.val
    rw [prefixBit_number,flatAddress_val]
  unfold wordAddress
  rw [bits,flatAddress_val]
  change _ = number ((tile 2 P (3*L)).cast (pref,b))*S+low.val
  rw [tile_n,Nat.mul_comm (number pref)]

/-- The emitted schedule pulls back a flat row through the numeric window.
This applies to data in any type, so each record may have many physical bits. -/
theorem program_rows_at {Y : Type*} (L S pref G : ℕ) (pos : 0 < G) (low : Fin S) (f : ℕ → Y) :
    (program L G).foldl (fun b q => b ∘ fun w => act G w q) (f ∘ wordAddress L S pref low) =
      fun w => f (directedRead L S (wordAddress L S pref low w)) := by
  have e := program_rows (k := 3*L) pos (f ∘ wordAddress L S pref low)
  simpa [Function.comp_def,wordAddress_directed] using e

/-- A Walsh gate at the two aligned offsets reads exactly the padded native
program's source address, regardless of the enclosing prefix or suffix. -/
theorem xorIndex_directed {a : ℕ} (g : Fin (a+1) × Fin (a+1)) (ne : g.1 ≠ g.2) (s : Shape)
    (src : XorBits.offset (grow (a+1) (s.level-1)) g.2 = 2*grow (a+1) (s.level-1))
    (dst : XorBits.offset (grow (a+1) (s.level-1)) g.1 = grow (a+1) (s.level-1)) (n : ℕ) :
    xorIndex a g s n = directedRead (grow (a+1) (s.level-1)) s.suff n := by
  rw [XorBits.xorIndex_eq g ne,directedRead_window]
  rw [src,dst]

/-- Move an integer window above a preserved low bit field. -/
theorem window_shift (h src dst L u : ℕ) :
    XorBits.window (h+src) (h+dst) L u =
      XorBits.window src dst L (u/2^h)*2^h + u%2^h := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.mul_comm (XorBits.window ..), Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
    XorBits.window_bit]
  by_cases low : i < h
  · have outside : ¬(h+dst ≤ i ∧ i < h+dst+L) := by omega
    simp [low,outside,Nat.testBit_mod_two_pow]
  · have inside : (h+dst ≤ i ∧ i < h+dst+L) ↔ (dst ≤ i-h ∧ i-h < dst+L) := by omega
    rw [ite_eq_right low,XorBits.window_bit,if_congr inside rfl rfl]
    simp only [Nat.testBit_div_two_pow]
    congr 1
    · congr 1 <;> congr 1 <;> omega
    · congr 1; omega

/-- A native three-field gate acts on an interior window above an arbitrary
low spectator stride and below an arbitrary high prefix. -/
theorem directedRead_shift (L h suffix n : ℕ) :
    directedRead L (suffix*2^h) n =
      XorBits.window (h+2*L) (h+L) L (n/suffix)*suffix+n%suffix := by
  rw [directedRead_window,window_shift,Nat.div_div_eq_div_mul,Nat.mod_mul]
  ring

theorem xorIndex_directed_shift {a : ℕ} (g : Fin (a+1) × Fin (a+1)) (ne : g.1 ≠ g.2)
    (s : Shape) (h : ℕ)
    (src : XorBits.offset (grow (a+1) (s.level-1)) g.2 = h+2*grow (a+1) (s.level-1))
    (dst : XorBits.offset (grow (a+1) (s.level-1)) g.1 = h+grow (a+1) (s.level-1)) (n : ℕ) :
    xorIndex a g s n = directedRead (grow (a+1) (s.level-1)) (s.suff*2^h) n := by
  rw [XorBits.xorIndex_eq g ne,directedRead_shift,src,dst]

/-- MSF slot 1 feeds slot 2, with slot 3 as the low scratch field. Slot 0
is available as an unchanged high prefix; all later slots join the stride. -/
theorem xorIndex_interior {a : ℕ} (wide : 3 ≤ a) (s : Shape) (n : ℕ) :
    let L := grow (a+1) (s.level-1)
    xorIndex a (⟨2,by omega⟩,⟨1,by omega⟩) s n = directedRead L (s.suff*2^((a-3)*L)) n := by
  intro L
  apply xorIndex_directed_shift _ (by intro e; exact (by decide : (2:ℕ) ≠ 1) (congrArg Fin.val e)) s ((a-3)*L) _ _ n
  · change (a-1)*L = (a-3)*L+2*L
    rw [←Nat.add_mul,show a-3+2 = a-1 by omega]
  · change (a-2)*L = (a-3)*L+L
    rw [←Nat.succ_mul,show (a-3).succ = a-2 by omega]

end PhysicalWalsh.XorSweep

end NearSquareRoot
end Computability
end OAI
