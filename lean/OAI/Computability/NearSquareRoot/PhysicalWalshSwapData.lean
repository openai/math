import OAI.Computability.NearSquareRoot.PhysicalWalshSwapStage
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefix
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapSource
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapCodec

/-! # Actual source ordinals and record volumes of the upper-slot interchange -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.SlotSwap

open IntegerMultiplication Code Strip Strip.Dims Adic Space
open ElementarySchedule (slotWidth)

variable {a : ℕ} (W D : ℕ) (i j : Fin (a+1))

def wingSource (z : Geometry) := SwapOrdinal.source (2^z.wing) (room (field 2 z.gap)) 1

def moved (s : Shape) (k : ℕ) :=
  let c := reserve D (a+1) s
  let b := stride i j s c
  wingSource (geometry W i j s c) (k/b)*b+k%b

def upper (s : Shape) (x : Data s) : Data s :=
  let L := slotWidth (a+1) s
  let c := reserve D (a+1) s
  x ∘ SwapWord.stride s (SwapWord.run (XorBits.offset L i+c) (XorBits.offset L j+c) (L-c))

private theorem factors (s : Shape) (order : j.val < i.val) :
    let L := slotWidth (a+1) s
    let c := reserve D (a+1) s
    let lo := XorBits.offset L i+c
    let hi := XorBits.offset L j+c
    let z := geometry W i j s c
    lo+z.wing ≤ hi ∧ z.gap=hi-(lo+z.wing) ∧ stride i j s c = 2^lo*s.suff := by
  intro L c lo hi z
  have cut : c ≤ L := min_le_left ..
  have ix := i.isLt
  have jx := j.isLt
  have idx : a-i.val+1+(i.val-j.val-1)=a-j.val := by omega
  have h := congrArg (fun t => t*L) idx
  simp only [Nat.add_mul,Nat.one_mul] at h
  have mg : min i.val j.val = j.val := min_eq_right order.le
  have mx : max i.val j.val = i.val := max_eq_left order.le
  simp only [z,hi,lo,geometry,XorBits.offset,stride,trailBits,mg,mx,Nat.add_sub_cancel]
  dsimp only [L] at h cut ⊢
  omega

theorem moved_eq (s : Shape) (order : j.val < i.val) (k : ℕ) :
    let L := slotWidth (a+1) s
    let c := reserve D (a+1) s
    moved W D i j s k = SwapWord.stride s (SwapWord.run (XorBits.offset L i+c) (XorBits.offset L j+c) (L-c)) k := by
  obtain ⟨apart,gap,width⟩ := factors W D i j s order
  let c := reserve D (a+1) s
  let z := geometry W i j s c
  let b := stride i j s c
  have factor := SwapWord.source_stride (2^z.wing) (2^z.gap) 1 b k
  rw [one_mul] at factor
  change SwapOrdinal.source (2^z.wing) (room (field 2 z.gap)) 1 (k/b)*b+k%b = _
  rw [show room (field 2 z.gap)=2^z.gap from (space _).symm.trans (lineSize ..),← factor]
  dsimp only [b,c,z]
  rw [gap,width,SwapWord.rectangular _ _ _ _ _ apart]
  rfl

theorem moved_lt (s : Shape) (positive : 0<s.level) (order : j.val < i.val) (k : ℕ)
    (hk : k<SwapPrefix.length (a+1) W s) : moved W D i j s k < SwapPrefix.length (a+1) W s := by
  let L := slotWidth (a+1) s
  let c := reserve D (a+1) s
  let lo := XorBits.offset L i+c
  let hi := XorBits.offset L j+c
  let z := geometry W i j s c
  have cut : c ≤ L := min_le_left ..
  obtain ⟨apart,_,_⟩ := factors W D i j s order
  have axes : (a+1)*L = grow (a+1) s.level := by
    dsimp [L,slotWidth,grow];rw [Nat.mul_left_comm (a+1) 2,← pow_succ',Nat.sub_add_cancel positive]
  have ix : (a-j.val)*L+L ≤ (a+1)*L := by
    rw [← Nat.succ_mul]
    exact Nat.mul_le_mul_right L (by omega)
  have inside : hi+(L-c) ≤ grow (a+1) s.level := by dsimp only [hi,XorBits.offset];omega
  have eq := (SwapWord.rectangular lo hi (L-c) s k apart).symm
  rw [moved_eq W D i j s order k,eq]
  rw [SwapPrefix.length,inner,← Nat.mul_assoc] at hk ⊢
  apply (SwapOrdinal.binary_source_lt_full lo hi (L-c) (grow (a+1) s.level) s.suff (groups W s) k s.suff_pos apart inside).mpr
  exact hk

def bank (s : Shape) (x : Data s) : Packet where
  geometry := geometry W i j s (reserve D (a+1) s)
  width := wordWidth i j s (reserve D (a+1) s)
  bits := PhysicalWalshSwapCodec.payload (stride i j s (reserve D (a+1) s)) x
  exactWidth := PhysicalWalshSwapCodec.payload_length _ x

theorem bank_volume (s : Shape) (x : Data s) (ne : i ≠ j) (hs : 0<s.level) :
    (bank W D i j s x).volume = SwapPrefix.paddedSize (a+1) W s * (2*(s.w+1)) := by
  change (geometry _ _ _ _ _).grid.count * (stride _ _ _ _ * _) = _
  rw [← Nat.mul_assoc, volume_eq (W:=W) i j ne s hs (reserve D (a+1) s) (min_le_left ..)]
  rfl

theorem bank_room (s : Shape) (x : Data s) (ne : i ≠ j) (hs : 0<s.level) :
    (bank W D i j s x).geometry.wing = 0 ∨
      (size (bank W D i j s x).geometry.header+1)^D ≤ (bank W D i j s x).width := by
  by_cases large : Controlled.payloadBits D (Header.scale (a+1) s) ≤ slotWidth (a+1) s
  · exact Or.inr (reserve_fit D i j ne s hs large)
  · exact Or.inl (by simp [bank,geometry,reserve,min_eq_left (Nat.le_of_not_ge large)])

theorem lane_volume_le (A W d : ℕ) (s : Shape) :
    (SwapPrefix.paddedSize A W s+1)*(s.w+1) ≤ 2*allowance A d s := by
  have n := (SwapPrefix.paddedSize_le A W s).trans (Nat.mul_le_mul_left 2 (SwapPrefix.length_le_count A W s))
  calc
    _ ≤ (2*(count A s+1))*(grow A s.level+s.w+1) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.le_add_right ..)

theorem bank_cost {ρ : ℝ} (nonneg : 0 ≤ ρ) (s : Shape) (x : Data s) (ne : i ≠ j) (hs : 0<s.level) :
    let b := bank W D i j s x
    ⌈(b.volume : ℝ)*((b.geometry.wing+1:ℕ):ℝ)^ρ⌉₊+1 ≤ 5*(wideExtra ρ (a+1) s+1) := by
  intro b
  have n := (SwapPrefix.paddedSize_le (a+1) W s).trans (Nat.mul_le_mul_left 2 (SwapPrefix.length_le_count (a+1) W s))
  have volume : b.volume ≤ 4*((count (a+1) s+1)*(s.w+1)) := by
    rw [bank_volume W D i j s x ne hs]
    calc
      _ = (2*SwapPrefix.paddedSize (a+1) W s)*(s.w+1) := by ring
      _ ≤ (4*(count (a+1) s+1))*(s.w+1) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have wing : b.geometry.wing+1 ≤ slotWidth (a+1) s+1 := Nat.succ_le_succ (Nat.sub_le ..)
  apply InterchangePayload.ceil_charge (C:=4)
  change (b.volume:ℝ)*((b.geometry.wing+1:ℕ):ℝ)^ρ ≤
    (4:ℝ)*(((((count (a+1) s+1)*(s.w+1):ℕ):ℝ))*((slotWidth (a+1) s+1:ℕ):ℝ)^ρ)
  rw [← mul_assoc]
  exact mul_le_mul (by exact_mod_cast volume)
    (Real.rpow_le_rpow (by positivity) (by exact_mod_cast wing) nonneg) (by positivity) (by positivity)

end PhysicalWalshNode.SlotSwap

end NearSquareRoot
end Computability
end OAI
