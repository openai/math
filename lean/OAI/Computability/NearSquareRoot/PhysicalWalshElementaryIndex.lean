import OAI.Computability.NearSquareRoot.PhysicalWalshElementarySchedule
import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryOrdinal
import Mathlib.Data.Nat.Bitwise

/-! # The effect of a physical elementary gate on an ordinal

A record's ordinal can be read as a prefix, a higher bit, an intervening
gap, a lower bit, and a suffix. Toggling either bit, conditionally on the
other, gives exactly the corresponding XOR on the binary address above the
possibly non-power-of-two spectator stride. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.ElementaryIndex

open PhysicalWalsh.ElementaryGate (rank natAction Bits2)

/-- The source bit and destination bit are numbered from the low end of the address. -/
def toggle (src dst stride n : ℕ) :=
  (if (n/stride).testBit src then (n/stride) ^^^ 2^dst else n/stride)*stride+n%stride

private theorem div_keep (d a b : ℕ) (hd : 0 < d) :
    (a*d+b)/d = a + b/d := by rw [Nat.mul_comm a d,Nat.mul_add_div hd]

private theorem xor_one (a v : ℕ) (hv : v < 2) : (a*2+v) ^^^ 1 = a*2+(1-v) := by
  have div : ((a*2+v) ^^^ 1)/2 = a := by rw [Nat.xor_div_two]; simp; omega
  have rem := @Nat.xor_mod_two_eq (a*2+v) 1
  omega

private theorem toggle_digit (dest stride outer v tail : ℕ) (hs : 0 < stride) (hv : v < 2)
    (ht : tail < 2^dest*stride) :
    let n := (outer*2+v)*(2^dest*stride)+tail
    (n/stride ^^^ 2^dest)*stride+n%stride =
      (outer*2+(1-v))*(2^dest*stride)+tail := by
  intro n
  let m := 2^dest
  have hm : 0 < m := pow_pos (by decide) _
  have small : tail/stride < m := (Nat.div_lt_iff_lt_mul hs).mpr ht
  have quo : n/stride = (outer*2+v)*m + tail/stride := by
    unfold n; rw [← Nat.mul_assoc,div_keep _ _ _ hs]
  have remain : n%stride = tail%stride := by
    unfold n; rw [← Nat.mul_assoc, Nat.mul_add_mod_self_right]
  let y := n/stride ^^^ 2^dest
  have yq : y/m = outer*2+(1-v) := by
    change (n/stride ^^^ 2^dest)/2^dest = _
    rw [Nat.xor_div_two_pow, quo]
    change (((outer*2+v)*m + tail/stride)/m ^^^ m/m) = _
    rw [div_keep m _ _ hm,Nat.div_eq_of_lt small, Nat.add_zero, Nat.div_self hm, xor_one _ _ hv]
  have yr : y%m = tail/stride := by
    change (n/stride ^^^ 2^dest)%2^dest = _
    rw [Nat.xor_mod_two_pow, quo]
    change (((outer*2+v)*m + tail/stride)%m ^^^ m%m) = _
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt small,Nat.mod_self,Nat.xor_zero]
  have eq := Nat.div_add_mod' y m
  rw [yq,yr] at eq
  change y*stride+_ = _
  rw [← eq,remain,Nat.add_mul,Nat.add_assoc,Nat.div_add_mod']
  simp only [m,Nat.mul_assoc]

private theorem read_digit (pos stride outer v tail : ℕ) (hs : 0 < stride) (hv : v < 2)
    (ht : tail < 2^pos*stride) :
    (((outer*2+v)*(2^pos*stride)+tail)/stride).testBit pos = decide (v=1) := by
  have small := (Nat.div_lt_iff_lt_mul hs).mpr ht
  rw [Nat.testBit_eq_decide_div_mod_eq,← Nat.mul_assoc,div_keep _ _ _ hs,div_keep _ _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt small, Nat.add_zero,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hv]

theorem dimensions {lo hi : ℕ} (h : lo < hi) : 2^(hi-(lo+1))*2*2^lo = 2^hi := by
  rw [← pow_succ, ← pow_add, show hi-(lo+1)+1+lo = hi by omega]

private theorem upper_split {lo hi stride p h g l b : ℕ} (lowHigh : lo < hi) :
    let G := 2^(hi-(lo+1))
    let B := 2^lo*stride
    rank G B p h g l b = (p*2+h)*(2^hi*stride) + ((g*2+l)*B+b) := by
  intro G B
  rw [← dimensions lowHigh]
  unfold rank G B
  ring

private theorem upper_small {lo hi stride g l b : ℕ} (lowHigh : lo < hi)
    (hg : g < 2^(hi-(lo+1))) (hl : l < 2) (hb : b < 2^lo*stride) :
    (g*2+l)*(2^lo*stride)+b < 2^hi*stride := by
  have h := calc
    (g*2+l)*(2^lo*stride)+b < (g*2+l+1)*(2^lo*stride) := by rw [Nat.succ_mul]; omega
    _ ≤ (2^(hi-(lo+1))*2)*(2^lo*stride) := Nat.mul_le_mul_right _ (by omega)
    _ = 2^hi*stride := by rw [← Nat.mul_assoc,dimensions lowHigh]
  exact h

/-- A high control bit selects whether the low bit is complemented. -/
theorem low_target {lo hi stride p h g l b : ℕ} (lowHigh : lo < hi) (hs : 0 < stride)
    (hh : h < 2) (hg : g < 2^(hi-(lo+1))) (hl : l < 2) (hb : b < 2^lo*stride) :
    let G := 2^(hi-(lo+1))
    let B := 2^lo*stride
    rank G B p h g (if h=1 then 1-l else l) b = toggle hi lo stride (rank G B p h g l b) := by
  intro G B
  have e := upper_split (p:=p) (h:=h) (g:=g) (l:=l) (b:=b) (stride:=stride) lowHigh
  have small := upper_small lowHigh hg hl hb
  change rank G B p h g l b = _ at e
  have read : ((rank G B p h g l b)/stride).testBit hi = decide (h=1) := by
    rw [e,read_digit hi stride p h _ hs hh small]
  unfold toggle
  rw [read]
  by_cases yes : h = 1
  · simp only [yes,decide_true, ↓reduceIte]
    exact (toggle_digit lo stride ((p*2+1)*G+g) l b hs hl hb).symm
  · simp [yes, Nat.div_add_mod']

/-- A low control bit selects whether the high bit is complemented. -/
theorem high_target {lo hi stride p h g l b : ℕ} (lowHigh : lo < hi) (hs : 0 < stride)
    (hh : h < 2) (hg : g < 2^(hi-(lo+1))) (hl : l < 2) (hb : b < 2^lo*stride) :
    let G := 2^(hi-(lo+1))
    let B := 2^lo*stride
    rank G B p (if l=1 then 1-h else h) g l b = toggle lo hi stride (rank G B p h g l b) := by
  intro G B
  have read := read_digit lo stride ((p*2+h)*G+g) l b hs hl hb
  change ((rank G B p h g l b)/stride).testBit lo = decide (l=1) at read
  unfold toggle
  rw [read]
  by_cases yes : l = 1
  · simp only [yes,decide_true, ↓reduceIte]
    have e := upper_split (p:=p) (h:=h) (g:=g) (l:=1) (b:=b) (stride:=stride) lowHigh
    have f := upper_split (p:=p) (h:=1-h) (g:=g) (l:=1) (b:=b) (stride:=stride) lowHigh
    change rank G B p h g 1 b = _ at e
    change rank G B p (1-h) g 1 b = _ at f
    rw [e,f]
    exact (toggle_digit hi stride p h _ hs hh (upper_small lowHigh hg (by decide : 1<2) hb)).symm
  · simp [yes, Nat.div_add_mod']

private def flip (v : Fin 2) : Fin 2 := ⟨1-v.val, by omega⟩

/-- The finite four-lane selector for fixed source and destination slots. -/
def rewire {A : ℕ} (src dst : Fin A) (v : Bits2) : Bits2 :=
  if src.val < dst.val then (v.1, if v.1.val=1 then flip v.2 else v.2)
  else (if v.2.val=1 then flip v.1 else v.1, v.2)

private theorem coordinates (G B n : ℕ) :
    rank G B (n/B/2/G/2) (n/B/2/G%2) (n/B/2%G) (n/B%2) (n%B) = n := by
  unfold rank
  rw [Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod']

/-- The finite gate lookup is precisely a one-bit XOR of the word quotient
for every natural ordinal, with arbitrary spectator stride. -/
theorem natAction_bits {A : ℕ} (src dst : Fin A) (ne : src ≠ dst) (s : Shape) (t n : ℕ) :
    natAction (ElementarySchedule.gap src dst s t) (ElementarySchedule.suff src dst s t) (rewire src dst) n =
      toggle (ElementarySchedule.offset src s t) (ElementarySchedule.offset dst s t) s.suff n := by
  let G := ElementarySchedule.gap src dst s t
  let B := ElementarySchedule.suff src dst s t
  let p := n/B/2/G/2
  let h := n/B/2/G%2
  let g := n/B/2%G
  let l := n/B%2
  let b := n%B
  have hh : h < 2 := Nat.mod_lt _ (by decide)
  have hg : g < G := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hl : l < 2 := Nat.mod_lt _ (by decide)
  have hb : b < B := Nat.mod_lt _ (Nat.mul_pos (Nat.two_pow_pos _) s.suff_pos)
  have total : rank G B p h g l b = n := coordinates G B n
  let lo := ElementarySchedule.low src dst s t
  let hi := ElementarySchedule.high src dst s t
  have apart : lo < hi := ElementarySchedule.low_lt_high ne s t
  by_cases order : src.val < dst.val
  · have cmp : A-1-dst.val ≤ A-1-src.val := by omega
    have low : lo = ElementarySchedule.offset dst s t := by simp [lo,ElementarySchedule.low,ElementarySchedule.offset,min_eq_right cmp]
    have high : hi = ElementarySchedule.offset src s t := by simp [hi,ElementarySchedule.high,ElementarySchedule.offset,max_eq_left cmp]
    rw [← high,← low]
    have eq := low_target (p:=p) apart s.suff_pos hh hg hl hb
    change rank G B p h g (if h=1 then 1-l else l) b = toggle hi lo s.suff (rank G B p h g l b) at eq
    rw [total] at eq
    change rank G B p (rewire src dst (⟨h,hh⟩,⟨l,hl⟩)).1 g (rewire src dst (⟨h,hh⟩,⟨l,hl⟩)).2 b = _
    by_cases bit : h=1 <;> simpa [rewire,order,bit,flip] using eq
  · have cmp : A-1-src.val ≤ A-1-dst.val := by omega
    have low : lo = ElementarySchedule.offset src s t := by simp [lo,ElementarySchedule.low,ElementarySchedule.offset,min_eq_left cmp]
    have high : hi = ElementarySchedule.offset dst s t := by simp [hi,ElementarySchedule.high,ElementarySchedule.offset,max_eq_right cmp]
    rw [← low,← high]
    have eq := high_target (p:=p) apart s.suff_pos hh hg hl hb
    change rank G B p (if l=1 then 1-h else h) g l b = toggle lo hi s.suff (rank G B p h g l b) at eq
    rw [total] at eq
    change rank G B p (rewire src dst (⟨h,hh⟩,⟨l,hl⟩)).1 g (rewire src dst (⟨h,hh⟩,⟨l,hl⟩)).2 b = _
    by_cases bit : l=1 <;> simpa [rewire,order,bit,flip] using eq

end PhysicalWalshNode.ElementaryIndex

end NearSquareRoot
end Computability
end OAI
