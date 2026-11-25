import OAI.ThreeFlat.Diagonal.TraceUniformAddress
import OAI.ThreeFlat.RAM.ContractionMemory

namespace OAI
/-! # Constant-size descriptions of physical trace addresses

Every local port has one record shared by all row numbers. The record tests
an interval, computes an affine address after an optional XOR displacement,
and can extract one bit for a row-dependent constant.
-/

namespace ThreeFlat.Diagonal.TraceAddressRecord

open Computability.VPVNP RAM.BitLayout TracePhysical TraceUniformRow

structure Record where
  testStride : ℕ := 0
  testBias : ℕ := 0
  lo : ℕ := 0
  hi : ℕ := 1
  base : ℕ := 0
  stride : ℕ := 0
  mask : ℕ := 0
  sub : ℕ := 0
  bit : Option ℕ := none
  fallback : ℕ := 0

def Record.test (R : Record) (v : ℕ) := R.testStride*v + R.testBias
def Record.numerator (R : Record) (v : ℕ) := R.base + R.stride*(v ^^^ R.mask)
def Record.result (R : Record) (v : ℕ) := R.numerator v - R.sub
def Record.eval (R : Record) (v : ℕ) : ℕ :=
  if R.lo ≤ R.test v ∧ R.test v < R.hi then
    match R.bit with
    | none => R.result v
    | some j => ((R.result v).testBit j).toNat
  else R.fallback

/-- Every argument whose unsigned value the native evaluator inspects. -/
structure Record.Fits (R : Record) (W v : ℕ) : Prop where
  row : v < 2^W
  mask : R.mask < 2^W
  test : R.test v < 2^W
  lo : R.lo < 2^W
  hi : R.hi < 2^W
  numerator : R.numerator v < 2^W
  sub : R.sub < 2^W
  bit : R.bit.getD 0 < 2^W

variable {w r k p d : ℕ}

/-- Each constructor of an ordinary local port supplies the constants of a
single record. Layer masks, fixed-field bits, and local pin ordinals belong
to the polynomial-size public local table. -/
def ordinary (hw : 2 ≤ w+1) (S f : ℕ) : TracePhysical.Port w r d → Record
  | .inl (c,j) =>
    let width := (5+r)*(w+1)
    { testStride := 2, testBias := c.val, lo := S, hi := S+f,
      base := hiddenBase (S*w) + j.val + width*c.val,
      stride := 2*width, sub := width*S }
  | .inr (.inl (s,j)) =>
    { testStride := 2, testBias := s.val, hi := S, base := 2+j.val+w*s.val, stride := 2*w }
  | .inr (.inr (.inl (l,own,s,j))) =>
    let width := 7*(w+1)
    { base := hiddenBase (S*w) + f*((5+r)*(w+1)) + j.val + width*s.val
        + (2^d*(2*width))*l.val,
      stride := 2*width, mask := if own then 0 else 2^((RAMLayout.layerEquiv d).symm l).siteBit }
  | .inr (.inr (.inr (out,j))) =>
    let width := 7*(w+1)
    let base := hiddenBase (S*w) + f*((5+r)*(w+1))
      + RAMLayout.layerCount d * (2^d*(2*width)) + j.val
    let fallback := ((TraceSlots.slotFormat hw).encode none j).toNat
    if out then
      {testStride := 1, hi := 2^d-1, base, stride := width, fallback}
    else
      {testStride := 1, lo := 1, hi := 2^d, base, stride := width, sub := width, fallback}

private theorem subtract_product {a b h v s : ℕ} (inRange : s ≤ 2*v+h) :
    a+b*h+2*b*v-b*s = a+b*(2*v+h-s) := by
  rw [Nat.mul_sub, show a+b*h+2*b*v = a+b*(2*v+h) by ring,
    Nat.add_sub_assoc (Nat.mul_le_mul_left b inRange)]

theorem ordinary_eval (hw : 2 ≤ w+1) (S f : ℕ) (v : Fin (2^d)) (port : TracePhysical.Port w r d) :
    (ordinary hw S f port).eval v.val = sourceAddress (TracePhysical.address hw S f v port) := by
  rcases port with ⟨c,j⟩ | (⟨s,j⟩ | (⟨l,own,s,j⟩ | ⟨out,j⟩))
  · by_cases lo : S ≤ 2*v.val+c.val
    · by_cases hi : 2*v.val+c.val-S < f
      · have yes : 2*v.val+c.val < S+f := by omega
        simp only [ordinary, Record.eval, Record.test, Record.result, Record.numerator,
          Nat.xor_zero, lo, yes, and_self, TracePhysical.address, hi, ↓reduceDIte, ↓reduceIte,
          shared, sourceAddress, cpuOrdinal]
        rw [subtract_product lo]
        omega
      · have no : ¬ 2*v.val+c.val < S+f := by omega
        simp [ordinary, Record.eval, Record.test, TracePhysical.address, lo, hi, no, sourceAddress]
    · simp [ordinary, Record.eval, Record.test, TracePhysical.address, lo, sourceAddress]
  · by_cases h : 2*v.val+s.val < S
    · simp [ordinary, Record.eval, Record.test, Record.result, Record.numerator, h,
        TracePhysical.address, sourceAddress, finProdFinEquiv]
      ring
    · simp [ordinary, Record.eval, Record.test, h, TracePhysical.address, sourceAddress]
  · cases own <;>
      simp [ordinary, Record.eval, Record.test, Record.result, Record.numerator,
        TracePhysical.address, shared, sourceAddress, sortOrdinal, RAMLayout.Layer.partner, RAMSort.partner] <;> ring
  · cases out with
    | false =>
      by_cases h : 0 < v.val
      · obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
        have inrange := v.isLt
        simp [ordinary, Record.eval, Record.test, Record.result, Record.numerator, h, inrange,
          TracePhysical.address, sourceAddress, shared, boundaryOrdinal]
        rw [hn]
        simp only [show 1 ≤ n.succ by omega, ite_true, Nat.succ_sub_one, Nat.mul_succ (7*(w+1)) n]
        omega
      · have hv : v.val = 0 := by omega
        simp [ordinary, Record.eval, Record.test, TracePhysical.address, hv, sourceAddress]
    | true =>
      by_cases h : v.val+1 < 2^d
      · have hr : v.val < 2^d-1 := by omega
        simp [ordinary, Record.eval, Record.test, Record.result, Record.numerator, h, hr,
          TracePhysical.address, sourceAddress, shared, boundaryOrdinal]; ring
      · have hr : ¬ v.val < 2^d-1 := by omega
        simp [ordinary, Record.eval, Record.test, h, hr, TracePhysical.address, sourceAddress]

def portRecord (hw : 2 ≤ w+1) (S f : ℕ) : TraceUniformRow.Port w p r k d → Record
  | .inl z => ordinary hw S f z
  | .inr (future,j) =>
    let width := (1+6*p+k)*w
    let base := hiddenBase (S*w) + Fintype.card (Shared w r f d) + (finProdFinEquiv j).val
    if future then { testStride := 1, hi := 2^d-1, base := base+width, stride := width }
    else { base, stride := width }

theorem portRecord_eval (hw : 2 ≤ w+1) (S f : ℕ) (v : Fin (2^d)) (z : TraceUniformRow.Port w p r k d) :
    (portRecord hw S f z).eval v.val = sourceAddress (addresses hw S f v z) := by
  rcases z with z | ⟨b,j⟩
  · rw [portRecord, ordinary_eval, addresses]
    cases TracePhysical.address hw S f v z <;> rfl
  · cases b with
    | false =>
      simp [portRecord, Record.eval, Record.test, Record.result, Record.numerator, addresses,
        sourceAddress, copyOrdinal, finProdFinEquiv]; ring
    | true =>
      by_cases h : v.val+1 < 2^d
      · have hr : v.val < 2^d-1 := by omega
        simp [portRecord, Record.eval, Record.test, Record.result, Record.numerator, h, hr,
          addresses, sourceAddress, copyOrdinal, finProdFinEquiv]; ring
      · have hr : ¬v.val < 2^d-1 := by omega
        simp [portRecord, Record.eval, Record.test, h, hr, addresses, sourceAddress]

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
