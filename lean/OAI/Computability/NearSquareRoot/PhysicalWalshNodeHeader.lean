import OAI.Computability.NearSquareRoot.PhysicalWalshMint
import OAI.Computability.NearSquareRoot.PhysicalWalshNode

/-! # Effective geometry of a recursive Walsh piece

A compact descriptor stores the level, active bit count, and word width in
unary, and both spectator lengths in binary. From this descriptor one fixed
tape program computes the new descriptor for a given child slot. Unary layout
rulers used by a bank pass can be expanded separately at their encoded size.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.Header

open IntegerMultiplication Code Staff Strip Carry PhysicalWalsh

/-- Leading zeroes are fixed by the ceiling binary logarithm of `n+1`. -/
def binary (n : ℕ) : Bits.Word := Bits.phrase (Nat.clog 2 (n+1)) n

private theorem below_power (n : ℕ) : n < 2^(Nat.clog 2 (n+1)) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide) _)

@[simp] theorem binary_value (n : ℕ) : Bits.value (binary n) = n := Bits.value_phrase (below_power _)

abbrev Wire := (Tally × Tally × Tally) × Bits.Word × Bits.Word

def wire (A : ℕ) (s : Shape) : Wire :=
  ((tally s.level, tally (grow A s.level), tally (s.w+1)), binary s.pref, binary s.suff)

/-- Exactly the serialized compact input size. -/
def scale (A : ℕ) (s : Shape) := size (wire A s)

theorem scale_exact (A : ℕ) (s : Shape) :
    scale A s = 2*(s.level + grow A s.level + (s.w+1) + Nat.clog 2 (s.pref+1) + Nat.clog 2 (s.suff+1))+9 := by
  simp only [scale, wire, size_prod, size_tally, binary, Bits.size_word,tally_length, Bits.phrase_length]; ring

def regime (A : ℕ) : Regime Shape := ⟨scale A, send ∘ wire A, Dom.base _⟩

variable (A W : ℕ)

private theorem descriptor : (regime A).Has (wire A) := (regime A).self

private theorem level : Realizes (regime A) Shape.level :=
  (descriptor A).ez (Easy.fst.compose Easy.fst)

private theorem active : Realizes (regime A) (fun s => grow A s.level) :=
  (descriptor A).ez (Easy.fst.compose (Easy.snd.compose Easy.fst))

private theorem recordWidth : Realizes (regime A) (fun s => s.w+1) :=
  (descriptor A).ez (Easy.fst.compose (Easy.snd.compose Easy.snd))

private theorem pref : Figure (regime A) Shape.pref :=
  ⟨_,(descriptor A).ez (Easy.snd.compose Easy.fst),fun s => binary_value s.pref⟩

theorem suff : Figure (regime A) Shape.suff :=
  ⟨_,(descriptor A).ez (Easy.snd.compose Easy.snd),fun s => binary_value s.suff⟩

theorem groupCount : Figure (regime A) (groups W) :=
  (Figure.natural 1).maximum ((pref A).quotients (Figure.natural W))

private theorem powerSpan : Figure (regime A) (fun s => 2^(grow A s.level)) :=
  (Figure.natural 2).repeated (active A)

private theorem innerCount : Figure (regime A) (inner A) := (powerSpan A).multiplied (suff A)

private theorem predLevel : Realizes (regime A) (fun s => s.level-1) := (level A).minused (Realizes.fix 1)

theorem childBits (hA : 1 ≤ A) : Realizes (regime A) (fun s => grow A (s.level-1)) := by
  have formula : Figure (regime A) (fun s => grow A (s.level-1)) :=
    (Figure.natural 2).multiplied ((Figure.natural A).repeated (predLevel A))
  have d : Dom (regime A).scale (fun s => size (tally (grow A s.level))) :=
    Regime.Small.extent (active A)
  apply formula.pay (d.mono ?_)
  intro s
  have hle := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hA (Nat.sub_le s.level 1))
  simp only [size_tally, tally_length]; unfold grow; omega

private theorem shifted (n : ℕ) (hA : 1 ≤ A) : Figure (regime A) (fun s => 2^(n*grow A (s.level-1))) :=
  (Figure.natural 2).repeated ((Realizes.fix n).times (childBits A hA))

/-- Serialize a polynomial-bit natural in its canonical, unpadded binary field. -/
theorem toBinary {I : Type} {r : Regime I} {f : I → ℕ} (hf : Figure r f) :
    r.Has (binary ∘ f) := hf.phrase_ (hf.added (Figure.natural 1)).short_log (fun i => below_power (f i))

/-- Compute the compact descriptor to pass to the recursive call. Its binary
spectator lengths include the inactive slots on either side of that child. -/
theorem descend_has (axis : Fin A) : (regime A).Has (wire A ∘ descend A W axis) := by
  have hA : 1 ≤ A := by have := axis.isLt; omega
  have P := (groupCount A W).multiplied (shifted A axis.val hA)
  have B := (shifted A (A-1-axis.val) hA).multiplied (suff A)
  exact ((Regime.Has.pair (predLevel A) (Regime.Has.pair (childBits A hA) (recordWidth A)))).pair
    ((toBinary P).pair (toBinary B))

/-- A tag for the fixed interpreter tells whether to use the base transform. -/
theorem positiveLevel : (regime A).Has (fun s => decide (0 < s.level)) := by
  have h := (level A).ez (Carry.vacant Unit)
  have neg := h.ez (show Easy (! · : Bool → Bool) from Easy.finite _)
  convert neg using 1
  funext s
  cases e : s.level with
  | zero => simp [e, Staff.box, tally]
  | succ n => simp [e, Staff.box, tally_succ]

/-- Emit the tag and descriptor in the shape consumed by `RecSpec.query`. -/
theorem descend_tagged (axis : Fin A) : (regime A).Has (fun s =>
    (decide (0 < (descend A W axis s).level), wire A (descend A W axis s))) := by
  have desc := descend_has A W axis
  have pol : Poly (fun w : Wire => ((!w.1.1.isEmpty),w)) := by
    exact ((Easy.fst.compose Easy.fst).compose (Carry.vacant Unit) |>.compose
      (show Easy (! · : Bool → Bool) from Easy.finite _)).pair Easy.identity |>.poly
  have h := desc.thenDo pol
  convert h using 1
  funext s
  congr 1
  cases e : (descend A W axis s).level with
  | zero => simp [wire,e,tally]
  | succ n => simp [wire,e,tally_succ]

/-- Spectator and word-size rulers for the four-point base transform. -/
def baseHeader (s : Shape) := ((tally s.pref, tally s.suff), tally (s.w+1))

theorem base_mint : Mint (regime A) baseHeader :=
  ((Mint.tally (pref A)).pair (Mint.tally (suff A))).pair (Mint.of_has (recordWidth A))

/-- Read the recursion flag from the compact descriptor without destroying it. -/
theorem tagged_has : (regime A).Has (fun s => (decide (0 < s.level),wire A s)) :=
  (positiveLevel A).pair (descriptor A)

/-- Rulers consumed by `PhysicalWalsh.ChildLanes.splitTask` and `.mergeTask`. -/
def cuts (s : Shape) := (tally (groups W s), tally (inner A s))

theorem cuts_mint : Mint (regime A) (cuts A W) :=
  (Mint.tally (groupCount A W)).pair (Mint.tally (innerCount A))

/-- The exact physical grid header used by mixing and scaling on the work lanes. -/
theorem grid_mint (a : ℕ) : Mint (regime (a+1))
    (PhysicalWalshGrid.header (coords a W) Shape.w) := by
  let A := a+1
  have span : Realizes (regime A) (fun s => A * grow A (s.level-1)) :=
    (Realizes.fix A).times (childBits A (by dsimp [A]; omega))
  have width : Figure (regime A) (fun s => 2^(A*grow A (s.level-1))) := (Figure.natural 2).repeated span
  have N := (groupCount A W).multiplied (width.multiplied (suff A))
  have mk := ((Mint.tally N).pair (Mint.of_has (recordWidth A))).pair
    (((Mint.tally (groupCount A W)).pair (Mint.tally (suff A))).pair (Mint.of_has span))
  convert mk using 1
  funext s
  simp only [PhysicalWalshGrid.header, KernelScaleBank.count_eq, Function.comp_apply]
  rfl

private theorem inner_pos (A : ℕ) (s : Shape) : 0 < inner A s :=
  Nat.mul_pos (by positivity : 0 < 2^grow A s.level) s.suff_pos

private theorem groups_le (W : ℕ) (s : Shape) : groups W s ≤ s.pref :=
  max_le s.pref_pos (Nat.div_le_self _ _)

private theorem left_le_count (A : ℕ) (s : Shape) : s.pref ≤ count A s :=
  Nat.le_mul_of_pos_right _ (inner_pos A s)

private theorem inner_le_count (A : ℕ) (s : Shape) : inner A s ≤ count A s :=
  Nat.le_mul_of_pos_left _ s.pref_pos

/-- At any occupied recursive node, a global record-capacity bound gives a
linear bound on the compact descriptor scale, independent of the level. -/
theorem scale_le_of_count {A k : ℕ} (hA : 2 ≤ A) (s : Shape) (hN : count A s ≤ 2^k) :
    scale A s ≤ 12*(k+s.w+1)+9 := by
  have hp := (left_le_count A s).trans hN
  have raw : 2^grow A s.level ≤ count A s := (Nat.le_mul_of_pos_right _ s.suff_pos).trans (inner_le_count A s)
  have hb : s.suff ≤ 2^k := ((Nat.le_mul_of_pos_left _ (by positivity : 0 < 2^grow A s.level)).trans
    (inner_le_count A s)).trans hN
  have hbits := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (raw.trans hN)
  have hlevel : s.level ≤ grow A s.level := s.level.lt_two_pow_self.le.trans
    ((Nat.pow_le_pow_left hA _).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)))
  have bigger : 2^k+1 ≤ 2^(k+1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega
  have clp := Nat.clog_le_of_le_pow ((Nat.add_le_add_right hp 1).trans bigger)
  have clb := Nat.clog_le_of_le_pow ((Nat.add_le_add_right hb 1).trans bigger)
  rw [scale_exact]; omega

theorem cuts_size (s : Shape) : size (cuts A W s) ≤ 4*count A s + 3 := by
  have hg := (groups_le W s).trans (left_le_count A s)
  have hi := inner_le_count A s
  simp only [cuts,size_prod,size_tally,tally_length]; omega

/-- The active size of the physical grid at a nonbase node is exactly the
number of address bits written in its compact descriptor. -/
theorem grid_width (a : ℕ) (s : Shape) (hs : 0 < s.level) :
    KernelScaleBank.width (coords a W) s = grow (a+1) s.level := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  change (a+1)*(2*(a+1)^(s.level-1)) = 2*(a+1)^s.level
  rw [hj,Nat.succ_sub_one, pow_succ]; ring

theorem grid_size (a : ℕ) (s : Shape) (hs : 0 < s.level) :
    size (PhysicalWalshGrid.header (coords a W) Shape.w s) ≤ 10*(count (a+1) s+s.w+1) + 8 := by
  have hg := (groups_le W s).trans (left_le_count (a+1) s)
  have suff : s.suff ≤ count (a+1) s :=
    (Nat.le_mul_of_pos_left _ (by positivity : 0 < 2^grow (a+1) s.level)).trans (inner_le_count (a+1) s)
  have width := grid_width W a s hs
  have bits : grow (a+1) s.level ≤ count (a+1) s := (Nat.lt_two_pow_self.le.trans
    (Nat.le_mul_of_pos_right _ s.suff_pos)).trans (inner_le_count (a+1) s)
  have lanes := Nat.mul_le_mul_right (inner (a+1) s) (groups_le W s)
  change groups W s * (2^grow (a+1) s.level*s.suff) ≤ count (a+1) s at lanes
  simp only [PhysicalWalshGrid.header,KernelScaleBank.header,KernelScaleBank.count_eq,
    size_prod,size_tally,tally_length,width]
  change 2 * (groups W s * (2 ^ grow (a+1) s.level * s.suff)) + 1 + (2*(s.w+1)+1) + 1 +
    (2*groups W s+1+(2*s.suff+1)+1+(2*grow (a+1) s.level+1)+1)+1 ≤ _
  omega

/-- The lane boundary rulers are generated in time and space linear in the
node's record count plus a polynomial in its compact descriptor. -/
theorem cuts_bounded : ∃ d C : ℕ,
    let b s := C*(scale A s+1)^d + (count A s+1)
    Space.BoundedTask b b (send ∘ wire A) (send ∘ cuts A W) := by
  obtain ⟨d,C,h⟩ := (cuts_mint A W).bounded
  refine ⟨d,C,?_⟩
  apply h.bound 5 5 <;> intro s <;> have := cuts_size A W s <;> change
    C*(scale A s+1)^d + size (cuts A W s) + 1 ≤ 5*(C*(scale A s+1)^d+(count A s+1)+1) <;> omega

/-- Supply the two strided-base grouping rulers and the fixed-width ruler. -/
theorem base_bounded : ∃ d C : ℕ,
    let b s := C*(scale A s+1)^d + (count A s+s.w+1)
    Space.BoundedTask b b (send ∘ wire A) (send ∘ baseHeader) := by
  obtain ⟨d,C,h⟩ := (base_mint A).bounded
  have sizeBound (s : Shape) : size (baseHeader s) ≤ 6*(count A s + s.w+1)+5 := by
    have hp := left_le_count A s
    have hs : s.suff ≤ count A s :=
      (Nat.le_mul_of_pos_left _ (by positivity : 0 < 2^grow A s.level)).trans (inner_le_count A s)
    simp only [baseHeader,size_prod,size_tally,tally_length]; omega
  refine ⟨d,C,?_⟩
  apply h.bound 10 10 <;> intro s <;> have := sizeBound s <;> change
    C*(scale A s+1)^d + size (baseHeader s) + 1 ≤ 10*(C*(scale A s+1)^d+(count A s+s.w+1)+1) <;> omega

/-- Construct all five work-bank rulers before the first primitive is entered. -/
theorem grid_bounded (a : ℕ) : ∃ d C : ℕ,
    let b (s : {s : Shape // 0 < s.level}) := C*(scale (a+1) s.val+1)^d + (count (a+1) s.val+s.val.w+1)
    Space.BoundedTask b b (fun s => send (wire (a+1) s.val))
      (fun s => send (PhysicalWalshGrid.header (coords a W) Shape.w s.val)) := by
  obtain ⟨d,C,h⟩ := (grid_mint W a).bounded
  refine ⟨d,C,?_⟩
  apply (h.on (Subtype.val (p := fun s : Shape => 0 < s.level))).bound 20 20 <;>
    intro s <;> have := grid_size W a s.val s.property <;> change
      C*(scale (a+1) s.val+1)^d + size (PhysicalWalshGrid.header (coords a W) Shape.w s.val)+1 ≤
        20*(C*(scale (a+1) s.val+1)^d+(count (a+1) s.val+s.val.w+1)+1) <;> omega

/-- Polytime descriptor-only transition, including the recursive branch tag. -/
theorem descend_bounded (axis : Fin A) : ∃ d C : ℕ,
    let b s := C*(scale A s+1)^d
    Space.BoundedTask b b (send ∘ wire A) (fun s => send
      (decide (0 < (descend A W axis s).level), wire A (descend A W axis s))) := by
  obtain ⟨t,dt,h⟩ := descend_tagged A W axis
  obtain ⟨d,C,bound⟩ := (regime A).gauge.add dt
  refine ⟨d,C,?_⟩
  apply (Space.BoundedTask.of_time h).mono <;> intro s <;> have b := bound s <;> dsimp [regime] at b ⊢ <;> omega

end PhysicalWalshNode.Header

end NearSquareRoot
end Computability
end OAI
