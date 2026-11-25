import OAI.Hierarchy.TaggedPassState
import OAI.Hierarchy.TaggedWideOrder

namespace OAI
/-! # Homogeneous packed inputs and record preservation for the wide sort -/

namespace Hierarchy.Tagged.Radix.PassShape
open ThreeFlat Routing SortNetwork RadixStage SortedBlock WideOrder
open scoped Classical
noncomputable section

variable (s : PassShape) {w : ℕ} (dummy : Bits w) (real isDummy : Fin w) (digit : Fin s.digitBits → Fin w)

def packedInput (x : RowBits s.rows w → Bool) : Records s.globalHeight (s.pack*w) :=
  unwrap (staticRead (s.wideInput dummy) (s.localOut dummy real isDummy digit x))

theorem fits_local (room : s.packBits+2 ≤ s.digitBits) : s.perBlock ≤ 2^s.localBits := by
  have same : s.localBits = 2*s.digitBits+1 := by unfold localBits upperBits; omega
  exact same.symm ▸ s.local_height room

private theorem pack_divides_block (room : s.packBits ≤ 2*s.digitBits) : s.pack ∣ s.perBlock :=
  dvd_add (show s.pack ∣ s.block from pow_dvd_pow _ room) (dvd_mul_left ..)

private theorem rectangular_slot {p b : ℕ} (hp : 0 < p) (hb : 0 < b) (q : ℕ) (l : Fin p) :
    (q*p+l.val)/(b*p) = q/b ∧ (q*p+l.val)%(b*p) = (q%b)*p+l.val := by
  have pos : 0 < b*p := Nat.mul_pos hb hp
  have small : q%b*p+l.val < b*p := calc
    _ < q%b*p+p := Nat.add_lt_add_left l.isLt _
    _ = (q%b+1)*p := by rw [Nat.add_mul]; simp
    _ ≤ b*p := Nat.mul_le_mul_right _ (Nat.mod_lt _ hb)
  have form : q*p+l.val = (q%b*p+l.val)+(q/b)*(b*p) := calc
    _ = (q%b+b*(q/b))*p+l.val := by rw [Nat.mod_add_div]
    _ = _ := by ring
  rw [form,Nat.add_mul_div_right _ _ pos,Nat.add_mul_mod_self_right,Nat.div_eq_of_lt small,Nat.mod_eq_of_lt small,Nat.zero_add]
  exact ⟨rfl,rfl⟩

private theorem index_val (fits : s.perBlock ≤ 2^s.localBits) (i : Fin s.nextRows) :
    (s.retainedIndex i fits).1.val = i.val/s.perBlock ∧ (s.retainedIndex i fits).2.val = i.val%s.perBlock := ⟨rfl,rfl⟩

/-- Alignment of the local real rows is respected by the row-major packing
map even at block boundaries. -/
theorem pack_homogeneous (room : s.packBits+2 ≤ s.digitBits) (blank : dummy real = false) (flags : dummy isDummy = !(dummy real))
    (x : RowBits s.rows w → Bool) (valid : shapeFlags s.rows real isDummy x) :
    Homogeneous (show 0 < s.pack from Nat.two_pow_pos s.packBits) digit real (s.packedInput dummy real isDummy digit x) := by
  let fit := s.fits_local room
  let blockOutput : s.LocalData w → Bool := s.localOut dummy real isDummy digit x
  let mid (b : Fin s.blocks) := s.blockWord (s.localSortRun isDummy digit (staticRead (s.enter dummy) x)) b
  let X := s.packedInput dummy real isDummy digit x
  have readLocal (b i) : s.blockWord blockOutput b i = align (j := s.packBits) (t := s.upperBits) digit real (mid b) i := by
    exact congrFun (unwrap_pack (align (j := s.packBits) (t := s.upperBits) digit real (mid b))) i
  have word (q : Row s.globalHeight) (l : Fin s.pack) :
      lane (X q) l = if h : q.val*s.pack+l.val < s.nextRows then let k:=s.retainedIndex ⟨_,h⟩ fit; align (j := s.packBits) (t := s.upperBits) digit real (mid k.1) k.2 else dummy := by
    have laneEq : lane (X q) l = s.wideLane (staticRead (s.wideInput dummy) blockOutput) q l := rfl
    exact laneEq.trans (by simpa only [readLocal] using s.wide_word dummy blockOutput fit q l)
  intro q laneN alive
  let z : Fin s.pack := ⟨0,Nat.two_pow_pos _⟩
  change lane (X q) laneN real = true at alive
  change lane (X q) z real = true ∧ readKey digit (lane (X q) laneN) = readKey digit (lane (X q) z)
  by_cases h : q.val*s.pack+laneN.val < s.nextRows
  · have h0 : q.val*s.pack+z.val < s.nextRows := (Nat.add_le_add_left (show z.val ≤ laneN.val from Nat.zero_le _) _).trans_lt h
    let i := s.retainedIndex ⟨_,h⟩ fit
    let f := s.retainedIndex ⟨_,h0⟩ fit
    have w := word q laneN
    have w0 := word q z
    rw [dite_eq_left h] at w
    rw [dite_eq_left h0] at w0
    change lane (X q) laneN = align (j := s.packBits) (t := s.upperBits) digit real (mid i.1) i.2 at w
    change lane (X q) z = align (j := s.packBits) (t := s.upperBits) digit real (mid f.1) f.2 at w0
    rw [w] at alive
    obtain ⟨blocks,eq⟩ := s.pack_divides_block (by omega)
    have cap : s.perBlock = blocks*s.pack := eq.trans (Nat.mul_comm ..)
    have blocksPos : 0 < blocks := by by_contra! h; have := s.block; have pp : 0 < s.perBlock := (Nat.two_pow_pos (2*s.digitBits)).trans_le (Nat.le_add_right ..); simp [Nat.eq_zero_of_le_zero h] at cap; omega
    have xy := rectangular_slot (p := s.pack) (Nat.two_pow_pos _) blocksPos q.val laneN
    have zy := rectangular_slot (p := s.pack) (Nat.two_pow_pos _) blocksPos q.val z
    have ii := s.index_val fit ⟨_,h⟩
    have ff := s.index_val fit ⟨_,h0⟩
    simp only [cap] at ii ff
    have blockEq : f.1 = i.1 := Fin.ext ((ff.1.trans zy.1).trans (ii.1.trans xy.1).symm)
    have atFirst : f.2.val = i.2.val/s.pack*s.pack := by
      have pos : 0 < s.pack := Nat.two_pow_pos _
      have first : f.2.val = q.val%blocks*s.pack+0 := ff.2.trans zy.2
      have here : i.2.val = q.val%blocks*s.pack+laneN.val := ii.2.trans xy.2
      rw [first,here,Nat.add_zero,Nat.add_comm (q.val%blocks*s.pack),Nat.add_mul_div_right _ _ pos,Nat.div_eq_of_lt laneN.isLt,Nat.zero_add]
    obtain ⟨v,vFirst,vReal,vKey⟩ := align_first digit real (mid i.1)
      (s.aligned_input dummy real isDummy digit room blank flags x valid i.1) i.2 alive
    have vEq : f.2 = v := Fin.ext (atFirst.trans vFirst.symm)
    have firstWord : lane (X q) z = align (j := s.packBits) (t := s.upperBits) digit real (mid i.1) v :=
      w0.trans (by rw [blockEq,vEq])
    exact ⟨(congrFun firstWord real).trans vReal,
      (congrArg (readKey digit) w).trans (vKey.symm.trans (congrArg (readKey digit) firstWord).symm)⟩
  · have missing := word q laneN
    rw [dite_eq_right h] at missing
    rw [missing,blank] at alive
    contradiction

private theorem align_keeps {j t d w : ℕ} (digit : Fin d → Fin w) (real : Fin w)
    (v : Records (j+t) w) (P : Bits w → Prop) (holds : ∀ i, P (v i)) (i : Row (j+t)) :
    P (align (j := j) (t := t) digit real v i) := by
  by_cases ok : AlignedInput (j := j) (t := t) digit real v
  · unfold align
    rw [dite_eq_left ok]
    exact holds _
  · unfold align
    rw [dite_eq_right ok]
    exact holds i

/-- Every physical real or blank word copied into the wide input satisfies
any predicate shared by the original records and the chosen padding. -/
theorem packed_words (room : s.packBits+2 ≤ s.digitBits) (P : Bits w → Prop) (fixed : P dummy)
    (x : RowBits s.rows w → Bool) (valid : ∀ i, P (fun j => x (i,j))) :
    ∀ q l, P (lane (s.packedInput dummy real isDummy digit x q) l) := by
  let mapped := staticRead (s.enter dummy) x
  let initial := fun b => s.blockWord mapped b
  let mid := fun b => s.blockWord (s.localSortRun isDummy digit mapped) b
  have orig (b i) : P (initial b i) := by
    dsimp only [initial,mapped]; rw [enter_block_word]; split <;> first | (split <;> first | exact valid _ | exact fixed) | exact fixed
  have sorted (b i) : P (mid b i) := by
    have eq : mid b = stable (maskedDigit digit isDummy) (initial b) :=
      unwrap_pack (stable (maskedDigit digit isDummy) (initial b))
    rw [eq]; exact orig _ _
  have placed (b i) : P (s.blockWord (s.localOut dummy real isDummy digit x) b i) := by
    have eq : s.blockWord (s.localOut dummy real isDummy digit x) b i = align (j := s.packBits) (t := s.upperBits) digit real (mid b) i :=
      congrFun (unwrap_pack (align (j := s.packBits) (t := s.upperBits) digit real (mid b))) i
    rw [eq]
    exact align_keeps (j := s.packBits) (t := s.upperBits) digit real (mid b) P (sorted b) i
  intro q l
  let blockOutput : s.LocalData w → Bool := s.localOut dummy real isDummy digit x
  have word := s.wide_word dummy blockOutput (s.fits_local room) q l
  have laneEq : lane (s.packedInput dummy real isDummy digit x q) l = s.wideLane (staticRead (s.wideInput dummy) blockOutput) q l := rfl
  apply (congrArg P (laneEq.trans word)).mpr
  by_cases inside : q.val*s.pack+l.val < s.nextRows
  · rw [dite_eq_left inside]; exact placed _ _
  · rw [dite_eq_right inside]; exact fixed

/-- Dyadic surplus packs contain just the prescribed blank. -/
theorem wide_input_support (room : s.packBits+2 ≤ s.digitBits) (blank : dummy real = false) (x : RowBits s.rows w → Bool) :
    ∀ q : Row s.globalHeight, s.packs ≤ q.val → ∀ l, lane (s.packedInput dummy real isDummy digit x q) l real = false := by
  intro q hq l
  have count := s.exact_packs (by omega)
  have cap := Nat.mul_le_mul_right s.pack hq
  rw [count] at cap
  let blockOutput : s.LocalData w → Bool := s.localOut dummy real isDummy digit x
  have word := s.wide_word dummy blockOutput (s.fits_local room) q l
  have laneEq : lane (s.packedInput dummy real isDummy digit x q) l = s.wideLane (staticRead (s.wideInput dummy) blockOutput) q l := rfl
  rw [dite_eq_right (show ¬q.val*s.pack+l.val < s.nextRows by omega)] at word
  exact (congrFun (laneEq.trans word) real).trans blank

end
end Hierarchy.Tagged.Radix.PassShape

end OAI
