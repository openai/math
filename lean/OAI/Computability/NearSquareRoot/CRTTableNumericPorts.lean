import OAI.Computability.NearSquareRoot.CRTTableBoxRun
import OAI.Computability.NearSquareRoot.CRTTablePrefix
import OAI.Computability.NearSquareRoot.SynchronizedPhysicalBits
import OAI.Computability.NearSquareRoot.SynchronizedBitAddress

/-! # Reading a CRT axis word from its global record number

The arithmetic record index places the first axis at the low end. The
prefix reader numbers bits from the high end, including inside each axis.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication

/-- Local word ports count down from the highest bit of the radix digit. -/
theorem wordEquiv_testBit {d : ℕ} (x : Fin (2^d)) (i : Fin d) :
    wordEquiv d x i = x.val.testBit (d-1-i.val) := by
  have h := BoxFin.value_bit (Bits.phrase d x.val) (d-1-i.val)
    (by have := i.isLt; simp only [Bits.phrase_length]; omega)
  rw [Bits.value_phrase x.isLt] at h
  change (Bits.phrase d x.val).reverse[i.val]'(by simp [Bits.phrase_length]) = _
  rw [List.getElem_reverse, h]
  simp [Bits.phrase_length]

private theorem before_field {α : Type*} [DecidableEq α] (w : α → ℕ) (b : α)
    (pre post : List α) (h : b ∉ pre) :
    fieldOffset w (pre ++ b::post) b = (pre.map w).sum := by
  induction pre with
  | nil => simp [fieldOffset]
  | cons x xs ih =>
    have hx : x ≠ b := fun e => h (by simp [e])
    have hs : b ∉ xs := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [fieldOffset, hx, ih hs]

variable {box : List (ℕ × ℕ)} {k l : ℕ} (hb : BoxShape.Valid k l box)

include hb in
/-- Complementing the MSF prefix position gives the LSF bit position of
the same port in the global record number. -/
theorem fieldPosition_lsb (b : Fin box.length) (i : Fin (axisWidth box b)) :
    k-1-fieldPosition (axisWidth box) (List.finRange box.length) b i =
      BoxFin.offset b + (axisWidth box b-1-i.val) := by
  let xs := List.finRange box.length
  let w := axisWidth box
  let pre := xs.take b.val
  let post := xs.drop (b.val+1)
  have hbnd : b.val < xs.length := by simp [xs]
  have hget : xs[b.val] = b := by simp [xs, List.getElem_finRange]
  have split : pre ++ b::post = xs := by
    change xs.take b.val ++ b::xs.drop (b.val+1) = xs
    simpa only [List.drop_eq_getElem_cons hbnd, hget] using List.take_append_drop b.val xs
  have hn : (pre ++ b::post).Nodup := by rw [split]; exact List.nodup_finRange _
  have hnd := (List.nodup_append.mp hn).2.1
  have hpost : b ∉ post.reverse := by simpa using (List.nodup_cons.mp hnd).1
  have hoff : fieldOffset w xs.reverse b = (post.map w).sum := by
    calc
      _ = fieldOffset w (post.reverse ++ b :: pre.reverse) b := by
        conv_lhs => rw [← split]
        simp
      _ = _ := by simpa [List.map_reverse] using before_field w b post.reverse pre.reverse hpost
  have hpre : (pre.map w).sum = BoxFin.offset b := by
    change ((xs.take b.val).map w).sum = _
    rw [List.map_take, show xs.map w = List.ofFn w from List.ofFn_eq_map.symm,
      ← Fin.ofFn_take_eq_take_ofFn b.isLt.le, List.sum_ofFn]
    rfl
  have hsum : (xs.map w).sum = k := by
    rw [show xs.map w = List.ofFn w from List.ofFn_eq_map.symm, List.sum_ofFn]
    exact (Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum
  rw [← split, List.map_append, List.sum_append, List.map_cons, List.sum_cons, hpre] at hsum
  change k-1-(fieldOffset w xs.reverse b + i.val) = BoxFin.offset b + (w b-1-i.val)
  rw [hoff]
  have hi : i.val < w b := i.isLt
  omega

include hb in
private theorem portFits (b : Fin box.length) : BoxFin.modulus box b ≤ 2 ^ axisWidth box b :=
  (hb.axisBounds _ (List.get_mem box b)).2.2.2

variable [∀ g, NeZero (BoxFin.modulus box g)]

private theorem finEquiv_val {n : ℕ} [NeZero n] (x : Fin n) :
    (ZMod.finEquiv n x).val = x.val := by
  cases n <;> first | exact Fin.elim0 x | rfl

/-- The residue-first rank used by a CRT word equals the field rank of
the padded tape serializer, also on padding addresses. -/
theorem axisNumber_boxField (b : Fin box.length)
    (z : AxisValue (BoxFin.modulus box) (axisWidth box) b) :
    axisNumber (portFits hb b) z = BoxFin.field hb b z := by
  apply Fin.ext
  cases z with
  | inl r =>
    change r.val = ((ZMod.finEquiv _).symm r).val
    simpa using finEquiv_val ((ZMod.finEquiv _).symm r)
  | inr q => rfl

/-- Every bit read from an individual CRT field equals the corresponding
bit of the original flat record address. -/
theorem boxRecord_port (t : Fin (2^k)) (b : Fin box.length) (i : Fin (axisWidth box b)) :
    wordEquiv (axisWidth box b) (axisNumber (portFits hb b)
      ((BoxFin.recordIndex hb).symm t b)) i =
      t.val.testBit (k-1-fieldPosition (axisWidth box) (List.finRange box.length) b i) := by
  rw [wordEquiv_testBit, fieldPosition_lsb hb]
  refine (congrArg (fun z : Fin (2 ^ axisWidth box b) => z.val.testBit (axisWidth box b-1-i.val))
    (axisNumber_boxField hb b ((BoxFin.recordIndex hb).symm t b))).trans ?_
  have hi : i.val < (box.get b).1 := i.isLt
  have hq : axisWidth box b-1-i.val < (box.get b).1 := by unfold axisWidth; omega
  simpa only [Equiv.apply_symm_apply] using
    BoxFin.testBit_field hb ((BoxFin.recordIndex hb).symm t) b hq

end CRTTable

end NearSquareRoot
end Computability
end OAI
