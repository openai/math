import OAI.Computability.IntegerMultiplication.Code.Filter
import OAI.Computability.IntegerMultiplication.Code.Iter
import OAI.Computability.IntegerMultiplication.Code.Dup

/-! # Linear scans between compact and padded record streams

A single validity bit accompanies each padded address. Extraction keeps the
records with a true bit in their original order. Placement consumes one compact
record per true bit and fills the false positions with a padding record.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxMaskedRecords

open IntegerMultiplication IntegerMultiplication.Code

variable {A : Type}

/-- Records in valid positions, in tape order. -/
def selected (xs : List (Bool × A)) : List A := (xs.filter Prod.fst).map Prod.snd

private theorem read_selected (xs : List (Bool × A)) : Ribbon.read true xs = selected xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨b, x⟩ := x
    cases b <;> simp [Ribbon.read, Ribbon.keep, selected] at ih ⊢ <;> exact ih

/-- Expand the compact input using one segment of size zero or one per padded address. -/
def expand (pad : A) (p : List Bool × List A) : List A :=
  (Ribbon.dress true p).map fun chunk => chunk.headD pad

/-- Extract from aligned streams. The fixed dummy handles an incomplete input pair. -/
def compress (dummy : A) (p : List Bool × List A) : List A :=
  Ribbon.read true (zipFair false dummy p)

theorem expand_tagged (pad : A) (xs : List (Bool × A)) :
    expand pad (xs.map Prod.fst, selected xs) = xs.map (fun p => bif p.1 then p.2 else pad) := by
  rw [← read_selected, expand, Ribbon.frame, List.map_map]
  apply List.map_congr_left
  rintro ⟨b,x⟩ _
  cases b <;> rfl

theorem compress_tagged (dummy : A) (xs : List (Bool × A)) :
    compress dummy (xs.map Prod.fst, xs.map Prod.snd) = selected xs := by
  rw [compress, fair]
  simpa using read_selected xs

@[fun_prop] theorem expand_easy [Codec A] (pad : A) : Easy (expand pad) :=
  (Ribbon.easyDress true).compose (Iter.leader pad).mapping

@[fun_prop] theorem compress_easy [Codec A] (dummy : A) : Easy (compress dummy) :=
  (easy_zip false dummy).compose (Ribbon.easyRead true Easy.identity)

private theorem expand_cons (pad : A) (b : Bool) (mask : List Bool) (rows : List A) :
    expand pad (b::mask,rows) = if b then
      rows.headD pad :: expand pad (mask, rows.tail) else pad :: expand pad (mask,rows) := by
  cases b <;> cases rows <;> rfl

@[simp] theorem length_expand (pad : A) (mask : List Bool) (rows : List A) :
    (expand pad (mask, rows)).length = mask.length := by
  induction mask generalizing rows with
  | nil => rfl
  | cons b mask ih => cases b <;> simp [expand_cons, ih]

/-- A valid slot reads the compact record whose ordinal is the number of true
bits preceding it. An invalid slot reads the padding without advancing. -/
theorem get_expand (pad : A) (mask : List Bool) (rows : List A) (i : ℕ) (hi : i < mask.length) :
    (expand pad (mask, rows))[i]? = some
      (bif mask[i] then rows[(mask.take i).count true]?.getD pad else pad) := by
  induction mask generalizing rows i with
  | nil => simp at hi
  | cons b mask ih =>
    cases i with
    | zero => cases b <;> cases rows <;> rfl
    | succ i =>
      have hi' : i < mask.length := by simpa using hi
      cases b with
      | false => simpa [expand_cons] using ih rows i hi'
      | true =>
        cases rows with
        | nil => simpa [expand_cons] using ih [] i hi'
        | cons x rows => simpa [expand_cons] using ih rows i hi'

/-- Under the valid-slot count promise, unpacking then repacking is the identity. -/
theorem compress_expand (pad dummy : A) (mask : List Bool) (rows : List A)
    (hlen : mask.count true = rows.length) : compress dummy (mask, expand pad (mask,rows)) = rows := by
  let xs := mask.zip (expand pad (mask,rows))
  have hx : xs.map Prod.fst = mask := by simp [xs, List.map_fst_zip]
  have hy : xs.map Prod.snd = expand pad (mask,rows) := by simp [xs, List.map_snd_zip]
  have hcomp := compress_tagged dummy xs
  rw [hx, hy] at hcomp
  rw [hcomp]
  change selected (mask.zip (expand pad (mask,rows))) = rows
  clear hcomp hx hy xs
  induction mask generalizing rows with
  | nil => cases rows <;> simp_all [selected]
  | cons b mask ih =>
    cases b with
    | false =>
      simpa [expand_cons, selected] using ih rows (by simpa using hlen)
    | true =>
      cases rows with
      | nil => simp at hlen
      | cons x rows =>
        simpa [expand_cons, selected] using ih rows (by simpa using hlen)

private def preferRecord (p : List A × List A) : List A :=
  bif p.2.isEmpty then p.1 else p.2

private def mergePads (p : List (List A) × List (List A)) : List A :=
  (lock preferRecord [] [] p).flatten

/-- Padding record supplied on the tape, with one copy created per address. -/
def expandWith (p : List Bool × List A × A) : List A :=
  mergePads (List.replicate p.1.length [p.2.2], Ribbon.dress true (p.1,p.2.1))

theorem expandWith_tagged (pad : A) (xs : List (Bool × A)) :
    expandWith (xs.map Prod.fst, selected xs, pad) =
      xs.map (fun p => bif p.1 then p.2 else pad) := by
  unfold expandWith mergePads lock
  rw [← read_selected, Ribbon.frame, List.length_map, ← List.map_const' (l := xs), fair]
  simp only [List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨b,x⟩ := x
    cases b <;> simpa [Function.comp_def, Ribbon.keep, preferRecord] using ih

/-- A data-dependent pad may occupy the width of a whole record. This budget
explicitly charges for writing its `N` copies. -/
theorem expandWith_computes [Codec A] :
    Computes (fun p : List Bool × List A × A => size p + (p.1.length+1)*size [p.2.2])
      expandWith := by
  let pre (p : List Bool × List A × A) :=
    ((ruler p.1, [p.2.2]), Ribbon.dress true (p.1,p.2.1))
  let mid (p : List Bool × List A × A) :=
    (List.replicate p.1.length [p.2.2], Ribbon.dress true (p.1,p.2.1))
  have hpre : Easy pre := by
    apply Easy.pair (by fun_prop)
    exact (show Easy (fun p : List Bool × List A × A => (p.1,p.2.1)) by fun_prop).compose
      (Ribbon.easyDress true)
  have hg := (generate.on (fun p : List Bool × List A × A => (ruler p.1,[p.2.2]))).left
    (fun p => send (Ribbon.dress true (p.1,p.2.1)))
  have gen : Task (fun p : List Bool × List A × A => (p.1.length+1)*size [p.2.2])
      (fun p => send (pre p)) (fun p => send (mid p)) := by
    simpa only [pre, mid, ruler_length, send_prod] using hg
  have stage := Task.compose hpre gen
  have pref : Easy (preferRecord (A := A)) := by
    have empty : Easy (fun t : List A => t.isEmpty) := by
      have e : (fun t : List A => t.isEmpty) =
          (fun t => List.casesOn (motive := fun _ => Bool) t true (fun _ _ => false)) := by
        funext xs; cases xs <;> rfl
      rw [e]
      exact Easy.listCase true (Easy.const false)
    exact ((Easy.snd.compose empty).pair Easy.identity).compose
      (Easy.ifst Easy.snd Easy.fst)
  have post : Easy (mergePads (A := A)) := (easy_lock _ pref [] []).compose Easy.flatten
  obtain ⟨C,hC⟩ := stage.sizeBound
  refine (stage.compose (post.on mid)).bound (C+3) ?_
  intro p
  specialize hC p
  change size (mid p) ≤ size p + C * (size p + (p.1.length+1)*size [p.2.2] + 1) at hC
  rw [Nat.add_mul C 3]
  omega

/-- Total encoded volume for a masked scan with `N` slots and record size at most `w`. -/
def scanVolume (N w : ℕ) : ℕ := (N+1)*(w+1)

private theorem rows_size [Codec A] (rows : List A) (w : ℕ) (hw : ∀ x ∈ rows, size x ≤ w) :
    size rows ≤ rows.length * (w+1) + 1 := by
  induction rows with
  | nil => simp
  | cons x rows ih =>
    have h := hw x List.mem_cons_self
    have t := ih fun y hy => hw y (List.mem_cons_of_mem _ hy)
    rw [size_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem pair_size [Codec A] (mask : List Bool) (rows : List A) (w : ℕ)
    (hlen : rows.length ≤ mask.length) (hw : ∀ x ∈ rows, size x ≤ w) :
    size (mask,rows) ≤ 3 * scanVolume mask.length w + 3 := by
  have a := (rows_size rows w hw).trans (Nat.add_le_add_right
    (Nat.mul_le_mul_right (w+1) (hlen.trans (Nat.le_succ _))) 1)
  have b : mask.length + 1 ≤ scanVolume mask.length w :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change size rows ≤ scanVolume mask.length w + 1 at a
  simp only [size_prod, Bits.size_word]
  omega

/-- Any of the fixed linear scans above has a single task with an explicit
`(N+1)(w+1)` step budget, including framing the encoded mask and all records. -/
theorem scan_task {I B : Type} [Codec A] [Codec B]
    (f : List Bool × List A → B) (hf : Easy f) (mask : I → List Bool)
    (rows : I → List A) (w : I → ℕ) (hlen : ∀ i, (rows i).length ≤ (mask i).length)
    (hw : ∀ i x, x ∈ rows i → size x ≤ w i) :
    Task (fun i => scanVolume (mask i).length (w i)) (fun i => send (mask i, rows i))
      (fun i => send (f (mask i, rows i))) := by
  apply (hf.on fun i => (mask i, rows i)).bound 4
  intro i
  have := pair_size (mask i) (rows i) (w i) (hlen i) (hw i)
  omega

/-- Supplying a width-dependent record on the tape preserves the same scan budget. -/
theorem expandWith_task {I : Type} [Codec A] (mask : I → List Bool)
    (rows : I → List A) (pad : I → A) (w : I → ℕ) (hlen : ∀ i, (rows i).length ≤ (mask i).length)
    (hw : ∀ i x, x ∈ rows i → size x ≤ w i) (hpad : ∀ i, size (pad i) ≤ w i) :
    Task (fun i => scanVolume (mask i).length (w i)) (fun i => send (mask i,rows i,pad i))
      (fun i => send (expandWith (mask i,rows i,pad i))) := by
  apply (expandWith_computes.on fun i => (mask i,rows i,pad i)).bound 8
  intro i
  let N := (mask i).length
  let W := w i
  let V := scanVolume N W
  have pairBound := pair_size (mask i) (rows i) W (hlen i) (hw i)
  change size (mask i,rows i) ≤ 3 * V + 3 at pairBound
  have addrBound : N+1 ≤ V := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have wordBound : W+1 ≤ V := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have hp : size (pad i) ≤ W := hpad i
  have extra : (N+1)*size [pad i] ≤ V + (N+1) := by
    simp only [size_cons, size_nil]
    rw [show V+(N+1)=(N+1)*(W+1+1) by simp [V, scanVolume, Nat.mul_add]]
    exact Nat.mul_le_mul_left _ (by omega)
  change size (mask i,rows i,pad i) + (N+1)*size [pad i] + 1 ≤ 8*(V+1)
  simp only [size_prod] at pairBound ⊢
  omega

end BoxMaskedRecords

end NearSquareRoot
end Computability
end OAI
