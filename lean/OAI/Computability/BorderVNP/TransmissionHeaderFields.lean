import OAI.Computability.BorderVNP.DiagonalTallyRAMBroadcast
import Mathlib.Data.List.SplitLengths

/-! # The mode bit, auxiliary bits and subtotal fields in a common transmission header

Evaluation carries fixed-width little-endian subtotal claims in row-major order.
The unit branch uses the all-zero header of the same physical length. The copied
words, including a possible zero padding suffix, supply the actual native tally
reader at the address immediately following the mode and auxiliary bits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

variable {R d b w : ℕ}

/-- Evaluation-mode spelling for a candidate list of subtotal fields. -/
def spelling (aux : List Bool) (fields : List (List Bool)) : List Bool :=
  true :: (aux ++ fields.flatten)

/-- Canonical evaluation header carrying each team's actual subtotal words. -/
def evaluation (aux : List Bool) (b : ℕ) (claims : Fin R → Fin d → ℕ) : List Bool :=
  spelling aux (DiagonalTallyRAM.broadcast b claims)

/-- The all-zero unit-mode header occupies the same reserved range. -/
def unit (length : ℕ) : List Bool := List.replicate length false

/-- Append exactly the unused zero bits of a fixed-width transmission header. -/
def padded (header : List Bool) (extra : ℕ) := header ++ List.replicate extra false

/-- The canonical claim bank has exactly one field per team and coordinate. -/
theorem field_count (claims : Fin R → Fin d → ℕ) (b : ℕ) :
    (DiagonalTallyRAM.broadcast b claims).length = R*d := by simp [DiagonalTallyRAM.broadcast]

/-- Every canonical subtotal word has the public field width, including zero-width words. -/
theorem field_width (claims : Fin R → Fin d → ℕ) (b : ℕ) :
    ∀ xs ∈ DiagonalTallyRAM.broadcast b claims, xs.length = b := by
  intro xs h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  exact length_wordBits _

/-- Number of literal subtotal bits broadcast in row-major order. -/
theorem flat_length (claims : Fin R → Fin d → ℕ) (b : ℕ) :
    (DiagonalTallyRAM.broadcast b claims).flatten.length = R*d*b := by
  rw [List.length_flatten, List.map_eq_replicate_iff.mpr (field_width claims b),
    List.sum_replicate_nat, field_count]

/-- One mode bit, the auxiliary bit string, and the full common subtotal bank. -/
theorem evaluation_length (aux : List Bool) (b : ℕ) (claims : Fin R → Fin d → ℕ) :
    (evaluation aux b claims).length = 1+aux.length+R*d*b := by
  simp only [evaluation,spelling,List.length_cons,List.length_append,flat_length]; omega

/-- Equal physical lengths of the canonical unit and zero-padded evaluation spellings. -/
theorem unit_length (aux : List Bool) (b extra : ℕ) (claims : Fin R → Fin d → ℕ) :
    (unit (1+aux.length+R*d*b+extra)).length = (padded (evaluation aux b claims) extra).length := by
  simp [unit,padded,evaluation_length]

/-- Every bit occupies one shared-memory word, with its literal Boolean value. -/
def FlatAt (m : Memory w) (base : ℕ) (xs : List Bool) : Prop :=
  ∀ i : Fin xs.length, m (base+i.val) = word w xs[i].toNat

/-- Read the initial segment of a copied physical bit bank. -/
theorem FlatAt.left {m : Memory w} {base : ℕ} {xs ys : List Bool} (h : FlatAt m base (xs++ys)) :
    FlatAt m base xs := by
  intro i
  have hi : i.val < (xs++ys).length := by simp; omega
  have k := h ⟨i.val,hi⟩
  change m (base+i.val) = word w (xs++ys)[i.val].toNat at k
  rwa [List.getElem_append_left i.isLt] at k

/-- Read the suffix at the physical address following the initial segment. -/
theorem FlatAt.right {m : Memory w} {base : ℕ} {xs ys : List Bool} (h : FlatAt m base (xs++ys)) :
    FlatAt m (base+xs.length) ys := by
  intro i
  have hi : xs.length+i.val < (xs++ys).length := by simp
  have k := h ⟨xs.length+i.val,hi⟩
  change m (base+(xs.length+i.val)) = word w (xs++ys)[xs.length+i.val].toNat at k
  change m ((base+xs.length)+i.val) = word w ys[i.val].toNat
  simpa only [List.getElem_append_right (by omega : xs.length ≤ xs.length+i.val),
    Nat.add_sub_cancel_left,Nat.add_assoc] using k

private theorem bitsFromFlat {m : Memory w} (hw : 0 < w) (base : ℕ) (xs : List Bool)
    (read : FlatAt m base xs) : DiagonalTallyBits.BitsAt m base xs := by
  induction xs generalizing base with
  | nil => trivial
  | cons x xs ih =>
    have h := read ⟨0,by simp⟩
    change m (base+0) = word w x.toNat at h
    have fit : x.toNat < 2^w := by have one := Nat.one_lt_two_pow hw.ne'; cases x <;> simp_all
    refine ⟨by rw [Nat.add_zero] at h; rw [h,word_val w _ fit],?_⟩
    exact ih (base+1) (FlatAt.right (xs := [x]) (ys := xs) read)

/-- Turn actual contiguous Boolean words into the nested native reader's per-field input.
At positive machine width both bit values have their ordinary natural readings. -/
theorem fieldsFromFlat {m : Memory w} (hw : 0 < w) (base : ℕ) (xs : List (List Bool))
    (read : FlatAt m base xs.flatten) : DiagonalTallyBits.WordsAt m base xs := by
  induction xs generalizing base with
  | nil => trivial
  | cons x xs ih =>
    change FlatAt m base (x++xs.flatten) at read
    exact ⟨bitsFromFlat hw base x read.left, ih (base+x.length) read.right⟩

/-- The first subtotal field begins immediately after the copied mode bit and auxiliary string. -/
theorem fieldsAt {m : Memory w} (hw : 0 < w) (copyBase : ℕ) (aux : List Bool)
    (xs : List (List Bool)) (read : FlatAt m copyBase (spelling aux xs)) :
    DiagonalTallyBits.WordsAt m (copyBase+1+aux.length) xs := by
  have tail : FlatAt m (copyBase+1) (aux++xs.flatten) :=
    FlatAt.right (xs := [true]) (ys := aux++xs.flatten) read
  exact fieldsFromFlat hw _ xs tail.right

/-- The same absolute field addresses are read from a header whose reservation ends in zeros. -/
theorem fieldsAt_padded {m : Memory w} (hw : 0 < w) (copyBase : ℕ) (aux : List Bool)
    (xs : List (List Bool)) (extra : ℕ) (read : FlatAt m copyBase (padded (spelling aux xs) extra)) :
    DiagonalTallyBits.WordsAt m (copyBase+1+aux.length) xs := fieldsAt hw copyBase aux xs read.left

/-- Specialization to the exact field values used to construct an evaluation run. -/
theorem evaluation_fieldsAt {m : Memory w} (hw : 0 < w) (copyBase : ℕ) (aux : List Bool)
    (b : ℕ) (claims : Fin R → Fin d → ℕ) (read : FlatAt m copyBase (evaluation aux b claims)) :
    DiagonalTallyBits.WordsAt m (copyBase+1+aux.length) (DiagonalTallyRAM.broadcast b claims) :=
  fieldsAt hw copyBase aux _ read

/-- The native reader interprets a flat claim bank in consecutive fields of the public width. -/
def splitFields (width count : ℕ) (bits : List Bool) : List (List Bool) :=
  (List.replicate count width).splitLengths bits

/-- Splitting at the public field boundaries consumes all bits of a correctly sized bank. -/
theorem splitFields_flatten (width count : ℕ) (bits : List Bool) (h : bits.length = count*width) :
    (splitFields width count bits).flatten = bits :=
  List.flatten_splitLengths _ _ (by rw [List.sum_replicate_nat,h])

/-- Every interpreted field has the public width, also when that width is zero. -/
theorem splitFields_width (width count : ℕ) (bits : List Bool) (h : bits.length = count*width) :
    ∀ s ∈ splitFields width count bits, s.length = width := by
  have eq := List.map_splitLengths_length bits (List.replicate count width) (by rw [List.sum_replicate_nat,h])
  intro s hs
  have mem := List.mem_map_of_mem (f := List.length) hs
  change s.length ∈ ((List.replicate count width).splitLengths bits).map List.length at mem
  rw [eq] at mem
  exact (List.mem_replicate.mp mem).2

private theorem split_flatten (xs : List (List Bool)) :
    (xs.map List.length).splitLengths xs.flatten = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- Reading the canonical flat bit bank restores the exact original subtotal fields. -/
theorem splitFields_broadcast (b : ℕ) (claims : Fin R → Fin d → ℕ) :
    splitFields b (R*d) (DiagonalTallyRAM.broadcast b claims).flatten =
      DiagonalTallyRAM.broadcast b claims := by
  have lengths := List.map_eq_replicate_iff.mpr (field_width claims b)
  rw [field_count] at lengths
  rw [splitFields,← lengths,split_flatten]

/-- An arbitrary correctly sized copied claim string directly supplies the native
reader's consecutive fixed-width fields. -/
theorem splitFieldsAt {m : Memory w} (hw : 0 < w) (copyBase width count : ℕ) (aux raw : List Bool)
    (size : raw.length = count*width) (read : FlatAt m copyBase (true :: (aux++raw))) :
    DiagonalTallyBits.WordsAt m (copyBase+1+aux.length) (splitFields width count raw) := by
  apply fieldsAt hw copyBase aux
  rwa [spelling,splitFields_flatten width count raw size]

/-- Exactly one literal flat claim string decodes to a given bounded table of counts.
Fixed-width splitting and flattening are inverse even for empty banks or zero-width fields. -/
theorem unique_claim_bits (claims : Fin R → Fin d → ℕ) (hb : b ≤ w) (fits : ∀ i j, claims i j < 2^b) :
    ∃! raw : List Bool, raw.length = R*d*b ∧
      ∀ i j, DiagonalTallyRAM.fieldWord w (splitFields b (R*d) raw) i j = word w (claims i j) := by
  let fields := DiagonalTallyRAM.broadcast b claims
  refine ⟨fields.flatten,⟨flat_length claims b,?_⟩,?_⟩
  · intro i j
    rw [show splitFields b (R*d) fields.flatten = fields from splitFields_broadcast ..]
    exact DiagonalTallyRAM.fieldWord_broadcast claims fits i j
  · rintro raw ⟨n,h⟩
    have hu := DiagonalTallyRAM.unique_broadcast claims hb fits
    have eq := hu.unique (y₁ := splitFields b (R*d) raw) (y₂ := fields)
      ⟨by simp [splitFields],splitFields_width b (R*d) raw n,h⟩
      ⟨field_count claims b,field_width claims b,DiagonalTallyRAM.fieldWord_broadcast claims fits⟩
    rw [← eq,splitFields_flatten b (R*d) raw n]

/-- Every evaluation header whose interpreted claims pass the actual native tally checks
is the canonical spelling of the checked local counts. The auxiliary bits are fixed here. -/
theorem evaluation_of_complete_runs (aux bits : List Bool) (claims : Fin R → Fin d → ℕ)
    (hb : b ≤ w) (fits : ∀ i j, claims i j < 2^b) (count : bits.length = R*d*b)
    (f : Fin R → DiagonalTallyRAM.Frame) (pub : Fin R → Arg → Word w)
    (mac : Fin R → TeamOpcode.Macros w 8) (s : Fin R → Bank w) (m : Fin R → Memory w)
    (rs : Fin R → List (ℕ × ℕ)) (hf : ∀ i, (f i).dim = d ∧ (f i).team = i.val)
    (input : ∀ i, DiagonalTallyRAM.Input (f i) (pub i) (m i) (rs i) (splitFields b (R*d) bits))
    (localCounts : ∀ i (j : Fin d), DiagonalTallyScatter.after (f i).localBase (rs i) (m i)
      ((f i).localBase+j.val) = word w (claims i j))
    (accepted : ∀ i, ∃ es t mt, Runs (pub i) (mac i) DiagonalTallyRAM.complete (s i) (m i) es t mt) :
    true :: (aux++bits) = evaluation aux b claims := by
  have eq := DiagonalTallyRAM.broadcast_of_complete_runs claims hb fits (splitFields b (R*d) bits)
    (by simp [splitFields]) (splitFields_width b (R*d) bits count) f pub mac s m rs hf input localCounts accepted
  rw [evaluation,spelling,← eq,splitFields_flatten b (R*d) bits count]

end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
