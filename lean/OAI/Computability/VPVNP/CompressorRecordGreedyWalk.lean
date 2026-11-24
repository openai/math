import OAI.Computability.VPVNP.CompressorRecordGreedySlots
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMBuckets

/-!
# Indexed memory and complete greedy scans

The mutable assignments occupy one word per base vertex. Each fixed-stride
record following those cells contains the assignment's address, the address
of the next record, and the operand pointers read by the native visit. This
layout permits the same fixed instruction table to visit the entire base.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy

open BurstRAM BurstRAM.PrivateRAM Compression Compression.SlotGraph

variable {w N width : ℕ} {V A : Type*}

/-- `width` counts pointer words after each two-word header. -/
structure WalkLayout (w N width : ℕ) where
  /-- First address of the contiguous vertex assignments, followed by their fixed-stride greedy
  records. -/
  origin : ℕ
  fits : origin + N + N * (2 + width) ≤ 2 ^ w

namespace WalkLayout

variable (L : WalkLayout w N width)

/-- The mutable word for an indexed vertex. -/
def label (i : Fin N) : Word w := Fin.ofNat _ (L.origin + i.val)

/-- The descriptor for cursor `k`. After the last visit this is the return cursor. -/
def base (k : ℕ) : Word w := Fin.ofNat _ (L.origin + N + k * (2 + width))

@[simp] theorem label_val (i : Fin N) : (L.label i).val = L.origin + i.val :=
  Nat.mod_eq_of_lt (by have := L.fits; have := i.isLt; omega)

/-- Natural start of the following region, reserved for fixed graph data. -/
def limit : ℕ := L.origin + N + N * (2 + width)

private theorem field_lt (i : Fin N) {t : ℕ} (ht : t < 2 + width) :
    L.origin + N + i.val * (2 + width) + t < L.limit := by
  have h := Nat.mul_le_mul_right (2 + width) (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at h
  unfold limit
  omega

/-- The full descriptor, with the next pointer present also at the last vertex. -/
def record (ptrs : Fin N → List (Word w)) (i : Fin N) : List (Word w) :=
  L.label i :: L.base (i.val + 1) :: ptrs i

/-- Assemble the fixed-stride descriptor directory over the supplied memory.
The mutable assignment region starts at zero. Addresses beyond the table
retain their initial values, including fixed displacement operands. -/
def initialMemory (ptrs : Fin N → List (Word w)) (outside : Memory w) : Memory w := fun z ↦
  if z < L.origin then outside z else if z < L.origin + N then 0 else
    let off := z - (L.origin + N)
    let row := off / (2 + width)
    if h : row < N then ((L.record ptrs ⟨row, h⟩)[off % (2 + width)]?).getD 0 else outside z

@[simp] theorem initialMemory_label_offset (ptrs : Fin N → List (Word w)) (outside : Memory w)
    (i : Fin N) : L.initialMemory ptrs outside (L.origin + i.val) = 0 := by
  simp [initialMemory, Nat.add_lt_add_left i.isLt, Nat.not_lt.mpr (Nat.le_add_right ..)]

theorem initialMemory_label (ptrs : Fin N → List (Word w)) (outside : Memory w)
    (i : Fin N) : L.initialMemory ptrs outside (L.label i).val = 0 := by
  rw [label_val, initialMemory_label_offset]

theorem initialMemory_field (ptrs : Fin N → List (Word w)) (outside : Memory w)
    (i : Fin N) {t : ℕ} (ht : t < 2 + width) :
    L.initialMemory ptrs outside (L.origin + N + i.val * (2 + width) + t) =
      ((L.record ptrs i)[t]?).getD 0 := by
  let z := L.origin + N + i.val * (2 + width) + t
  have hsub : z - (L.origin + N) = i.val * (2 + width) + t := by dsimp [z]; omega
  have hd : (i.val * (2 + width) + t) / (2 + width) = i.val := by
    rw [Nat.mul_comm i.val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt ht, Nat.add_zero]
  change L.initialMemory ptrs outside z = _
  simp only [initialMemory, ite_eq_right (show ¬z < L.origin by dsimp [z]; omega),
    ite_eq_right (show ¬z < L.origin + N by dsimp [z]; omega), hsub, hd, dite_eq_left i.isLt,
    Nat.mul_add_mod_of_lt ht]

/-- Contents of the table relative to an arbitrary partially filled label vector. -/
structure Represents (initial m : Memory w) (encode : A → Word w) (order : V ≃ Fin N)
    (f : V → A) : Prop where
  labels : ∀ x, m (L.label (order x)).val = encode (f x)
  frame : ∀ z, z < L.origin ∨ L.origin + N ≤ z → m z = initial z

private theorem Represents.write [DecidableEq V] {initial m : Memory w} {encode : A → Word w}
    {order : V ≃ Fin N} {f : V → A} (rep : L.Represents initial m encode order f)
    (x : V) (v : A) : L.Represents initial (writeMemory m (L.label (order x)) (encode v))
      encode order (Function.update f x v) := by
  constructor
  · intro y
    by_cases h : y = x
    · subst y; simp [writeMemory]
    · have hn : (order y).val ≠ (order x).val := fun e ↦ h (order.injective (Fin.ext e))
      simpa [writeMemory, hn, Function.update_of_ne h] using rep.labels y
  · intro z hz
    have hne : z ≠ (L.label (order x)).val := by rw [label_val]; have := (order x).isLt; omega
    simpa only [writeMemory, ite_eq_right hne] using rep.frame z hz

private theorem stores_read (m : Memory w) (start : ℕ) (xs : List (Word w))
    (fit : start + xs.length ≤ 2 ^ w) (h : ∀ t : Fin xs.length, m (start + t.val) = xs[t.val]) :
    Stores m (Fin.ofNat _ start) xs := by
  induction xs generalizing start with
  | nil => trivial
  | cons x xs ih =>
    have hstart : start < 2 ^ w := by simp only [List.length_cons] at fit; omega
    constructor
    · simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hstart, Fin.val_zero, Nat.add_zero,
        List.getElem_cons_zero] using h 0
    · have hadd : (Fin.ofNat _ start : Word w) + 1 = Fin.ofNat _ (start + 1) := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_ofNat, Fin.val_one', Nat.mod_add_mod, Nat.add_mod_mod]
      rw [hadd]
      apply ih (start + 1) (by simp only [List.length_cons] at fit; omega)
      intro t
      simpa [Nat.add_assoc, Nat.add_comm 1] using h t.succ

/-- Writes to the assignment cells preserve all descriptor headers and pointers. -/
theorem Represents.record {ptrs : Fin N → List (Word w)} {outside m : Memory w}
    {encode : A → Word w} {order : V ≃ Fin N} {f : V → A}
    (rep : L.Represents (L.initialMemory ptrs outside) m encode order f)
    (size : ∀ i, (ptrs i).length = width) (i : Fin N) :
    Stores m (L.base i.val) (L.record ptrs i) := by
  have len : (L.record ptrs i).length = 2 + width := by simp [WalkLayout.record, size]; omega
  apply stores_read
  · rw [len]
    have h := Nat.mul_le_mul_right (2 + width) (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at h
    have := L.fits
    omega
  · intro t
    have ht : t.val < 2 + width := len ▸ t.isLt
    rw [rep.frame _ (.inr (by omega)), L.initialMemory_field ptrs outside i ht,
      List.getElem?_eq_getElem t.isLt, Option.getD_some]

private theorem finRange_indices (N : ℕ) : (List.finRange N).map Fin.val = List.range' 0 N := by
  apply List.ext_getElem
  · simp
  · intro t ht ht'
    simp

/-- The machine's complete native execution, final cursor, labels, and exact per-call cost. -/
def Pass (m : Memory w) (arity n : ℕ) (encode : A → Word w) (order : V ≃ Fin N)
    (f : V → A) : Prop :=
  ∃ reports, runSegment (visitMachine w arity n).program (1 + (visitCode arity n).length)
      (some (L.base 0)) m (List.replicate N []) = some reports ∧
    endState (some (L.base 0)) reports = some (L.base N) ∧
    L.Represents m (after m (eventLog reports)) encode order f ∧ reports.length = N ∧
    ∀ r ∈ reports, r.events.length = 12 + ((4 * arity + 4) * n + 4) * n ∧
      countProbes r.events = 3 + 2 * arity * n * n

/-- Total calls plus probes in the native scan, linear in the base size at fixed degree. -/
theorem Pass.cost {m : Memory w} {arity n : ℕ} {encode : A → Word w}
    {order : V ≃ Fin N} {f : V → A} (h : L.Pass m arity n encode order f) :
    ∃ rs, runSegment (visitMachine w arity n).program (1 + (visitCode arity n).length)
        (some (L.base 0)) m (List.replicate N []) = some rs ∧
      RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = N * (4 + 2 * arity * n * n) := by
  obtain ⟨rs, run, _, _, len, work⟩ := h
  refine ⟨rs, run, ?_⟩
  have count (xs : List (Report w)) (hs : ∀ r ∈ xs, countProbes r.events = 3 + 2 * arity * n * n) :
      RAMBuckets.cost (fun r ↦ countProbes r.events) xs = xs.length * (4 + 2 * arity * n * n) := by
    induction xs with
    | nil => simp [RAMBuckets.cost]
    | cons r xs ih =>
      rw [RAMBuckets.cost, hs r List.mem_cons_self, ih (fun s h ↦ hs s (List.mem_cons_of_mem _ h)),
        List.length_cons]
      ring
  rw [count rs (fun r hr ↦ (work r hr).2), len]

theorem scan_pass [DecidableEq V] {encode : A → Word w} (init : A) (hinit : encode init = 0)
    (order : V ≃ Fin N) (select : V → (V → A) → A) (ptrs : Fin N → List (Word w))
    (size : ∀ i, (ptrs i).length = width) (outside : Memory w) (arity n : ℕ)
    (step : ∀ m f i, L.Represents (L.initialMemory ptrs outside) m encode order f →
      Stores m (L.base i.val + 1 + 1) (ptrs i) →
      Visit m (L.base i.val) arity n (encode (select (order.symm i) f))) :
    L.Pass (L.initialMemory ptrs outside) arity n encode order
      ((List.finRange N).foldl (orderedUpdate order select) (fun _ ↦ init)) := by
  let P := (visitMachine w arity n).program
  let fuel := 1 + (visitCode arity n).length
  let initial := L.initialMemory ptrs outside
  have walk (ids : List (Fin N)) (k : ℕ) (seq : ids.map Fin.val = List.range' k ids.length)
      (m : Memory w) (f : V → A) (rep : L.Represents initial m encode order f) :
      ∃ rs, runSegment P fuel (some (L.base k)) m (List.replicate ids.length []) = some rs ∧
        endState (some (L.base k)) rs = some (L.base (k + ids.length)) ∧
        L.Represents initial (after m (eventLog rs)) encode order (ids.foldl (orderedUpdate order select) f) ∧
        rs.length = ids.length ∧ ∀ r ∈ rs, r.events.length = 12 + ((4 * arity + 4) * n + 4) * n ∧
          countProbes r.events = 3 + 2 * arity * n * n := by
    induction ids generalizing k m f with
    | nil => exact ⟨[], rfl, rfl, rep, rfl, by simp⟩
    | cons i ids ih =>
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at seq
      obtain ⟨rfl, tail⟩ := seq
      obtain ⟨hout, hnext, rows⟩ := rep.record L size i
      obtain ⟨es, he, hm, hsteps, hprobes⟩ := step m f i rep rows
      rw [hout] at hm
      rw [hnext] at he
      let r : Report w := ⟨es, some (L.base (i.val + 1))⟩
      have rep' : L.Represents initial (after m es) encode order (orderedUpdate order select f i) := by
        rw [hm]
        simpa only [orderedUpdate, Equiv.apply_symm_apply] using rep.write L (order.symm i) (select (order.symm i) f)
      obtain ⟨rs, run, hend, hfinal, hlen, hcost⟩ := ih _ tail _ _ rep'
      refine ⟨r :: rs, ?_, ?_, ?_, by simp [hlen], ?_⟩
      · simp only [List.length_cons, List.replicate_succ, runSegment, P, fuel, he, run, Option.map_some, r]
      · simpa only [endState, r, List.length_cons, Nat.add_right_comm i.val 1, Nat.add_assoc] using hend
      · change L.Represents initial (List.foldl update m (es ++ eventLog rs)) _ _ _
        rw [List.foldl_append]
        exact hfinal
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | h
        · exact ⟨hsteps, hprobes⟩
        · exact hcost _ h
  have rep0 : L.Represents initial initial encode order (fun _ ↦ init) :=
    ⟨fun x ↦ (L.initialMemory_label ptrs outside (order x)).trans hinit.symm, fun _ _ ↦ rfl⟩
  simpa only [Pass, List.length_finRange, Nat.zero_add, P, fuel, initial] using
    walk (List.finRange N) 0 (by simpa only [List.length_finRange] using finRange_indices N) _ _ rep0

/-- Fields beyond the fixed-stride records retain their supplied values. -/
theorem initialMemory_after (ptrs : Fin N → List (Word w)) (outside : Memory w)
    {z : ℕ} (hz : L.limit ≤ z) : L.initialMemory ptrs outside z = outside z := by
  unfold limit at hz
  have hq : N ≤ (z - (L.origin + N)) / (2 + width) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp only [initialMemory, ite_eq_right (show ¬z < L.origin by omega),
    ite_eq_right (show ¬z < L.origin + N by omega), dite_eq_right hq.not_gt]

variable {d j : ℕ}

/-- Actual operand addresses of the color visit, in incidence order. -/
def colorOperands (L : WalkLayout w N (2 * d)) (G : SlotGraph V d) (order : V ≃ Fin N)
    (i : Fin N) : List (Word w) := (colorRows G (order.symm i) (L.label ∘ order)).flatten

/-- Starting from zero assignments, the full native scan writes precisely the
ordered coloring. No condition on the memory surrounding its directory is needed. -/
theorem color_pass (L : WalkLayout w N (2 * d)) (G : SlotGraph V d) (order : V ≃ Fin N)
    (outside : Memory w) (hfit : 2 * d < 2 ^ w) :
    L.Pass (L.initialMemory (L.colorOperands G order) outside) 1 (2 * d)
      (fun v : Fin (2 * d + 1) ↦ Fin.ofNat _ v.val) order (G.orderedColor order) := by
  classical
  rw [orderedColor_fold]
  apply scan_pass L 0 (by simp) order G.chooseColor (L.colorOperands G order) _ outside
  · intro m f i rep rows
    apply color_visit G (order.symm i) f m _ (L.label ∘ order) _ rows hfit
    intro x
    have hx := congrArg Fin.val (rep.labels x)
    simpa only [Fin.val_ofNat, Function.comp_apply, Nat.mod_eq_of_lt
      (show (f x).val < 2 ^ w by have := (f x).isLt; omega)] using hx
  · intro i
    simp [colorOperands, colorRows, List.length_flatten, List.map_map, Function.comp_def]

/-- Number of four-operand tests for one tag. -/
abbrev tagCount (d : ℕ) := 2 * d * ((d + 1) + (d + 1) ^ 2)

/-- Place the zero word and the vertex-major array of outgoing tag displacements
immediately after the pointer directory. -/
def tagAddresses (L : WalkLayout w N (4 * tagCount d)) (order : V ≃ Fin N) : TagAddresses V d w :=
  ⟨Fin.ofNat _ L.limit,
    fun e ↦ Fin.ofNat _ (L.limit + 1 + (order e.1).val * d + e.2.val), L.label ∘ order⟩

/-- The four addresses of every test, laid out consecutively in tag test order. -/
def tagOperands (L : WalkLayout w N (4 * tagCount d)) (G : SlotGraph V d) (order : V ≃ Fin N)
    (i : Fin N) : List (Word w) :=
  ((tagTests d).map (tagPointers G (L.tagAddresses order) (order.symm i))).flatten

/-- Initialize the immutable operands from the indexed graph's displacements. -/
def tagData (L : WalkLayout w N (4 * tagCount d)) (order : V ≃ Fin N) (hw : j ≤ w)
    (τ : V × Fin d → BitWord j) (outside : Memory w) : Memory w := fun z ↦
  if z = L.limit then 0 else if z < L.limit + 1 then outside z else
    let off := z - (L.limit + 1)
    if hd : 0 < d then
      if hn : off / d < N then tagWord hw (τ (order.symm ⟨off / d, hn⟩, ⟨off % d, Nat.mod_lt _ hd⟩))
      else outside z
    else outside z

private theorem tag_data_rep (L : WalkLayout w N (4 * tagCount d)) (G : SlotGraph V d)
    (order : V ≃ Fin N) (hw : j ≤ w) (τ : V × Fin d → BitWord j) (outside : Memory w)
    (hfit : L.limit + 1 + N * d ≤ 2 ^ w) {m : Memory w} {f : V → BitWord j}
    (rep : L.Represents (L.initialMemory (L.tagOperands G order) (L.tagData order hw τ outside))
      m (tagWord hw) order f) : (L.tagAddresses order).Represents hw m τ f := by
  have hframe (z : ℕ) (hz : L.limit ≤ z) : m z = L.tagData order hw τ outside z :=
    (rep.frame z (.inr (by unfold limit at hz; omega))).trans (L.initialMemory_after _ _ hz)
  constructor
  · change m (Fin.ofNat (2 ^ w) L.limit).val = 0
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt (by omega), hframe _ le_rfl]
    simp [tagData]
  · rintro ⟨x, i⟩
    let z := L.limit + 1 + (order x).val * d + i.val
    have hs := Nat.mul_le_mul_right d (Nat.succ_le_of_lt (order x).isLt)
    rw [Nat.succ_mul] at hs
    have hslot := i.isLt
    have hval : z < 2 ^ w := by dsimp [z]; omega
    have hd : ((order x).val * d + i.val) / d = (order x).val := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt i.isLt, Nat.add_zero]
    change m (Fin.ofNat (2 ^ w) z).val = _
    rw [Fin.val_ofNat, Nat.mod_eq_of_lt hval, hframe _ (by dsimp [z]; omega)]
    simp only [tagData, ite_eq_right (show z ≠ L.limit by dsimp [z]; omega),
      ite_eq_right (show ¬z < L.limit + 1 by dsimp [z]; omega),
      show z - (L.limit + 1) = (order x).val * d + i.val by dsimp [z]; omega,
      dite_eq_left (show 0 < d by omega), hd, dite_eq_left (order x).isLt,
      Nat.mul_add_mod_of_lt i.isLt, Fin.eta, Equiv.symm_apply_apply]
  · exact rep.labels

/-- Starting from zero offsets and the graph's displacement array, the complete
native tag scan writes the same offsets as `orderedTagOffsets` in Appendix C. -/
theorem tag_pass (L : WalkLayout w N (4 * tagCount d)) (G : SlotGraph V d) (order : V ≃ Fin N)
    (τ : V × Fin d → BitWord j) (hw : j ≤ w) (hcard : tagCount d < 2 ^ j)
    (hfit : L.limit + 1 + N * d ≤ 2 ^ w) (outside : Memory w) :
    L.Pass (L.initialMemory (L.tagOperands G order) (L.tagData order hw τ outside))
      4 (tagCount d) (tagWord hw) order (G.orderedTagOffsets order (bitWordFinEquiv j) τ hcard) := by
  classical
  rw [orderedTagOffsets_fold]
  apply scan_pass L 0 (tagWord_zero hw) order (G.chooseTag (bitWordFinEquiv j) τ hcard)
    (L.tagOperands G order) _ (L.tagData order hw τ outside)
  · intro m f i rep rows
    exact tag_visit G (order.symm i) τ f hcard hw m _ _ (tag_data_rep L G order hw τ outside hfit rep) rows
  · intro i
    have hlen (t : TagTests d) : (tagPointers G (L.tagAddresses order) (order.symm i) t).length = 4 := by
      obtain ⟨⟨b, k⟩, a | ⟨a,c⟩⟩ := t <;> cases b <;> rfl
    simp [tagOperands, List.length_flatten, List.map_map, Function.comp_def, hlen, Nat.mul_comm]

end WalkLayout
end CompressorRecords.Greedy

end VPVNP
end Computability
end OAI
