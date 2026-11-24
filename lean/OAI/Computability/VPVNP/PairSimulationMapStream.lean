import OAI.Computability.VPVNP.PairSimulationMapLookup

/-!
# Reading a grouped motif one copy at a time

Each iteration checks the two ends of all incident selectors against the
anchor, decodes the common tag, and reads the local demand and payload row.
The cursor advances on every supply edge, including edges away from the
party. The terminal test compares this entire vector with the descriptor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapStream

open MotifSelector MotifEntry

variable {J D E S V : Type*} {bits u : ℕ}

/-- Offsets of the next copy and labels of the completed copies, newest first. -/
structure Cursor (E V : Type*) where
  /-- Cumulative payload width already consumed on each supply edge, giving the starting bit
  offset of the next copy. -/
  offset : E → ℕ
  /-- Labels obtained from completed copies, stored newest first so the scan can prepend each
  new row result. -/
  labelsRev : List V

/-- Read one selector and one row per iteration. A malformed copy stops the scan. -/
def scan (width : S → E → ℕ) : {n : ℕ} → (Fin n → Option S) →
    (Fin n → S → (E → ℕ) → V) → Cursor E V → Option (Cursor E V)
  | 0, _, _, c => some c
  | n + 1, select, row, c => (select 0).bind fun s ↦
    scan width (n := n) (fun i ↦ select i.succ) (fun i ↦ row i.succ)
      ⟨fun e ↦ c.offset e + width s e, row 0 s c.offset :: c.labelsRev⟩

/-- At a copy boundary the cumulative offset fits a fixed multiple of the copy index,
even for a descriptor whose final width test will fail. -/
theorem offset_le {n W : ℕ} (width : S → E → ℕ) (hw : ∀ s e, width s e ≤ W)
    (θ : Fin n → S) (e : E) (i : Fin n) :
    MotifEntry.offset (fun l ↦ width (θ l) e) i ≤ i.val * W := by
  unfold MotifEntry.offset
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun t : Fin i.val ↦ fun _ ↦ hw (θ (Fin.castLE i.isLt.le t)) e)

/-- The full-vector comparison can use the same bound on arbitrary decoded selectors. -/
theorem totalWidth_le {n W : ℕ} (width : S → E → ℕ) (hw : ∀ s e, width s e ≤ W)
    (θ : Fin n → S) (e : E) : totalWidth width θ e ≤ n * W := by
  simpa [totalWidth] using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hw (θ i) e)

/-- A missing or inconsistent tag rejects the complete stream at any position. -/
theorem scan_none (width : S → E → ℕ) {n : ℕ} (select : Fin n → Option S)
    (row : Fin n → S → (E → ℕ) → V) (c : Cursor E V) (i : Fin n)
    (hi : select i = none) : scan width select row c = none := by
  induction n generalizing c with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i hi
    · intro h
      simp [scan, h]
    · intro h
      cases he : select 0 with
      | none => simp [scan, he]
      | some s =>
        simp only [scan, he, Option.bind_some]
        exact ih _ _ _ j h

private theorem offset_zero {n : ℕ} (w : Fin (n + 1) → ℕ) : MotifEntry.offset w 0 = 0 := by
  change (∑ t : Fin 0, w (Fin.castLE (by omega) t)) = 0
  simp

private theorem offset_succ {n : ℕ} (w : Fin (n + 1) → ℕ) (i : Fin n) :
    MotifEntry.offset w i.succ = w 0 + MotifEntry.offset (fun j ↦ w j.succ) i := by
  unfold MotifEntry.offset
  simp only [Fin.val_succ]
  rw [Fin.sum_univ_succ]
  rfl

/-- The cursor before copy `i` is its prefix sum, the final cursor is the total,
and each accepted row appears with its original multiplicity and copy position. -/
theorem scan_some (width : S → E → ℕ) {n : ℕ} (select : Fin n → Option S)
    (row : Fin n → S → (E → ℕ) → V) (c : Cursor E V) (θ : Fin n → S)
    (ht : ∀ i, select i = some (θ i)) :
    scan width select row c =
      some ⟨fun e ↦ c.offset e + totalWidth width θ e,
        (List.ofFn fun i ↦ row i (θ i)
          (fun e ↦ c.offset e + MotifEntry.offset (fun l ↦ width (θ l) e) i)).reverse ++
          c.labelsRev⟩ := by
  induction n generalizing c with
  | zero => simp [scan, totalWidth]
  | succ n ih =>
    simp only [scan, ht 0, Option.bind_some]
    rw [ih _ _ _ (fun i ↦ θ i.succ) (fun i ↦ ht i.succ)]
    simp [List.ofFn_succ, totalWidth, Fin.sum_univ_succ, offset_succ,
      Nat.add_assoc, offset_zero]

variable [DecidableEq J] [Fintype E]

/-- Check both port directions at this copy, including both ends of a loop. -/
def agrees (G : Supply J E) (j : J) (tags : Half G (fun _ ↦ Fin u → Word bits) j)
    (i : Fin u) : Bool :=
  let t := anchor G j tags i
  decide (∀ e, (if h : j = G.src e then tags.1 e h i = t else True) ∧
    (if h : j = G.dst e then tags.2 e h i = t else True))

theorem consistent_iff_agrees (G : Supply J E) (j : J)
    (tags : Half G (fun _ ↦ Fin u → Word bits) j) :
    consistent G j tags = true ↔ ∀ i, agrees G j tags i = true := by
  simp only [consistent, agrees, decide_eq_true_eq]
  constructor
  · intro h i e
    obtain ⟨a, b⟩ := h e
    constructor <;> split at * <;> simp_all
  · intro h e
    constructor
    · split
      · rename_i he
        exact fun i ↦ by simpa [he] using (h i e).1
      · trivial
    · split
      · rename_i he
        exact fun i ↦ by simpa [he] using (h i e).2
      · trivial

/-- Restrict the input to one selector position to invoke the native whole-array
agreement test on this copy. -/
theorem agrees_eq_consistent_one (G : Supply J E) (j : J)
    (tags : Half G (fun _ ↦ Fin u → Word bits) j) (i : Fin u) :
    agrees G j tags i = consistent G j
      (mapHalf G (fun _ t (_ : Fin 1) ↦ t i) tags) := by
  let one := mapHalf G (fun _ t (_ : Fin 1) ↦ t i) tags
  have ha (k : Fin 1) : anchor G j one k = anchor G j tags i := by
    unfold anchor
    split <;> rfl
  apply Bool.eq_iff_iff.mpr
  change agrees G j tags i = true ↔ consistent G j one = true
  rw [consistent_iff_agrees]
  simp only [Fin.forall_fin_one, agrees, ha]
  rfl

/-- An unused anchor code and a mismatch between any two incident ports
both suppress the row lookup for this copy. -/
def selectCopy (G : Supply J E) (table : List S) (code : S ↪ Word bits)
    (j : J) (tags : Half G (fun _ ↦ Fin u → Word bits) j) (i : Fin u) : Option S :=
  if agrees G j tags i then decode table code (anchor G j tags i) else none

/-- A native precheck of the complete port arrays leaves just one anchor-table
lookup per copy in the subsequent loop. -/
theorem selectCopy_of_consistent (G : Supply J E) (table : List S) (code : S ↪ Word bits)
    (j : J) (tags : Half G (fun _ ↦ Fin u → Word bits) j)
    (ha : consistent G j tags = true) (i : Fin u) :
    selectCopy G table code j tags i = decode table code (anchor G j tags i) := by
  simp [selectCopy, (consistent_iff_agrees G j tags).1 ha i]

/-- The local base-matrix row indexed by demand and payload fields, starting
each payload field at the current cursor. -/
def readRow (src dst : D → J) (a b : D → ℕ) (G : Supply J E) (width : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e ↦ Word (width s e)) j → V)
    (v : E → ℕ) (j : J) (d : DemandBits src dst b j)
    (x : Half G (fun e ↦ Fin (v e + u * bits) → Bool) j)
    (i : Fin u) (s : S) (off : E → ℕ) : V :=
  lookup s j (demandFields src dst a i j d)
    (mapHalf G (fun e y ↦ fieldIndex (payloadBits y) (off e) (width s e)) x)

/-- Check all final payload offsets and restore the order of the emitted labels. -/
def finish (v : E → ℕ) (c : Cursor E V) : Option (List V) :=
  if ∀ e, v e = c.offset e then some c.labelsRev.reverse else none

/-- The complete streaming evaluator starts at zero and validates the full
vector before returning the labels in copy order. -/
def evaluate (src dst : D → J) (a b : D → ℕ) (G : Supply J E) (width : S → E → ℕ)
    (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e ↦ Word (width s e)) j → V)
    (table : List S) (code : S ↪ Word bits) (v : E → ℕ) (j : J)
    (d : DemandBits src dst b j) (x : Half G (fun e ↦ Fin (v e + u * bits) → Bool) j) :
    Option (List V) :=
  let tags := mapHalf G (fun _ ↦ readTag) x
  (scan width (selectCopy G table code j tags)
    (readRow src dst a b G width lookup v j d x) ⟨fun _ ↦ 0, []⟩).bind (finish v)

/-- Factor out a port-major native agreement pass. The remaining scan only
decodes the anchor and reads payload and demand rows. -/
theorem evaluate_after_consistency (src dst : D → J) (a b : D → ℕ) (G : Supply J E)
    (width : S → E → ℕ) (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e ↦ Word (width s e)) j → V)
    (table : List S) (code : S ↪ Word bits) (v : E → ℕ) (j : J)
    (d : DemandBits src dst b j) (x : Half G (fun e ↦ Fin (v e + u * bits) → Bool) j) :
    let tags := mapHalf G (fun _ ↦ readTag) x
    evaluate src dst a b G width lookup table code v j d x =
      if consistent G j tags then
        (scan width (fun i ↦ decode table code (anchor G j tags i))
          (readRow src dst a b G width lookup v j d x) ⟨fun _ ↦ 0, []⟩).bind (finish v)
      else none := by
  intro tags
  change (scan width (selectCopy G table code j tags)
    (readRow src dst a b G width lookup v j d x) ⟨fun _ ↦ 0, []⟩).bind (finish v) = _
  by_cases ha : consistent G j tags = true
  · rw [ite_eq_left ha, funext (selectCopy_of_consistent G table code j tags ha)]
  · have hm : ¬ ∀ i, agrees G j tags i = true := fun h ↦ ha ((consistent_iff_agrees G j tags).2 h)
    obtain ⟨i, hi⟩ := not_forall.mp hm
    rw [ite_eq_right ha, scan_none width (selectCopy G table code j tags) _ _ i
      (by simp [selectCopy, hi])]
    rfl

private theorem selectors_pointwise (table : List S) (code : S ↪ Word bits)
    (t : Fin u → Word bits) (θ : Fin u → S) :
    selectors? table code t = some θ ↔ ∀ i, decode table code (t i) = some (θ i) := by
  simp only [selectors?, Vector.getElem_ofFn]
  split
  · rename_i h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl i
      exact (Option.some_get (h i)).symm
    · intro he
      exact funext fun i ↦ Option.get_of_eq_some _ (he i)
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro he
    exact h fun i ↦ by simp [he i]

private theorem selectors_none (table : List S) (code : S ↪ Word bits) (t : Fin u → Word bits)
    (h : selectors? table code t = none) : ∃ i, decode table code (t i) = none := by
  by_contra! hn
  have hs (i : Fin u) := Option.isSome_iff_ne_none.mpr (hn i)
  have he := (selectors_pointwise table code t (fun i ↦ (decode table code (t i)).get (hs i))).2
    (fun i ↦ (Option.some_get (hs i)).symm)
  simp [h] at he

/-- Equivalence with the metered entry interpreter for arbitrary input bits and
arbitrary selector tables, with no consistency, completeness or width hypotheses. -/
theorem evaluate_eq_run [Fintype D] (src dst : D → J) (a b : D → ℕ) (G : Supply J E)
    (width : S → E → ℕ) (lookup : ∀ s j, MotifDemandPadding.HalfBits src dst a j →
      Half G (fun e ↦ Word (width s e)) j → V)
    (table : List S) (code : S ↪ Word bits) (v : E → ℕ) (j : J)
    (d : DemandBits src dst b j) (x : Half G (fun e ↦ Fin (v e + u * bits) → Bool) j) :
    evaluate src dst a b G width lookup table code v j d x =
      (MotifEntry.run src dst a b G width lookup table code v j d x).1 := by
  rw [MotifEntry.run_value]
  let tags := mapHalf G (fun _ ↦ readTag) x
  let row := readRow src dst a b G width lookup v j d x
  let sel := fun i ↦ decode table code (anchor G j tags i)
  let start : Cursor E V := ⟨fun _ ↦ 0, []⟩
  rw [evaluate_after_consistency]
  unfold describe labels indices
  change (if consistent G j tags then (scan width sel row start).bind (finish v) else none) =
    Option.map _ (if consistent G j tags then
      (selectors? table code (anchor G j tags)).bind _ else none)
  by_cases ha : consistent G j tags = true
  · simp only [ha, ↓reduceIte]
    cases hs : selectors? table code (anchor G j tags) with
    | none =>
      obtain ⟨i, hi⟩ := selectors_none _ _ _ hs
      rw [scan_none width sel row start i hi]
      rfl
    | some θ =>
      rw [scan_some width sel row start θ ((selectors_pointwise _ _ _ θ).1 hs)]
      simp only [Option.bind_some, extract, finish, start, Nat.zero_add, List.append_nil,
        List.reverse_reverse]
      split <;> rfl
  · simp [ha]


section FixedBlock

open MotifGrid MotifBlocks MotifConversion MotifDemandPadding MapLookup

variable {K J D E : Type} [Field K] [Fintype J] [Fintype D] [Fintype E]
  {src dst : D → J} {G : Supply J E} {p : D → ℚ} {q : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p) (realWidths q) H H')
  (z : B.grid.demands) (s : Selector B) (j : J) {wordWidth : ℕ}
  (fd : ∀ e, baseDemand B z e ≤ wordWidth) (fs : ∀ e, basePayload B s e ≤ wordWidth)

/-- The row search tests the finite word tuple used by the native lookup tree.
Neither the row table nor the field list depends on the number of repetitions. -/
noncomputable def searchRow (x : LabelRow B z s j) : Option (LabelRow B z s j) :=
  let key := labelKey B z s j fd fs
  (labelRows B z s j).find? (fun y ↦ (labelFields D E).all fun i ↦ decide (key x i = key y i))

theorem searchRow_eq (x : LabelRow B z s j) : searchRow B z s j fd fs x = some x := by
  let key := labelKey B z s j fd fs
  let isMatch := fun y ↦ (labelFields D E).all fun i ↦ decide (key x i = key y i)
  change (labelRows B z s j).find? isMatch = some x
  cases he : (labelRows B z s j).find? isMatch with
  | none =>
    have hm : isMatch x = true := by simp [isMatch]
    exact ((List.find?_eq_none.mp he x (mem_labelRows B z s j x)) hm).elim
  | some y =>
    have hm := List.find?_some he
    simp only [isMatch, List.all_eq_true, decide_eq_true_eq] at hm
    rw [labelKey_injective B z s j fd fs (funext (fun i ↦ hm i (mem_labelFields i)))]

/-- The name is taken from the matching row of the fixed matrix. -/
noncomputable def rowName (x : HalfBits src dst (baseDemand B z) j)
    (y : Half G (fun e ↦ Word (basePayload B s e)) j) : (parameterData B).Entry :=
  let found := searchRow B z s j fd fs (x, y)
  let r := found.get (by simp [found, searchRow_eq])
  lookup B z s j r.1 r.2

theorem rowName_eq (x : HalfBits src dst (baseDemand B z) j)
    (y : Half G (fun e ↦ Word (basePayload B s e)) j) :
    rowName B z s j fd fs x y = lookup B z s j x y := by
  simp [rowName, searchRow_eq]

variable [DecidableEq J]

/-- Execute the scan with the fixed selector and local matrix tables of this
block. The register width only has to contain the base digits used by the row tree. -/
noncomputable def runBlock (hp : ∀ e, 0 < p e) (demand : D → ℕ) (v : E → ℕ)
    (fd : ∀ e, baseDemand B (demandGrid B hp demand) e ≤ wordWidth)
    (fs : ∀ t e, basePayload B t e ≤ wordWidth) (j : J)
    (d : DemandBits src dst demand j)
    (x : Half G (fun e ↦ Fin (supplyWidths B demand v e) → Bool) j) :
    Option (List (parameterData B).Entry) :=
  let z := demandGrid B hp demand
  evaluate src dst (baseDemand B z) demand G (basePayload B)
    (fun s j ↦ rowName B z s j fd (fs s)) (selectorTable B) (selectorCode B) v j d x

theorem runBlock_eq_runEntry (hp : ∀ e, 0 < p e) (demand : D → ℕ) (v : E → ℕ)
    (fd : ∀ e, baseDemand B (demandGrid B hp demand) e ≤ wordWidth)
    (fs : ∀ t e, basePayload B t e ≤ wordWidth) (j : J)
    (d : DemandBits src dst demand j)
    (x : Half G (fun e ↦ Fin (supplyWidths B demand v e) → Bool) j) :
    runBlock B hp demand v fd fs j d x = (runEntry B hp demand v j d x).1 := by
  let z := demandGrid B hp demand
  have he : (fun s j ↦ rowName B z s j fd (fs s)) = lookup B z :=
    funext fun s ↦ funext fun j ↦ funext fun d ↦ funext fun x ↦ rowName_eq B z s j fd (fs s) d x
  unfold runBlock runEntry
  dsimp only
  rw [he]
  exact evaluate_eq_run ..

end FixedBlock

end PairSimulation.MapStream

end VPVNP
end Computability
end OAI
