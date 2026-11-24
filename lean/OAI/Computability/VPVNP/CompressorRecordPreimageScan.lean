import OAI.Computability.VPVNP.CompressorRecordPreimages
import OAI.Computability.VPVNP.RAMBuckets

/-!
# The preimage-list pass of the descriptor builder

Store the selected placement in increasing old-site order, followed by a count per new
site and a rectangular array of bounded preimage lists. The native visit from
`CompressorRecordPreimages` appends one old-site identifier to exactly its selected row.
The complete pass builds the placement fibers in scan order using five calls-plus-probes
per old site, starting with a zero count in each new-site row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- The owner inputs, the list counters and the row data occupy disjoint address ranges. -/
structure RowRegions (pub : Fin 6 → Word w) : Prop where
  ownersBeforeCounts : (pub 1).val + (pub 0).val ≤ (pub 3).val
  countsBeforeRows : (pub 3).val + (pub 2).val ≤ (pub 5).val
  rowsFit : (pub 5).val + (pub 2).val * (pub 4).val ≤ 2 ^ w

/-- All old identifiers below the scan cursor which have the specified owner. -/
def preimagePrefix (place : Word w → Word w) (owner : Word w) (k : ℕ) : List (Word w) :=
  ((List.range k).map (fun j => Fin.ofNat (2 ^ w) j)).filter fun j => place j == owner

private theorem preimagePrefix_succ (place : Word w → Word w) (owner : Word w) (k : ℕ) :
    preimagePrefix place owner (k + 1) =
      preimagePrefix place owner k ++ (if place (Fin.ofNat (2 ^ w) k) = owner then [(Fin.ofNat (2 ^ w) k)] else []) := by
  simp only [preimagePrefix, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.filter_append, List.filter_cons, List.filter_nil, beq_iff_eq]

private theorem preimagePrefix_mono (place : Word w → Word w) (owner : Word w) :
    Monotone (fun k => (preimagePrefix place owner k).length) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [preimagePrefix_succ, List.length_append]
  omega

/-- Complete contents of the scan tables after the first `k` old sites. -/
structure PreimagesAt (pub : Fin 6 → Word w) (place : Word w → Word w)
    (mem : Memory w) (k : ℕ) : Prop where
  owners : ∀ i : Word w, i < pub 0 → ownerAt pub mem i = place i
  rows : ∀ v : Word w, v < pub 2 →
    rowRepresents mem (countAt pub v) (rowAt pub v) (preimagePrefix place v k)

private theorem countAt_val {pub : Fin 6 → Word w} (a : RowRegions pub)
    {v : Word w} (hv : v < pub 2) : (countAt pub v).val = (pub 3).val + v.val := by
  have h := a.countsBeforeRows
  have hb := (pub 5).isLt
  change v.val < (pub 2).val at hv
  rw [countAt, Fin.val_add, Nat.mod_eq_of_lt (by omega)]

private theorem rowAt_val {pub : Fin 6 → Word w} (a : RowRegions pub)
    {v : Word w} (hv : v < pub 2) : (rowAt pub v).val = (pub 5).val + v.val * (pub 4).val := by
  have h := a.rowsFit
  have hstep := Nat.mul_le_mul_right (pub 4).val (show v.val + 1 ≤ (pub 2).val from hv)
  rw [Nat.succ_mul] at hstep
  by_cases hc : (pub 4).val = 0
  · simp [rowAt, Fin.val_add, Fin.val_mul, hc, Nat.mod_eq_of_lt (pub 5).isLt]
  · rw [rowAt, Fin.val_add, Fin.val_mul, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]

/-- A valid row of a different owner is disjoint from the current owner's row. -/
private theorem rows_apart {pub : Fin 6 → Word w} (a : RowRegions pub)
    {v u : Word w} (hv : v < pub 2) (hu : u < pub 2) (hne : v ≠ u) :
    (rowAt pub v).val + (pub 4).val ≤ (rowAt pub u).val ∨
    (rowAt pub u).val + (pub 4).val ≤ (rowAt pub v).val := by
  rw [rowAt_val a hv, rowAt_val a hu]
  have hn : v.val ≠ u.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hn with h | h
  · left
    have hh := Nat.mul_le_mul_right (pub 4).val (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at hh
    omega
  · right
    have hh := Nat.mul_le_mul_right (pub 4).val (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at hh
    omega

private theorem row_fits {pub : Fin 6 → Word w} (a : RowRegions pub)
    {v : Word w} (hv : v < pub 2) :
    (rowAt pub v).val + (pub 4).val ≤ 2 ^ w := by
  rw [rowAt_val a hv]
  have h := Nat.mul_le_mul_right (pub 4).val (show v.val + 1 ≤ (pub 2).val from hv)
  rw [Nat.succ_mul] at h
  have := a.rowsFit
  omega

private theorem count_before_row {pub : Fin 6 → Word w} (a : RowRegions pub)
    {u v : Word w} (hu : u < pub 2) (hv : v < pub 2) :
    (countAt pub u).val < (rowAt pub v).val := by
  rw [countAt_val a hu, rowAt_val a hv]
  change u.val < (pub 2).val at hu
  have := a.countsBeforeRows
  omega

theorem preimagesAt_step {pub : Fin 6 → Word w} (a : RowRegions pub) {place : Word w → Word w}
    (legal : ∀ i : Word w, i < pub 0 → place i < pub 2)
    (capacity : ∀ v : Word w, v < pub 2 →
      (preimagePrefix place v (pub 0).val).length ≤ (pub 4).val)
    {i : Word w} (hi : i < pub 0) {mem : Memory w} (h : PreimagesAt pub place mem i.val) :
    ownerAt pub mem i < pub 2 ∧ mem (countAt pub (ownerAt pub mem i)).val < pub 4 ∧
      PreimagesAt pub place (collectUpdate pub mem i) (i.val + 1) := by
  let v := place i
  have hv : v < pub 2 := legal i hi
  have howner : ownerAt pub mem i = v := h.owners i hi
  have row := h.rows v hv
  have hi' : i.val + 1 ≤ (pub 0).val := hi
  have hiCast : Fin.ofNat (2 ^ w) i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hprefix : preimagePrefix place v (i.val + 1) = preimagePrefix place v i.val ++ [i] := by
    rw [preimagePrefix_succ, hiCast, ite_eq_left (show place i = v from rfl)]
  have hlen : (preimagePrefix place v i.val).length < (pub 4).val := by
    have hh := (preimagePrefix_mono place v hi').trans (capacity v hv)
    simp only [hprefix, List.length_append, List.length_singleton] at hh
    omega
  have hcap : (mem (countAt pub v).val).val < (pub 4).val := row.1.trans_lt hlen
  refine ⟨howner ▸ hv, howner ▸ hcap, ?_⟩
  let addr := rowAt pub v + mem (countAt pub v).val
  have haddr : addr.val = (rowAt pub v).val + (mem (countAt pub v).val).val := by
    have := row_fits a hv
    rw [show addr = _ from rfl, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  have hwrite : collectUpdate pub mem i =
      writeMemory (writeMemory mem addr i) (countAt pub v) (mem (countAt pub v).val + 1) := by
    simp [collectUpdate, howner, addr]
  rw [hwrite]
  constructor
  · intro j hj
    have hstart := a.ownersBeforeCounts
    change j.val < (pub 0).val at hj
    have hbefore : (pub 1 + j).val < (countAt pub v).val := by
      rw [countAt_val a hv, Fin.val_add, Nat.mod_eq_of_lt (by have := (pub 3).isLt; omega)]
      omega
    have hrow := count_before_row a hv hv
    simpa [ownerAt, writeMemory, hbefore.ne, show (pub 1 + j).val ≠ addr.val by omega]
      using h.owners j hj
  · intro u hu
    by_cases he : u = v
    · subst u
      rw [hprefix]
      exact appendRecord_represents row hlen (row_fits a hv) (Or.inl (count_before_row a hv hv))
    · rw [preimagePrefix_succ, hiCast, ite_eq_right (Ne.symm he), List.append_nil]
      have hca : (countAt pub u).val ≠ (countAt pub v).val := by
        rw [countAt_val a hu, countAt_val a hv]
        exact fun hh => he (Fin.ext (Nat.add_left_cancel hh))
      have hur := count_before_row a hu hv
      have huc := count_before_row a hv hu
      obtain ⟨hl, hvals⟩ := h.rows u hu
      constructor
      · simpa [writeMemory, hca, show (countAt pub u).val ≠ addr.val by omega] using hl
      · intro b
        have hb := (preimagePrefix_mono place u (Nat.le_of_lt hi)).trans (capacity u hu)
        change (preimagePrefix place u i.val).length ≤ (pub 4).val at hb
        have hbl := b.isLt
        have hrows := rows_apart a hu hv he
        simpa [writeMemory, show (rowAt pub u).val + b.val ≠ (countAt pub v).val by omega,
          show (rowAt pub u).val + b.val ≠ addr.val by omega] using hvals b

/-- All calls of the actual preimage pass, starting at any valid intermediate cursor.
The final memory contains the complete ordered fibers through the resulting cursor. -/
theorem collectPreimages_run {pub : Fin 6 → Word w} (a : RowRegions pub)
    {place : Word w → Word w} (legal : ∀ i : Word w, i < pub 0 → place i < pub 2)
    (capacity : ∀ v : Word w, v < pub 2 →
      (preimagePrefix place v (pub 0).val).length ≤ (pub 4).val)
    {mem : Memory w} {k : ℕ} (h : PreimagesAt pub place mem k)
    (steps : ℕ) (hb : k + steps ≤ (pub 0).val) :
    let M := (template collectPreimage 3).instantiate w pub
    ∃ rs, runSegment M.program 23 (some (Fin.ofNat (2^w) k)) mem (List.replicate steps []) = some rs ∧
      PreimagesAt pub place (after mem (eventLog rs)) (k + steps) ∧
      rs.length = steps ∧ ∀ r ∈ rs, r.events.length = 22 ∧ countProbes r.events = 4 := by
  let M := (template collectPreimage 3).instantiate w pub
  induction steps generalizing k mem with
  | zero => exact ⟨[], rfl, h, rfl, by simp⟩
  | succ s ih =>
    let i := Fin.ofNat (2 ^ w) k
    have hmax := (pub 0).isLt
    have hval : i.val = k := Nat.mod_eq_of_lt (by omega)
    have hi : i < pub 0 := by change i.val < _; omega
    obtain ⟨ho, hcap, hnext⟩ := preimagesAt_step a legal capacity hi (hval ▸ h)
    have h1 : 1 % (2^w) = 1 := Nat.mod_eq_of_lt (by omega)
    have hnexti : i + 1 = Fin.ofNat (2^w) (k+1) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one' _, h1, hval]
      rfl
    let es := collectEvents pub mem i
    let r : Report w := ⟨es, some (i + 1)⟩
    obtain ⟨rs, hrun, hrows, hlength, hcounts⟩ := ih (k := k + 1) (hval ▸ hnext) (by omega)
    refine ⟨r :: rs, ?_, ?_, by simp [hlength], ?_⟩
    · change runSegment M.program 23 (some i) mem (List.replicate (s+1) []) = _
      rw [List.replicate_succ, runSegment, collectPreimage_native pub mem i hi ho hcap]
      simp only [M, r, es, after_collectEvents, hnexti, hrun, Option.map_some]
    · have hm : after mem (eventLog (r :: rs)) = after (collectUpdate pub mem i) (eventLog rs) := by
        change List.foldl update mem (es ++ eventLog rs) = _
        rw [List.foldl_append]
        rfl
      simpa [hm, Nat.add_assoc, Nat.add_comm 1 s] using hrows
    · intro rep hr
      rcases List.mem_cons.mp hr with rfl | hs
      · exact collectEvents_work pub mem i
      · exact hcounts rep hs

/-- In particular the pass uses exactly one call and four external probes per old site. -/
theorem preimagePass_cost {rs : List (Report w)} (h : ∀ r ∈ rs, countProbes r.events = 4) :
    RAMBuckets.cost (fun r : Report w => countProbes r.events) rs = 5 * rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    rw [RAMBuckets.cost, h r (List.mem_cons_self ..), ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      List.length_cons, Nat.mul_succ]
    omega

end CompressorRecords

end VPVNP
end Computability
end OAI
