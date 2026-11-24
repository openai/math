import OAI.Computability.VPVNP.LiveHeaderSparseLayout
import OAI.Computability.VPVNP.LiveHeaderCopyDispatch
import OAI.Computability.VPVNP.RAMChain

/-!
# Copying the seven populated auxiliary header fields

The persistent cursor ranges over a packed interval even though the virtual
header reserves space for both exterior fields at full capacity. The actual
machine reads the seven descriptors from external memory and writes the selected
word into the separate auxiliary region.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryHeaders

open BurstRAM PrimedInputRAM LiveHeaderCopyDispatch
open scoped Fin.CommRing

variable {w : ℕ}

/-- Descriptor ends are packed cursor positions; targets use sparse virtual offsets. -/
def records (L : Lengths) (N base : ℕ) (source : Fin 7 → Word w) (j : Fin 7) : Descriptor w :=
  ⟨(rangeStart L N j.succ : Word w), source j, ((base + destinationStart L j : ℕ) : Word w)⟩

private theorem prev_records (L : Lengths) (N base : ℕ) (source : Fin 7 → Word w) (j : Fin 7) :
    prevEnd (records L N base source) j = (rangeStart L N j.castSucc : Word w) := by
  fin_cases j <;> simp [prevEnd, records, rangeStart]

/-- The original, contiguous array address of each word in the packed iteration. -/
noncomputable def sourceAddress (L : Lengths) (N : ℕ) (source : Fin 7 → Word w)
    (i : Fin (populated L N)) : Word w :=
  let j := rangeAt L N i
  source j + ((i.val - rangeStart L N j.castSucc : ℕ) : Word w)

private theorem target_eq (L : Lengths) (N base : ℕ) (source : Fin 7 → Word w)
    (hfit : base + span L N ≤ 2^w) (i : Fin (populated L N)) :
    let j := rangeAt L N i
    let ds := records L N base source
    (ds j).targetBase + ((i.val : Word w) - prevEnd ds j) =
      scratchAddress base hfit (sparseOffset L N i) := by
  dsimp only
  rw [prev_records, ← Nat.cast_sub (rangeAt_bounds L N i).1]
  change ((base + destinationStart L (rangeAt L N i) : ℕ) : Word w) + _ = _
  rw [← Nat.cast_add, Nat.add_assoc, ← sparseOffset_at_range]
  apply Fin.ext
  rw [Fin.val_natCast, Nat.mod_eq_of_lt ((Nat.add_lt_add_left (sparseOffset L N i).isLt base).trans_le hfit)]
  rfl

private theorem store_mem_congr {n : ℕ} (dst : Fin n ↪ Word w) (v : Fin n → Word w)
    (a b : List (Fin n)) (h : ∀ j, j ∈ a ↔ j ∈ b) (m : Memory w) :
    store dst v a m = store dst v b m := by
  funext p
  by_cases ht : ∃ i ∈ a, (dst i).val = p
  · obtain ⟨i,hi,rfl⟩ := ht
    rw [store_at _ _ _ _ hi, store_at _ _ _ _ ((h i).1 hi)]
  · have outside (i : Fin n) (hi : i ∈ a) : p ≠ (dst i).val :=
      fun e => ht ⟨i, hi, e.symm⟩
    rw [store_outside _ _ _ _ _ outside,
      store_outside _ _ _ _ _ (fun i hi => outside i ((h i).2 hi))]

private theorem store_packed_eq_install (base : ℕ) (L : Lengths) (hdr : Header L → Bool)
    (hist : List (Word w)) (hfit : base + span L hist.length ≤ 2^w) (m : Memory w) :
    store (scratchAddress base hfit) (fun j => headerMemory L hdr hist j.val)
      ((List.finRange (populated L hist.length)).map (sparseOffset L hist.length)) m =
    install base L hdr hist hfit m := by
  apply store_mem_congr
  intro j
  rw [sparseOffset_range]
  simp

/-- Working areas and the dispatcher table are disjoint from every destination
word written by the sparse copy. Only the addresses actually read are required. -/
structure Separated (desc : Word w) (base : ℕ) (L : Lengths) (N : ℕ)
    (src : Fin 7 → Word w) (fit : base + span L N ≤ 2^w) : Prop where
  sources : ∀ i j : Fin (populated L N),
    (sourceAddress L N src i).val ≠ (scratchAddress base fit (sparseOffset L N j)).val
  table : ∀ row field (j : Fin (populated L N)),
    (address desc row field).val ≠ (scratchAddress base fit (sparseOffset L N j)).val

/-- State of the read-only arrays required for the copy. The three length words
and all populated data bits match the auxiliary machine's prescribed header. -/
structure Prepared (desc : Word w) (base : ℕ) (L : Lengths) (hdr : Header L → Bool)
    (hist : List (Word w)) (src : Fin 7 → Word w) (m : Memory w) : Prop where
  descriptors : Spec desc (records L hist.length base src) m
  sources : ∀ i : Fin (populated L hist.length),
    m (sourceAddress L hist.length src i).val = headerMemory L hdr hist (sparseOffset L hist.length i).val

theorem Prepared.write {desc : Word w} {base : ℕ} {L : Lengths} {hdr : Header L → Bool}
    {hist : List (Word w)} {src : Fin 7 → Word w} {m : Memory w}
    (h : Prepared desc base L hdr hist src m) {fit : base + span L hist.length ≤ 2^w}
    (sep : Separated desc base L hist.length src fit) (j : Fin (populated L hist.length)) (x : Word w) :
    Prepared desc base L hdr hist src (writeMemory m (scratchAddress base fit (sparseOffset L hist.length j)) x) := by
  constructor
  · constructor
    · intro r; simpa only [writeMemory, ite_eq_right (sep.table r 0 j)] using h.descriptors.ends r
    · intro r; simpa only [writeMemory, ite_eq_right (sep.table r 1 j)] using h.descriptors.sources r
    · intro r; simpa only [writeMemory, ite_eq_right (sep.table r 2 j)] using h.descriptors.targets r
  · intro i; simpa only [writeMemory, ite_eq_right (sep.sources i j)] using h.sources i

variable {desc : Word w} {base : ℕ} {L : Lengths} {hdr : Header L → Bool}
    {hist : List (Word w)} {src : Fin 7 → Word w}

theorem native_cell (fit : base + span L hist.length ≤ 2^w)
    (hwidth : populated L hist.length < 2^w) {m : Memory w}
    (h : Prepared desc base L hdr hist src m) (i : Fin (populated L hist.length)) :
    ∃ es, execute (program desc) 64 ((program desc).start (i.val : Word w)) m [] =
        some ⟨es, some ((i.val : Word w)+1)⟩ ∧
      after m es = writeMemory m (scratchAddress base fit (sparseOffset L hist.length i))
        (headerMemory L hdr hist (sparseOffset L hist.length i).val) ∧
      es.length < 64 ∧ countProbes es ≤ 11 ∧ choiceBits es = [] := by
  let ds := records L hist.length base src
  let row := rangeAt L hist.length i
  have endval (j : Fin 7) : (ds j).endOffset.val = rangeStart L hist.length j.succ := by
    exact Nat.mod_eq_of_lt ((rangeEnd_le L hist.length j).trans_lt hwidth)
  have curval : ((i.val : Word w) : ℕ) = i.val := Nat.mod_eq_of_lt (i.isLt.trans hwidth)
  have hskip (j : Fin 7) (hj : j < row) : (ds j).endOffset ≤ (i.val : Word w) := by
    change (ds j).endOffset.val ≤ ((i.val : Word w) : ℕ)
    rw [endval, curval]
    exact rangeAt_skips L hist.length i j hj
  have hhit : (i.val : Word w) < (ds row).endOffset := by
    change ((i.val : Word w) : ℕ) < (ds row).endOffset.val
    rw [endval, curval]
    exact (rangeAt_bounds L hist.length i).2
  have hs : (ds row).sourceBase + ((i.val : Word w) - prevEnd ds row) =
      sourceAddress L hist.length src i := by
    rw [prev_records, ← Nat.cast_sub (rangeAt_bounds L hist.length i).1]
    rfl
  obtain ⟨es,hr,hm,hh⟩ := row_native desc ds (i.val : Word w) m h.descriptors row hskip hhit
  rw [hs, target_eq L hist.length base src fit i, h.sources i] at hm
  exact ⟨es,hr,hm,hh⟩

private theorem run_packed (fit : base + span L hist.length ≤ 2^w)
    (hwidth : populated L hist.length < 2^w) (sep : Separated desc base L hist.length src fit)
    (indices : List (Fin (populated L hist.length))) (start : ℕ)
    (haligned : indices.map Fin.val = List.range' start indices.length)
    {m : Memory w} (h : Prepared desc base L hdr hist src m) :
    ∃ rs, runSegment (program desc) 64 (some (start : Word w)) m (List.replicate indices.length []) = some rs ∧
      endState (some (start : Word w)) rs = some ((start + indices.length : ℕ) : Word w) ∧
      after m (eventLog rs) = store (scratchAddress base fit) (fun j => headerMemory L hdr hist j.val)
        (indices.map (sparseOffset L hist.length)) m ∧
      rs.length = indices.length ∧ ∀ r ∈ rs, r.events.length < 64 ∧ countProbes r.events ≤ 11 ∧ choiceBits r.events = [] := by
  induction indices generalizing start m with
  | nil => exact ⟨[], rfl, rfl, rfl, rfl, by simp⟩
  | cons i indices ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at haligned
    obtain ⟨rfl,haligned⟩ := haligned
    obtain ⟨es, hr, hm, hl, hp, hc⟩ := native_cell fit hwidth h i
    have hprep : Prepared desc base L hdr hist src (after m es) := hm ▸ h.write sep i _
    obtain ⟨rs, hn, hs, hu, hlen, hh⟩ := ih (i.val+1) haligned hprep
    refine ⟨⟨es, some ((i.val : Word w)+1)⟩ :: rs, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.replicate_succ, runSegment, hr, ← Nat.cast_one (R := Word w), ← Nat.cast_add]
      rw [hn]
      rfl
    · simpa [endState, Nat.add_assoc, Nat.add_comm 1] using hs
    · change after m (es ++ eventLog rs) = store _ _ _ (writeMemory m _ _)
      rw [← hm]
      simpa [after] using hu
    · simp [hlen]
    · intro r hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨hl,hp,hc⟩
      · exact hh r hmem

/-- The compiled fixed dispatcher writes precisely the auxiliary header memory.
The count of calls is the number of populated words. No call visits a reserved
exterior padding slot. -/
theorem sweep_native (fit : base + span L hist.length ≤ 2^w)
    (hwidth : populated L hist.length < 2^w) (sep : Separated desc base L hist.length src fit)
    {m : Memory w} (h : Prepared desc base L hdr hist src m) :
    let n := populated L hist.length
    ∃ rs, runSegment (program desc) 64 (some 0) m (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (n : Word w) ∧ after m (eventLog rs) = install base L hdr hist fit m ∧
      rs.length = n ∧ ∀ r ∈ rs, r.events.length < 64 ∧ countProbes r.events ≤ 11 ∧ choiceBits r.events = [] := by
  let n := populated L hist.length
  have aligned : (List.finRange n).map Fin.val = List.range' 0 (List.finRange n).length := by
    simp [List.range_eq_range']
  have hr := run_packed fit hwidth sep (List.finRange n) 0 aligned h
  simpa only [n, Nat.cast_zero, List.length_finRange, Nat.zero_add, store_packed_eq_install] using hr

end LiveAuxiliaryHeaders

end VPVNP
end Computability
end OAI
