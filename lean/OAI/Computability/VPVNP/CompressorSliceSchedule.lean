import OAI.Computability.VPVNP.CompressorSlicePairVisit
import OAI.Computability.VPVNP.CompressorSlicePreparation
import OAI.Computability.VPVNP.CompressorSliceAdjacency
import OAI.Computability.VPVNP.RAMChain
import Mathlib.Data.List.OfFn

/-!
# Scheduling the compressor's interval records

The source-major Cartesian scan uses one persistent pair number. Its quotient
and remainder select source and target fields in their two external arrays.
The output frame for that pair consists of three words, two offsets and a
length. Empty intersections have length zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceSchedule

open BurstRAM BurstRAM.PrivateRAM Compression.PackingData

/-- Descriptor at a numerical array index. The default width occurs only
outside the array and is never read by a scheduled visit. -/
def fieldAt (ws : List ℕ) (i : ℕ) : Field :=
  ⟨i, (ws.take i).sum, ws[i]?.getD 0⟩

private theorem fields_eq_ofFn (ws : List ℕ) :
    fieldsFrom 0 0 ws = List.ofFn (fun i : Fin ws.length => fieldAt ws i) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have h : i < ws.length := by simpa using hi
  simp [fieldsFrom_get ws 0 0 i h, fieldAt]

/-- Read the pair whose row-major index is `k`. -/
def pairAt (old new : List ℕ) (k : ℕ) : Field × Field :=
  (fieldAt old (k / new.length), fieldAt new (k % new.length))

/-- Copy interval for the `k`th old/new field pair in source-major order. -/
def sliceAt (old new : List ℕ) (k : ℕ) : CopySlice :=
  let p := pairAt old new k
  copySlice p.1.start p.1.width p.2.start p.2.width

/-- The word-arithmetic index order is the order of the record builder's
Cartesian product, including fields of width zero. -/
theorem numbered_pairs (old new : List ℕ) :
    List.ofFn (fun k : Fin (old.length * new.length) => pairAt old new k) = candidates old new := by
  rw [List.ofFn_mul, candidates, fields_eq_ofFn, fields_eq_ofFn]
  change _ = List.flatten (List.map _ (List.ofFn _))
  rw [List.map_ofFn]
  congr 2
  funext i
  dsimp only [Function.comp_apply]
  rw [List.map_ofFn]
  congr 1
  funext j
  have hn : 0 < new.length := (Nat.zero_le j.val).trans_lt j.isLt
  have hd : (i.val * new.length + j.val) / new.length = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  simp [pairAt, hd, Nat.mod_eq_of_lt j.isLt]

/-- Number of records emitted among the first `t` candidate visits,
starting with persistent index `k`. -/
def emitted (old new : List ℕ) (k t : ℕ) : ℕ :=
  ((List.range' k t).map (pairAt old new)).countP (fun p => (intersectFields p).isSome)

private theorem emitted_succ (old new : List ℕ) (k t : ℕ) :
    emitted old new k (t+1) =
      (if (sliceAt old new k).length = 0 then 0 else 1) + emitted old new (k+1) t := by
  simp only [emitted, List.range'_succ, List.map_cons, List.countP_cons, intersectFields, sliceAt]
  split <;> simp [Nat.add_comm, *]

theorem emitted_all (old new : List ℕ) :
    emitted old new 0 (old.length * new.length) = (copyRecords old new).length := by
  rw [emitted, copyRecords, List.length_filterMap_eq_countP, ← numbered_pairs]
  congr 1
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

/-- The four arrays read by the pair visitor contain natural width and start
coordinates. Array heads are in words 1–4 of the visitor's public data. -/
structure Inputs {w : ℕ} (p : Fin 6 → Word w) (old new : List ℕ) (mem : Memory w) : Prop where
  oldStart : ∀ i, i < old.length → (mem ((p 1).val + i)).val = (old.take i).sum
  oldWidth : ∀ i (hi : i < old.length), (mem ((p 2).val + i)).val = old[i]
  newStart : ∀ j, j < new.length → (mem ((p 3).val + j)).val = (new.take j).sum
  newWidth : ∀ j (hj : j < new.length), (mem ((p 4).val + j)).val = new[j]

/-- All five physical arrays fit their word addresses. Only the frame array
is written during the pair pass. Input arrays may share other data. -/
structure FrameSpace {w : ℕ} (p : Fin 6 → Word w) (m n : ℕ) : Prop where
  targetCount : (p 0).val = n
  cursorFit : m * n < 2^w
  inputsFit : ∀ t : Fin 4, (p t.succ.castSucc).val + (if t.val < 2 then m else n) ≤ 2^w
  framesFit : (p 5).val + 3 * (m*n) ≤ 2^w
  apart : ∀ t : Fin 4, (p t.succ.castSucc).val + (if t.val < 2 then m else n) ≤ (p 5).val ∨
    (p 5).val + 3*(m*n) ≤ (p t.succ.castSucc).val

/-- Contents of all completed frames. The length word is overwritten even
on the empty branch so arbitrary stale output cannot be read as a record. -/
structure FramesAt {w : ℕ} (p : Fin 6 → Word w) (old new : List ℕ)
    (initial mem : Memory w) (k : ℕ) : Prop where
  inputs : Inputs p old new mem
  lengths : ∀ a, a < k → (mem ((p 5).val + 3*a + 2)).val = (sliceAt old new a).length
  offsets : ∀ a, a < k → 0 < (sliceAt old new a).length →
    (mem ((p 5).val + 3*a)).val = (sliceAt old new a).sourceOffset ∧
    (mem ((p 5).val + 3*a + 1)).val = (sliceAt old new a).targetOffset
  outside : ∀ x, x < (p 5).val ∨ (p 5).val + 3*k ≤ x → mem x = initial x

variable {w : ℕ}

/-- Physical writes of a frame, using the ordinary natural offsets of a
validated array. The two empty offsets can have arbitrary prior contents. -/
def writeFrame (m : Memory w) (a : ℕ) (s : CopySlice) : Memory w := fun x =>
  if x = a + 2 then Fin.ofNat _ s.length else if s.length = 0 then m x
  else if x = a then Fin.ofNat _ s.sourceOffset else if x = a + 1 then Fin.ofNat _ s.targetOffset
  else m x

private theorem frame_outside (m : Memory w) (a : ℕ) (s : CopySlice) (x : ℕ)
    (hx : x < a ∨ a + 3 ≤ x) : writeFrame m a s x = m x := by
  simp [writeFrame, show x ≠ a by omega, show x ≠ a+1 by omega, show x ≠ a+2 by omega]

private theorem field_bounds (ws : List ℕ) (i : ℕ) (hi : i < ws.length) :
    (fieldAt ws i).start + (fieldAt ws i).width ≤ ws.sum := by
  have h : fieldAt ws i ∈ fieldsFrom 0 0 ws := by
    rw [fields_eq_ofFn]
    exact List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩
  simpa using (fieldsFrom_bounds h).2.2.2

private theorem indices_lt {m n k : ℕ} (h : k < m*n) :
    k / n < m ∧ k % n < n := by
  have hn : 0 < n := by by_contra! hn; rw [show n = 0 by omega, Nat.mul_zero] at h; omega
  exact ⟨(Nat.div_lt_iff_lt_mul hn).mpr h, Nat.mod_lt k hn⟩

private theorem pair_bounds (old new : List ℕ) (k : ℕ) (hk : k < old.length * new.length) :
    let p := pairAt old new k
    p.1.start + p.1.width ≤ old.sum ∧ p.2.start + p.2.width ≤ new.sum :=
  ⟨field_bounds _ _ (indices_lt hk).1, field_bounds _ _ (indices_lt hk).2⟩

private theorem slice_fits (old new : List ℕ) (k : ℕ) (hk : k < old.length * new.length)
    (hs : old.sum < 2^w) (ht : new.sum < 2^w) :
    let s := sliceAt old new k
    s.sourceOffset < 2^w ∧ s.targetOffset < 2^w ∧ s.length < 2^w := by
  have hb := pair_bounds old new k hk
  dsimp only [sliceAt, copySlice]
  dsimp only at hb
  omega

private theorem frame_step {old new : List ℕ} {p : Fin 6 → Word w} {initial mem : Memory w}
    {k : ℕ} (reg : FrameSpace p old.length new.length) (hs : old.sum < 2^w)
    (ht : new.sum < 2^w) (hk : k < old.length * new.length) (h : FramesAt p old new initial mem k) :
    FramesAt p old new initial (writeFrame mem ((p 5).val + 3*k) (sliceAt old new k)) (k+1) := by
  let a := (p 5).val + 3*k
  let s := sliceAt old new k
  let post := writeFrame mem a s
  have sameInput (t : Fin 4) (i : ℕ) (hi : i < (if t.val < 2 then old.length else new.length)) :
      post ((p t.succ.castSucc).val + i) = mem ((p t.succ.castSucc).val + i) := by
    apply frame_outside
    have := reg.apart t
    dsimp only [a]
    omega
  obtain ⟨hf₀,hf₁,hf₂⟩ := slice_fits old new k hk hs ht
  constructor
  · constructor
    · intro i hi; exact (congrArg Fin.val (sameInput 0 i hi)).trans (h.inputs.oldStart i hi)
    · intro i hi; exact (congrArg Fin.val (sameInput 1 i hi)).trans (h.inputs.oldWidth i hi)
    · intro i hi; exact (congrArg Fin.val (sameInput 2 i hi)).trans (h.inputs.newStart i hi)
    · intro i hi; exact (congrArg Fin.val (sameInput 3 i hi)).trans (h.inputs.newWidth i hi)
  · intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [frame_outside _ _ _ _ (Or.inl (by omega)), h.lengths j hj]
    · simp [writeFrame, Fin.ofNat, Nat.mod_eq_of_lt hf₂]
  · intro j hj hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [frame_outside _ _ _ _ (Or.inl (by omega)), frame_outside _ _ _ _ (Or.inl (by omega))]
      exact h.offsets j hj hp
    · simp [writeFrame, hp.ne', Fin.ofNat, Nat.mod_eq_of_lt hf₀, Nat.mod_eq_of_lt hf₁]
  · intro x hx
    rw [frame_outside _ _ _ _ (by omega), h.outside x (by omega)]

open SliceRAM.IndexedPair

private theorem read_inputs {p : Fin 6 → Word w} {old new : List ℕ} {mem : Memory w}
    (reg : FrameSpace p old.length new.length) (h : Inputs p old new mem)
    (id : Word w) (hk : id.val < old.length * new.length) :
    let f := pairAt old new id.val
    (mem (p 1 + oldIndex p id).val).val = f.1.start ∧
    (mem (p 2 + oldIndex p id).val).val = f.1.width ∧
    (mem (p 3 + newIndex p id).val).val = f.2.start ∧
    (mem (p 4 + newIndex p id).val).val = f.2.width := by
  obtain ⟨hi,hj⟩ := indices_lt hk
  have hd : (oldIndex p id).val = id.val / new.length := by
    change (id.val / (p 0).val) % (2^w) = _
    rw [reg.targetCount, Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt id.isLt)]
  have hm : (newIndex p id).val = id.val % new.length := by
    change (id.val % (p 0).val) % (2^w) = _
    rw [reg.targetCount, Nat.mod_eq_of_lt ((Nat.mod_le _ _).trans_lt id.isLt)]
  have addr (t : Fin 4) (v : Word w)
      (hv : v.val < (if t.val < 2 then old.length else new.length)) :
      (p t.succ.castSucc + v).val = (p t.succ.castSucc).val + v.val := by
    have := reg.inputsFit t
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  have a₀ : (p 1 + oldIndex p id).val = (p 1).val + (oldIndex p id).val := addr 0 _ (hd ▸ hi)
  have a₁ : (p 2 + oldIndex p id).val = (p 2).val + (oldIndex p id).val := addr 1 _ (hd ▸ hi)
  have a₂ : (p 3 + newIndex p id).val = (p 3).val + (newIndex p id).val := addr 2 _ (hm ▸ hj)
  have a₃ : (p 4 + newIndex p id).val = (p 4).val + (newIndex p id).val := addr 3 _ (hm ▸ hj)
  rw [a₀, a₁, a₂, a₃]
  simp [hd, hm, pairAt, fieldAt, hi, hj, h.oldStart _ hi, h.oldWidth _ hi, h.newStart _ hj, h.newWidth _ hj]

private theorem after_indexed {p : Fin 6 → Word w} {old new : List ℕ}
    (reg : FrameSpace p old.length new.length) (mem : Memory w) (id : Word w)
    (hk : id.val < old.length * new.length) (s : CopySlice) :
    after mem (report p id mem s).events = writeFrame mem ((p 5).val + 3*id.val) s := by
  let a := (p 5).val + 3*id.val
  have hf := reg.framesFit
  have h1 : (1 : Word w).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by omega)]
  have hb : (base p id).val = a := base_val p id (by omega)
  have hb₁ : (base p id+1).val = a+1 := by
    rw [Fin.val_add, hb, h1, Nat.mod_eq_of_lt (by dsimp [a]; omega)]
  have hb₂ : (base p id+1+1).val = a+2 := by
    rw [Fin.val_add, hb₁, h1, Nat.mod_eq_of_lt (by dsimp [a]; omega)]
  rw [report_after]
  funext x
  by_cases hz : s.length = 0 <;> by_cases h₀ : x = a <;> by_cases h₁ : x = a + 1 <;>
    by_cases h₂ : x = a + 2 <;>
    simp [writeFrame, writeMemory, hb, hb₁, hb₂, ← show a = (p 5).val + 3*id.val from rfl,
      hz, h₀, h₁, h₂]

/-- A contiguous segment of actual pair calls carries the linear pair cursor
and writes every completed frame. The scan starts from arbitrary prior contents
of its unused output slots. -/
theorem frameSegment_run {p : Fin 6 → Word w} {old new : List ℕ}
    (reg : FrameSpace p old.length new.length) (hs : old.sum < 2^w) (ht : new.sum < 2^w)
    {initial mem : Memory w} {k : ℕ} (h : FramesAt p old new initial mem k)
    (t : ℕ) (htot : k+t ≤ old.length * new.length) :
    let M := table.instantiate w p
    let idx := Fin.ofNat (2^w)
    ∃ rs, runSegment M.program 38 (some (idx k)) mem (List.replicate t []) = some rs ∧
      FramesAt p old new initial (after mem (eventLog rs)) (k+t) ∧
      endState (some (idx k)) rs = some (idx (k+t)) ∧ rs.length = t ∧
      (rs.map Report.probes).sum = 5*t + 2*emitted old new k t ∧
      (rs.map fun r => r.events.length+1).sum = 34*t + 4*emitted old new k t := by
  let idx := Fin.ofNat (2^w)
  let M := table.instantiate w p
  induction t generalizing k mem with
  | zero => exact ⟨[],rfl,by simpa [after,eventLog] using h,rfl,rfl,by simp [emitted],by simp [emitted]⟩
  | succ t ih =>
    have hk : k < old.length * new.length := by omega
    have hv : (idx k).val = k := Nat.mod_eq_of_lt (hk.trans reg.cursorFit)
    have hn : idx k + 1 = idx (k+1) := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by have := reg.cursorFit; omega), hv]
      rfl
    obtain ⟨h₀,h₁,h₂,h₃⟩ := read_inputs reg h.inputs (idx k) (by simpa only [hv] using hk)
    rw [hv] at h₀ h₁ h₂ h₃
    have hb := pair_bounds old new k hk
    dsimp only at hb
    have hs' : slice p (idx k) mem = sliceAt old new k := by
      simp only [slice, h₀, h₁, h₂, h₃, sliceAt]
    have hvst := visit_native p (idx k) mem (by rw [h₀,h₁]; omega) (by rw [h₂,h₃]; omega)
    rw [hs'] at hvst
    let r := report p (idx k) mem (sliceAt old new k)
    have hnext := frame_step reg hs ht hk h
    have hm := after_indexed reg mem (idx k) (by simpa only [hv] using hk) (sliceAt old new k)
    rw [hv] at hm
    change after mem r.events = _ at hm
    obtain ⟨rs,hr,hf,he,hlen,hcost,hinst⟩ := ih (hm ▸ hnext) (by omega)
    have hresult : r.result = some (idx (k+1)) := congrArg some hn
    refine ⟨r::rs,?_,?_,?_,by simp [hlen],?_,?_⟩
    · change runSegment M.program 38 (some (idx k)) mem (List.replicate (t+1) []) = _
      rw [List.replicate_succ, runSegment, hvst]
      change (runSegment M.program 38 r.result (after mem r.events) (List.replicate t [])).map _ = _
      rw [hresult,hr]; rfl
    · have hl : after mem (eventLog (r :: rs)) = after (after mem r.events) (eventLog rs) := by
        change List.foldl BurstRAM.update mem (r.events ++ eventLog rs) = _
        rw [List.foldl_append]; rfl
      simpa only [hl, show k+(t+1)=k+1+t by omega] using hf
    · change endState r.result rs = _
      rw [hresult, he, show k+1+t = k+(t+1) by omega]
    · have hc := (report_cost p (idx k) mem (sliceAt old new k)).1
      change r.probes = _ at hc
      simp only [List.map_cons, List.sum_cons, hcost, hc, emitted_succ]
      split <;> omega
    · have hc := (report_cost p (idx k) mem (sliceAt old new k)).2
      change r.events.length + 1 = _ at hc
      simp only [List.map_cons, List.sum_cons, hinst, hc, emitted_succ]
      split <;> omega

open SliceRAM

/-- First frame after the two totals, the incidence counts and the prefix arrays. -/
def frameHead (B m n : ℕ) := B + 2 + 2*m + 2*n

/-- Last exclusive workspace address. Each pair reserves three frame cells
and one reference slot in each of the two endpoint directories. -/
def stop (B m n : ℕ) := frameHead B m n + 5*(m*n)

/-- Address bounds and separation of the slice workspace from both input width arrays. -/
structure Workspace (oldBase newBase B : Word w) (m n : ℕ) : Prop where
  fits : stop B.val m n < 2^w
  oldFit : oldBase.val + m ≤ 2^w
  newFit : newBase.val + n ≤ 2^w
  oldApart : oldBase.val + m ≤ B.val ∨ stop B.val m n ≤ oldBase.val
  newApart : newBase.val + n ≤ B.val ∨ stop B.val m n ≤ newBase.val

private def pairNumbers (o t B m n : ℕ) : Fin 6 → ℕ :=
  ![n, B+2+m+n, o, B+2+2*m+n, t, frameHead B m n]

/-- Pair worker public data. -/
def pairData (oldBase newBase B : Word w) (m n : ℕ) : Fin 6 → Word w :=
  fun i => Fin.ofNat _ (pairNumbers oldBase.val newBase.val B.val m n i)

private def adjNumbers (B m n : ℕ) : Fin 7 → ℕ :=
  let a := frameHead B m n
  ![n, m, a, B+2, a+3*(m*n), B+2+m, a+4*(m*n)]

/-- Endpoint-directory worker public data. -/
def adjacencyData (B : Word w) (m n : ℕ) : Fin 7 → Word w :=
  fun i => Fin.ofNat _ (adjNumbers B.val m n i)

variable {o t B : Word w} {m n : ℕ}

private theorem pair_val (h : Workspace o t B m n) (i : Fin 6) :
    (pairData o t B m n i).val = pairNumbers o.val t.val B.val m n i := by
  apply Nat.mod_eq_of_lt
  have hfit := h.fits
  dsimp only [stop, frameHead] at hfit
  fin_cases i <;> dsimp [pairNumbers,frameHead] <;> first | exact o.isLt | exact t.isLt | omega

private theorem adj_val (h : Workspace o t B m n) (i : Fin 7) :
    (adjacencyData B m n i).val = adjNumbers B.val m n i := by
  apply Nat.mod_eq_of_lt
  have hfit := h.fits
  dsimp only [stop,frameHead] at hfit
  fin_cases i <;> dsimp [adjNumbers,frameHead] <;> omega

private theorem prepSpace (h : Workspace o t B m n) : PreparationRegions o t B m n := by
  obtain ⟨hf,ho,ht,hao,hat⟩ := h
  dsimp [stop,frameHead] at *
  exact ⟨ho,ht,by omega,by omega,by omega⟩

private theorem pairSpace (h : Workspace o t B m n) : FrameSpace (pairData o t B m n) m n := by
  have hf := h.fits
  have hao := h.oldApart
  have hat := h.newApart
  dsimp only [stop,frameHead] at hf hao hat
  constructor
  · exact pair_val h 0
  · omega
  · intro i
    rw [pair_val h]
    fin_cases i <;> dsimp [pairNumbers] <;> first | exact h.oldFit | exact h.newFit | omega
  · rw [pair_val h]; dsimp [pairNumbers,frameHead]; omega
  · intro i
    simp only [pair_val h]
    fin_cases i <;> dsimp [pairNumbers,frameHead] <;> omega

private theorem directorySpace (h : Workspace o t B m n) : AdjRegions (adjacencyData B m n) := by
  have hf := h.fits
  dsimp only [stop,frameHead] at hf
  constructor <;> simp only [oldBank,newBank,AdjBank.stop,adj_val h] <;>
    dsimp [adjNumbers,frameHead] <;> (try rw [Nat.mul_comm n m]) <;> omega

private theorem prepInputs {old new : List ℕ} {initial mem : Memory w}
    (h : Workspace o t B old.length new.length) (hp : Prepared o t B old new initial mem) :
    Inputs (pairData o t B old.length new.length) old new mem := by
  constructor <;> intro i hi <;> rw [pair_val h]
  · exact hp.oldStarts i hi
  · exact hp.oldWidths i hi
  · exact hp.newStarts i hi
  · exact hp.newWidths i hi

private theorem nonempty_eq_emitted (old new : List ℕ) (k t : ℕ) :
    adjNonempty (fun j => (sliceAt old new j).length) k t = emitted old new k t := by
  rw [adjNonempty, ← List.countP_eq_length_filter, emitted, List.countP_map]
  congr 1
  funext j
  dsimp only [Function.comp_apply, intersectFields, sliceAt]
  split <;> simp [*]

/-- Reports from the five rows of the local descriptor schedule. -/
structure Passes (w : ℕ) where
  /-- Reports for zeroing the two totals and both endpoint count arrays. -/
  clear : List (Report w)
  /-- Reports for computing the starts of the old fields from their widths. -/
  oldPrefix : List (Report w)
  /-- Reports for computing the starts of the new fields from their widths. -/
  newPrefix : List (Report w)
  /-- Reports from testing the field pairs and storing their interval offsets and lengths. -/
  frames : List (Report w)
  /-- Reports from indexing nonempty pair frames in both endpoint directories. -/
  directories : List (Report w)

/-- Memory after clearing and computing both arrays of field starts. -/
def Passes.prepared (rs : Passes w) (mem : Memory w) :=
  preparationAfter mem rs.clear rs.oldPrefix rs.newPrefix

/-- Memory after the pair scan writes its frames into the prepared workspace. -/
def Passes.tested (rs : Passes w) (mem : Memory w) :=
  after (rs.prepared mem) (eventLog rs.frames)

/-- Memory after both endpoint directories have been populated from the tested frames. -/
def Passes.result (rs : Passes w) (mem : Memory w) :=
  after (rs.tested mem) (eventLog rs.directories)

/-- Reports of all five sweeps in execution order. -/
def Passes.all (rs : Passes w) :=
  (rs.clear ++ rs.oldPrefix ++ rs.newPrefix) ++ rs.frames ++ rs.directories

/-- The five reset-cursor segments of the fixed worker schedule, in chronological order. -/
structure NativePasses (o t B : Word w) (m n : ℕ) (mem : Memory w) (rs : Passes w) : Prop where
  preparation : PreparationRuns o t B m n mem rs.clear rs.oldPrefix rs.newPrefix
  pairs : runSegment (table.instantiate w (pairData o t B m n)).program 38 (some 0)
    (rs.prepared mem) (List.replicate (m*n) []) = some rs.frames
  adjacency : runSegment (adjTemplate.instantiate w (adjacencyData B m n)).program 36 (some 0)
    (rs.tested mem) (List.replicate (m*n) []) = some rs.directories

/-- The final table stores the three words for each nonempty pair and its
identifier in both compact incidence lists. Each list occupies the live prefix
of its bounded row, in the order of the candidate scan. -/
structure Stored (B : Word w) (old new : List ℕ) (initial mem : Memory w) : Prop where
  oldStarts : ∀ i, i < old.length →
    (mem (B.val+2+old.length+new.length+i)).val = (old.take i).sum
  newStarts : ∀ j, j < new.length →
    (mem (B.val+2+2*old.length+new.length+j)).val = (new.take j).sum
  lengths : ∀ k, k < old.length*new.length →
    (mem (frameHead B.val old.length new.length + 3*k + 2)).val = (sliceAt old new k).length
  offsets : ∀ k, k < old.length*new.length → 0 < (sliceAt old new k).length →
    (mem (frameHead B.val old.length new.length + 3*k)).val = (sliceAt old new k).sourceOffset ∧
    (mem (frameHead B.val old.length new.length + 3*k+1)).val = (sliceAt old new k).targetOffset
  oldRows : (oldBank (adjacencyData B old.length new.length)).Represents mem
    (fun k => (sliceAt old new k).length) (· / new.length) (old.length*new.length)
  newRows : (newBank (adjacencyData B old.length new.length)).Represents mem
    (fun k => (sliceAt old new k).length) (· % new.length) (old.length*new.length)
  outside : ∀ x, x < B.val ∨ stop B.val old.length new.length ≤ x → mem x = initial x

/-- Following a reference in the live portion of an endpoint row. -/
def References (bank : AdjBank w) (mem : Memory w) (owner id : Word w) : Prop :=
  ∃ j < (mem (bank.count owner).val).val, mem ((bank.row owner).val + j) = id

private theorem references_iff {bank : AdjBank w} {mem : Memory w} {len owner : ℕ → ℕ}
    {k : ℕ} (h : bank.Represents mem len owner k) (fit : k ≤ 2^w)
    (v id : Word w) (hv : v < bank.size) :
    References bank mem v id ↔ id.val < k ∧ len id.val ≠ 0 ∧ owner id.val = v.val := by
  let row := adjPrefix w len owner v.val k
  obtain ⟨hcount, hslots⟩ := h v hv
  change (mem (bank.count v).val).val = row.length at hcount
  have inRow : References bank mem v id ↔ id ∈ row := by
    constructor
    · rintro ⟨j,hj,he⟩
      have hpos : j < row.length := hcount ▸ hj
      exact List.mem_iff_getElem.mpr ⟨j,hpos,(hslots ⟨j,hpos⟩).symm.trans he⟩
    · intro hr
      obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hr
      exact ⟨j,hcount.symm ▸ hj,(hslots ⟨j,hj⟩).trans he⟩
  rw [inRow]
  simp only [row, adjPrefix, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨j,⟨hj,hz,hv'⟩,he⟩
    have hj' : j = id.val := (Nat.mod_eq_of_lt (hj.trans_le fit)).symm.trans (congrArg Fin.val he)
    exact hj' ▸ ⟨hj,hz,hv'⟩
  · rintro ⟨hk,hz,hv'⟩
    exact ⟨id.val, ⟨hk,hz,hv'⟩, Fin.ext (Nat.mod_eq_of_lt id.isLt)⟩

/-- A source or target's physical row contains exactly the positive-length
frames incident to that field. Dividing the returned ID by the target count
recovers the source, and its remainder recovers the target. -/
theorem Stored.references {old new : List ℕ} {initial mem : Memory w}
    (space : Workspace o t B old.length new.length) (h : Stored B old new initial mem)
    (i j id : Word w) (hi : i.val < old.length) (hj : j.val < new.length) :
    let d := adjacencyData B old.length new.length
    let live := id.val < old.length*new.length ∧ (sliceAt old new id.val).length ≠ 0
    (References (oldBank d) mem i id ↔ live ∧ id.val / new.length = i.val) ∧
      (References (newBank d) mem j id ↔ live ∧ id.val % new.length = j.val) := by
  let d := adjacencyData B old.length new.length
  have hi' : i < (oldBank d).size := by
    change i.val < (d 1).val
    rw [adj_val space]; exact hi
  have hj' : j < (newBank d).size := by
    change j.val < (d 0).val
    rw [adj_val space]; exact hj
  have fit := (pairSpace space).cursorFit.le
  exact ⟨(references_iff h.oldRows fit i id hi').trans and_assoc.symm,
    (references_iff h.newRows fit j id hj').trans and_assoc.symm⟩

private theorem directory_outside {p : Fin 7 → Word w} (hp : p = adjacencyData B m n)
    (space : Workspace o t B m n) (x : ℕ) (hx : x < B.val ∨ stop B.val m n ≤ x) :
    ¬ (oldBank p).Inside x ∧ ¬ (newBank p).Inside x := by
  subst p
  simp only [oldBank, newBank, AdjBank.Inside, AdjBank.stop, adj_val space]
  dsimp [adjNumbers,frameHead]
  dsimp [stop,frameHead] at hx
  rw [Nat.mul_comm n m]
  omega

private theorem directory_skips_starts (space : Workspace o t B m n) (x : ℕ)
    (hl : B.val+2+m+n ≤ x) (hu : x < frameHead B.val m n) :
    ¬ (oldBank (adjacencyData B m n)).Inside x ∧ ¬ (newBank (adjacencyData B m n)).Inside x := by
  simp only [oldBank,newBank,AdjBank.Inside,AdjBank.stop,adj_val space]
  dsimp [adjNumbers,frameHead]
  dsimp [frameHead] at hu
  omega

/-- Build the interval records and both of their endpoint directories
directly from the two width arrays. All scratch words may initially be stale.
The exact totals include address preparation, the intersection tests, and the
writes that compact both endpoint lists. -/
theorem build (old new : List ℕ) (o t B : Word w) (mem : Memory w)
    (space : Workspace o t B old.length new.length)
    (ho : old.sum < 2^w) (hn : new.sum < 2^w)
    (oldWidths : ∀ i (hi : i < old.length), (mem (o.val+i)).val = old[i])
    (newWidths : ∀ j (hj : j < new.length), (mem (t.val+j)).val = new[j]) :
    let m := old.length
    let n := new.length
    let k := (copyRecords old new).length
    ∃ rs : Passes w, NativePasses o t B m n mem rs ∧ Stored B old new mem (rs.result mem) ∧
      rs.all.length = 2 + 2*(m+n) + 2*(m*n) ∧
      (rs.all.map Report.probes).sum = 2 + 5*(m+n) + 6*(m*n) + 8*k ∧
      (rs.all.map fun r => r.events.length + 1).sum = 16 + 22*(m+n) + 46*(m*n) + 28*k := by
  let m := old.length
  let n := new.length
  let p := pairData o t B m n
  let q := adjacencyData B m n
  let a := frameHead B.val m n
  let len := fun k => (sliceAt old new k).length
  have hp₅ : (p 5).val = a := pair_val space 5
  have hq₀ : (q 0).val = n := adj_val space 0
  have hq₁ : (q 1).val = m := adj_val space 1
  have hq₂ : (q 2).val = a := adj_val space 2
  have hq₃ : (q 3).val = B.val+2 := adj_val space 3
  have hq₅ : (q 5).val = B.val+2+m := adj_val space 5
  obtain ⟨clear, oldRun, newRun, hpre, hd⟩ :=
    preparation_run (prepSpace space) ho hn oldWidths newWidths
  let pre := preparationAfter mem clear oldRun newRun
  have h0 : FramesAt p old new pre pre 0 :=
    ⟨prepInputs space hd, fun _ hj => by omega, fun _ hj => by omega, fun _ _ => rfl⟩
  obtain ⟨ps,hps,hf,_,hplen,hpc,hpi⟩ := frameSegment_run (pairSpace space) ho hn h0 (m*n) (by simp [m,n])
  simp only [Nat.zero_add] at hf
  let fr := after pre (eventLog ps)
  change FramesAt p old new pre fr (m*n) at hf
  have lengths (k : ℕ) (hk : k < (q 1).val*(q 0).val) :
      (fr ((q 2).val + 3*k+2)).val = len k := by
    rw [hq₁,hq₀] at hk
    rw [hq₂, ← hp₅]
    exact hf.lengths k hk
  have hfit := space.fits
  change a + 5*(m*n) < 2^w at hfit
  have oldZero (i : Word w) (hi : i < q 1) : fr (adjOldCount q i).val = 0 := by
    have hv : i.val < m := hq₁ ▸ Fin.lt_def.mp hi
    have haddr : (adjOldCount q i).val = B.val + 2 + i.val := by
      rw [adjOldCount, Fin.val_add, hq₃, Nat.mod_eq_of_lt (by dsimp [a,frameHead] at hfit; omega)]
    rw [haddr, hf.outside _ (Or.inl (by rw [hp₅]; dsimp [a,frameHead]; omega))]
    exact hd.oldCounts i.val hv
  have newZero (j : Word w) (hj : j < q 0) : fr (adjNewCount q j).val = 0 := by
    have hv : j.val < n := hq₀ ▸ Fin.lt_def.mp hj
    have haddr : (adjNewCount q j).val = B.val+2+m+j.val := by
      rw [adjNewCount, Fin.val_add, hq₅, Nat.mod_eq_of_lt (by dsimp [a,frameHead] at hfit; omega)]
    rw [haddr, hf.outside _ (Or.inl (by rw [hp₅]; dsimp [a,frameHead]; omega))]
    exact hd.newCounts j.val hv
  have sq := directorySpace space
  obtain ⟨ds,hds,hdir,_,hdlen,hdc,hdi⟩ := adjPass_run sq lengths oldZero newZero
  rw [hq₁,hq₀] at hds hdir hdlen hdc hdi
  let post := after fr (eventLog ds)
  change AdjAt q len fr post (m*n) at hdir
  have preserve (x : ℕ) (hl : a ≤ x) (hu : x < a+3*(m*n)) : post x = fr x :=
    hdir.frame_eq sq (hq₂ ▸ hl) (by rw [hq₁,hq₀,hq₂]; exact hu)
  let rs : Passes w := ⟨clear,oldRun,newRun,ps,ds⟩
  refine ⟨rs, ⟨hpre,hps,hds⟩, ?_, ?_, ?_, ?_⟩
  · have sameStart (x : ℕ) (hl : B.val+2+m+n ≤ x) (hu : x < a) : post x = pre x := by
      obtain ⟨hox,hnx⟩ := directory_skips_starts space x hl hu
      exact (hdir.outside x hox hnx).trans (hf.outside x (Or.inl (hp₅ ▸ hu)))
    constructor
    · intro i hi
      change i < m at hi
      change (post (B.val+2+m+n+i)).val = _
      rw [sameStart _ (by omega) (by dsimp [a,frameHead]; omega)]
      exact hd.oldStarts i hi
    · intro j hj
      change j < n at hj
      change (post (B.val+2+2*m+n+j)).val = _
      rw [sameStart _ (by omega) (by dsimp [a,frameHead]; omega)]
      exact hd.newStarts j hj
    · intro k hk
      change k < m*n at hk
      change (post (a+3*k+2)).val = _
      rw [preserve _ (by omega) (by omega), ← hp₅]
      exact hf.lengths k hk
    · intro k hk hpos
      change k < m*n at hk
      change (post (a+3*k)).val = _ ∧ (post (a+3*k+1)).val = _
      rw [preserve _ (by omega) (by omega), preserve _ (by omega) (by omega), ← hp₅]
      exact hf.offsets k hk hpos
    · have h := hdir.oldRows
      rw [hq₀] at h
      exact h
    · have h := hdir.newRows
      rw [hq₀] at h
      exact h
    · intro x hx
      obtain ⟨hox,hnx⟩ := directory_outside (p := q) rfl space x hx
      change post x = mem x
      change x < B.val ∨ a + 5*(m*n) ≤ x at hx
      rw [hdir.outside x hox hnx, hf.outside x (by rw [hp₅]; dsimp [a,frameHead] at *; omega)]
      exact hd.outside x (by dsimp [a,frameHead] at hx; omega)
  · have hc := hpre.clearLength
    have hh := hpre.oldLength
    have hj := hpre.newLength
    simp only [rs, Passes.all, List.length_append]
    dsimp only [m,n] at *
    omega
  · rw [adjCost_eq_length_add_probes] at hdc
    have hk : adjNonempty len 0 (m*n) = (copyRecords old new).length :=
      (nonempty_eq_emitted old new 0 (m*n)).trans (emitted_all old new)
    rw [hk] at hdc
    rw [show emitted old new 0 (m*n) = _ from emitted_all old new] at hpc
    change (((clear ++ oldRun ++ newRun) ++ ps ++ ds).map Report.probes).sum = _
    rw [List.map_append, List.sum_append, List.map_append, List.sum_append, hpre.probes]
    dsimp only [m,n] at *
    omega
  · have hk : adjNonempty len 0 (m*n) = (copyRecords old new).length :=
      (nonempty_eq_emitted old new 0 (m*n)).trans (emitted_all old new)
    rw [hk] at hdi
    rw [show emitted old new 0 (m*n) = _ from emitted_all old new] at hpi
    change (((clear ++ oldRun ++ newRun) ++ ps ++ ds).map fun r => r.events.length+1).sum = _
    rw [List.map_append, List.sum_append, List.map_append, List.sum_append, hpre.instructions]
    dsimp only [m,n] at *
    omega

end CompressorRecords.SliceSchedule

end VPVNP
end Computability
end OAI
