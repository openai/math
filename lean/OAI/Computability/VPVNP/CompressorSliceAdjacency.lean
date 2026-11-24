import OAI.Computability.VPVNP.CompressorSliceAdjacencyNative
import OAI.Computability.VPVNP.CompressorSliceAdjacencyRows
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMBuckets

/-!
# Native construction of both endpoint directories for copy slices

Scan the rectangular output frames of Appendix E in row-major order. A nonempty
frame appends its identifier to the row for its source and the row for its
target. The stored counts delimit the meaningful portions of both directories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SliceRAM

open BurstRAM BurstRAM.PrivateRAM

variable {w : ℕ}

/-- Source-field adjacency directory, with one row per old field and one slot per new field. -/
def oldBank (pub : Fin 7 → Word w) : AdjBank w := ⟨pub 3, pub 4, pub 1, pub 0⟩
/-- Target-field adjacency directory, with one row per new field and one slot per old field. -/
def newBank (pub : Fin 7 → Word w) : AdjBank w := ⟨pub 5, pub 6, pub 0, pub 1⟩

/-- Counters precede the raw frames, which precede both reference arrays.
The inequalities allow gaps between arrays. -/
structure AdjRegions (pub : Fin 7 → Word w) : Prop where
  oldBeforeNewCounts : (pub 3).val + (pub 1).val ≤ (pub 5).val
  countsBeforeFrames : (pub 5).val + (pub 0).val ≤ (pub 2).val
  framesBeforeRefs : (pub 2).val + 3 * ((pub 1).val * (pub 0).val) ≤ (pub 4).val
  oldBeforeNewRefs : (oldBank pub).stop ≤ (pub 6).val
  refsFit : (newBank pub).stop ≤ 2^w

private theorem oldFits {pub : Fin 7 → Word w} (a : AdjRegions pub) : (oldBank pub).Fits := by
  have := a.oldBeforeNewCounts
  have := a.countsBeforeFrames
  have := a.framesBeforeRefs
  exact ⟨by change (pub 3).val + (pub 1).val ≤ (pub 4).val; omega,
    a.oldBeforeNewRefs.trans (pub 6).isLt.le⟩

private theorem newFits {pub : Fin 7 → Word w} (a : AdjRegions pub) : (newBank pub).Fits := by
  have := a.countsBeforeFrames
  have := a.framesBeforeRefs
  have ht := a.oldBeforeNewRefs
  change (pub 4).val + (pub 1).val * (pub 0).val ≤ (pub 6).val at ht
  exact ⟨by change (pub 5).val + (pub 0).val ≤ (pub 6).val; omega, a.refsFit⟩

private theorem banks_disjoint {pub : Fin 7 → Word w} (a : AdjRegions pub) (x : ℕ)
    (ho : (oldBank pub).Inside x) (hn : (newBank pub).Inside x) : False := by
  have := a.oldBeforeNewCounts
  have := a.countsBeforeFrames
  have := a.framesBeforeRefs
  have h := a.oldBeforeNewRefs
  simp only [oldBank, newBank, AdjBank.Inside, AdjBank.stop] at ho hn h
  omega

/-- Both directories represent the same prefix of the scan. -/
structure AdjAt (pub : Fin 7 → Word w) (length : ℕ → ℕ) (initial mem : Memory w) (k : ℕ) : Prop where
  oldRows : (oldBank pub).Represents mem length (· / (pub 0).val) k
  newRows : (newBank pub).Represents mem length (· % (pub 0).val) k
  outside : ∀ x, ¬ (oldBank pub).Inside x → ¬ (newBank pub).Inside x → mem x = initial x

/-- Every frame word retains its offsets or length throughout the adjacency pass. -/
theorem AdjAt.frame_eq {pub : Fin 7 → Word w} (bounds : AdjRegions pub)
    {length : ℕ → ℕ} {initial mem : Memory w} {k : ℕ} (h : AdjAt pub length initial mem k)
    {x : ℕ} (lo : (pub 2).val ≤ x) (hi : x < (pub 2).val + 3*((pub 1).val*(pub 0).val)) :
    mem x = initial x := by
  have := bounds.framesBeforeRefs
  have := bounds.countsBeforeFrames
  have := bounds.oldBeforeNewCounts
  have ho := bounds.oldBeforeNewRefs
  change (pub 4).val + (pub 1).val * (pub 0).val ≤ (pub 6).val at ho
  exact h.outside x (by simp only [oldBank, AdjBank.Inside]; omega)
    (by simp only [newBank, AdjBank.Inside]; omega)

theorem adjFrameLength_val {pub : Fin 7 → Word w} (bounds : AdjRegions pub)
    {id : Word w} (hk : id.val < (pub 1).val * (pub 0).val) :
    (adjFrameLength pub id).val = (pub 2).val + 3 * id.val + 2 := by
  have hfit := bounds.framesBeforeRefs
  have hlt := (pub 4).isLt
  have h3 : (3 : Word w).val = 3 := by
    change 3 % (2^w) = 3
    exact Nat.mod_eq_of_lt (by omega)
  have h2 : (2 : Word w).val = 2 := by
    change 2 % (2^w) = 2
    exact Nat.mod_eq_of_lt (by omega)
  rw [adjFrameLength, Fin.val_add, Fin.val_add, Fin.val_mul, h3, h2,
    Nat.mod_eq_of_lt (show 3 * id.val < 2^w by omega),
    Nat.mod_eq_of_lt (show (pub 2).val + 3*id.val < 2^w by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem current_length {pub : Fin 7 → Word w} (bounds : AdjRegions pub)
    {length : ℕ → ℕ} {initial mem : Memory w}
    (frames : ∀ t, t < (pub 1).val * (pub 0).val → (initial ((pub 2).val + 3*t+2)).val = length t)
    {id : Word w} (hk : id.val < (pub 1).val * (pub 0).val) (h : AdjAt pub length initial mem id.val) :
    (mem (adjFrameLength pub id).val).val = length id.val := by
  rw [adjFrameLength_val bounds hk, h.frame_eq bounds (by omega) (by omega)]
  exact frames _ hk

private theorem adjAt_step {pub : Fin 7 → Word w} (bounds : AdjRegions pub)
    {length : ℕ → ℕ} {initial mem : Memory w}
    (frames : ∀ t, t < (pub 1).val * (pub 0).val → (initial ((pub 2).val + 3*t+2)).val = length t)
    {id : Word w} (hk : id.val < (pub 1).val * (pub 0).val) (h : AdjAt pub length initial mem id.val) :
    AdjAt pub length initial (adjUpdate pub mem id) (id.val+1) := by
  have hlen := current_length bounds frames hk h
  have hzero : mem (adjFrameLength pub id).val = 0 ↔ length id.val = 0 := by
    rw [← hlen]
    exact ⟨fun he => by simp [he], fun h => Fin.ext (by simpa using h)⟩
  by_cases hz : length id.val = 0
  · rw [adjUpdate, ite_eq_left (hzero.mpr hz)]
    exact ⟨fun v hv => by simpa [adjPrefix_succ, hz] using h.oldRows v hv,
      fun v hv => by simpa [adjPrefix_succ, hz] using h.newRows v hv, h.outside⟩
  rw [adjUpdate, ite_eq_right (mt hzero.mp hz)]
  let i := id / pub 0
  let j := id % pub 0
  let O := oldBank pub
  let N := newBank pub
  have hn : 0 < (pub 0).val := by
    by_contra! he
    rw [show (pub 0).val = 0 by omega, Nat.mul_zero] at hk
    omega
  have hi : i < O.size := (Nat.div_lt_iff_lt_mul hn).mpr hk
  have hj : j < N.size := Nat.mod_lt _ hn
  have hid : id = Fin.ofNat (2^w) id.val := Fin.ext (Nat.mod_eq_of_lt id.isLt).symm
  have ocap (k : ℕ) (hbound : k ≤ (pub 1).val * (pub 0).val) (v : Word w) :
      (adjPrefix w length (· / (pub 0).val) v.val k).length ≤ O.cap.val :=
    adjPrefix_old_le length hbound
  have ncap (k : ℕ) (hbound : k ≤ (pub 1).val * (pub 0).val) (v : Word w) :
      (adjPrefix w length (· % (pub 0).val) v.val k).length ≤ N.cap.val :=
    adjPrefix_new_le length hbound
  let middle := adjAppend mem (O.count i) (O.row i) id
  obtain ⟨ho, hmo⟩ := AdjBank.append_step (oldFits bounds) h.oldRows hi rfl hid hz
    (fun v _ => ocap _ hk v)
  change O.Represents middle length (· / (pub 0).val) (id.val+1) at ho
  change ∀ x, ¬ O.Inside x → middle x = mem x at hmo
  have hnRows : N.Represents middle length (· % (pub 0).val) id.val :=
    AdjBank.represents_congr (newFits bounds) h.newRows (fun v _ => ncap _ hk.le v)
      (fun x hx => hmo x (fun ho => banks_disjoint bounds x ho hx))
  obtain ⟨hn', hmn⟩ := AdjBank.append_step (newFits bounds) hnRows hj rfl hid hz
    (fun v _ => ncap _ hk v)
  exact ⟨AdjBank.represents_congr (oldFits bounds) ho (fun v _ => ocap _ hk v)
      (fun x hx => hmn x (banks_disjoint bounds x hx)), hn',
    fun x xo xn => (hmn x xn).trans ((hmo x xo).trans (h.outside x xo xn))⟩

/-- Number of nonempty frames in a contiguous part of the scan. -/
def adjNonempty (length : ℕ → ℕ) (k steps : ℕ) : ℕ :=
  ((List.range' k steps).filter fun t => length t ≠ 0).length

private theorem adjNonempty_succ (length : ℕ → ℕ) (k steps : ℕ) :
    adjNonempty length k (steps+1) = (if length k = 0 then 0 else 1) +
      adjNonempty length (k+1) steps := by
  by_cases hz : length k = 0 <;> simp [adjNonempty, List.range'_succ, hz, Nat.add_comm]

/-- A segment of the native program visits all consecutive identifiers starting at `k`.
The total cost counts calls and probes, and the instruction total counts each return. -/
theorem adjSegment_run {pub : Fin 7 → Word w} (bounds : AdjRegions pub)
    {length : ℕ → ℕ} {initial mem : Memory w}
    (frames : ∀ t, t < (pub 1).val * (pub 0).val → (initial ((pub 2).val + 3*t+2)).val = length t)
    {k : ℕ} (h : AdjAt pub length initial mem k) (steps : ℕ)
    (hb : k + steps ≤ (pub 1).val * (pub 0).val) :
    let M := adjTemplate.instantiate w pub
    let idx := Fin.ofNat (2^w)
    ∃ rs, runSegment M.program 36 (some (idx k)) mem (List.replicate steps []) = some rs ∧
      AdjAt pub length initial (after mem (eventLog rs)) (k + steps) ∧
      endState (some (idx k)) rs = some (idx (k+steps)) ∧ rs.length = steps ∧
      RAMBuckets.cost Report.probes rs = 2*steps + 6*adjNonempty length k steps ∧
      (rs.map fun r => r.events.length + 1).sum = 12*steps + 24*adjNonempty length k steps := by
  let M := adjTemplate.instantiate w pub
  let idx := Fin.ofNat (2^w)
  have hfit := bounds.framesBeforeRefs
  have hspace := (pub 4).isLt
  induction steps generalizing k mem with
  | zero => exact ⟨[], rfl, h, rfl, rfl, by simp [RAMBuckets.cost, adjNonempty],
      by simp [adjNonempty]⟩
  | succ s ih =>
    have hi : (idx k).val = k := Nat.mod_eq_of_lt (by omega)
    have hnext : idx k + 1 = idx (k+1) := by
      apply Fin.ext
      rw [Fin.val_add, hi, Fin.val_one', Nat.mod_eq_of_lt (show 1 < 2^w by omega)]
      rfl
    let r : Report w := ⟨adjEvents pub mem (idx k), some (idx k + 1)⟩
    have hlen := current_length bounds frames (id := idx k) (by omega) (hi ▸ h)
    rw [hi] at hlen
    have hzero : mem (adjFrameLength pub (idx k)).val = 0 ↔ length k = 0 := by
      rw [← hlen]
      exact ⟨fun he => by simp [he], fun h => Fin.ext (by simpa using h)⟩
    have hp := adjAt_step bounds frames (id := idx k) (by omega) (hi ▸ h)
    rw [hi] at hp
    obtain ⟨rs, hr, hp', he, hl, hc, hw⟩ := ih hp (by omega)
    have ha : k + (s+1) = k+1+s := by omega
    refine ⟨r :: rs, ?_, ?_, ?_, by simp [hl], ?_, ?_⟩
    · change runSegment M.program 36 (some (idx k)) mem (List.replicate (s+1) []) = _
      rw [List.replicate_succ, runSegment, adjVisit_native]
      simp only [hnext, adjEvents_after]
      rw [hr]
      simp only [Option.map_some, r, hnext]
    · have hm : after mem (eventLog (r :: rs)) =
          after (adjUpdate pub mem (idx k)) (eventLog rs) := by
        change List.foldl update mem (r.events ++ eventLog rs) = _
        rw [List.foldl_append]
        change after (after mem (adjEvents pub mem (idx k))) (eventLog rs) = _
        rw [adjEvents_after]
      rw [hm, ha]
      exact hp'
    · change endState (some (idx k + 1)) rs = _
      rw [hnext, he, ha]
    · have hp := (adjEvents_work pub mem (idx k)).1
      change r.probes = _ at hp
      rw [RAMBuckets.cost, hp, hc, adjNonempty_succ]
      by_cases hz : length k = 0 <;> simp [hzero, hz] <;> omega
    · have hp := (adjEvents_work pub mem (idx k)).2
      change r.events.length + 1 = _ at hp
      rw [List.map_cons, List.sum_cons, hp, hw, adjNonempty_succ]
      by_cases hz : length k = 0 <;> simp [hzero, hz] <;> omega

/-- Splitting the reported segment cost into its call and probe totals. -/
theorem adjCost_eq_length_add_probes (rs : List (Report w)) :
    RAMBuckets.cost Report.probes rs = rs.length + (rs.map Report.probes).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [RAMBuckets.cost, ih]; omega

/-- Starting with zero counts, the scan constructs every row at both endpoints.
Empty frames and zero-dimensional tables produce no incidences. -/
theorem adjPass_run {pub : Fin 7 → Word w} (bounds : AdjRegions pub)
    {length : ℕ → ℕ} {mem : Memory w}
    (frames : ∀ t, t < (pub 1).val * (pub 0).val → (mem ((pub 2).val + 3*t+2)).val = length t)
    (oldZero : ∀ i : Word w, i < pub 1 → mem (adjOldCount pub i).val = 0)
    (newZero : ∀ j : Word w, j < pub 0 → mem (adjNewCount pub j).val = 0) :
    let pairs := (pub 1).val * (pub 0).val
    let M := adjTemplate.instantiate w pub
    ∃ rs, runSegment M.program 36 (some 0) mem (List.replicate pairs []) = some rs ∧
      AdjAt pub length mem (after mem (eventLog rs)) pairs ∧
      endState (some 0) rs = some (Fin.ofNat (2^w) pairs) ∧ rs.length = pairs ∧
      RAMBuckets.cost Report.probes rs = 2*pairs + 6*adjNonempty length 0 pairs ∧
      (rs.map fun r => r.events.length + 1).sum = 12*pairs + 24*adjNonempty length 0 pairs := by
  have h : AdjAt pub length mem mem 0 := by
    constructor
    · intro i hi
      change (mem (adjOldCount pub i).val).val = _ ∧ _
      simp [adjPrefix, oldZero i hi]
    · intro j hj
      change (mem (adjNewCount pub j).val).val = _ ∧ _
      simp [adjPrefix, newZero j hj]
    · exact fun _ _ _ => rfl
  simpa using adjSegment_run bounds frames h ((pub 1).val * (pub 0).val) (by simp)

end CompressorRecords.SliceRAM

end VPVNP
end Computability
end OAI
