import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Mul

namespace OAI
/-! # External indices in a scan of disjoint chunks

Each chunk has its own finite state space, which can itself represent a block of
bits. Updating disjoint chunks in succession forces the intermediate external
index. A complete scan therefore multiplies the local matrix entries.
-/

namespace ThreeFlat.Diagonal

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
variable {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

/-- Change the chunks in `s` according to their local matrices and preserve the
external index on all other chunks. -/
noncomputable def chunkKernel (K : ∀ i, Matrix (X i) (X i) R) (s : Finset ι) :
    Matrix (∀ i, X i) (∀ i, X i) R := by
  classical
  exact fun x y => if ∀ i ∉ s, x i = y i then ∏ i ∈ s, K i (x i) (y i) else 0

/-- With two disjoint sets of updates, each coordinate of the intermediate
index is forced by one of the two endpoints. -/
theorem chunkKernel_mul_of_disjoint (K : ∀ i, Matrix (X i) (X i) R)
    {s t : Finset ι} (hst : Disjoint s t) :
    chunkKernel K s * chunkKernel K t = chunkKernel K (s ∪ t) := by
  classical
  ext x y
  let m : ∀ i, X i := fun i => if i ∈ s then y i else x i
  have first : ∀ i ∉ s, x i = m i := fun i hi => by simp [m, hi]
  have only : ∀ z : ∀ i, X i, z ≠ m → chunkKernel K s x z * chunkKernel K t z y = 0 := by
    intro z hz
    by_cases hs : ∀ i ∉ s, x i = z i
    · by_cases ht : ∀ i ∉ t, z i = y i
      · exact (hz (funext fun i => by
          by_cases hi : i ∈ s
          · simpa [m, hi] using ht i (Finset.disjoint_left.mp hst hi)
          · simpa [m, hi] using (hs i hi).symm)).elim
      · simp [chunkKernel, ht]
    · simp [chunkKernel, hs]
  rw [Matrix.mul_apply, Finset.sum_eq_single m (fun z _ hz => only z hz)
    (fun h => (h (Finset.mem_univ m)).elim)]
  by_cases h : ∀ i ∉ s ∪ t, x i = y i
  · have second : ∀ i ∉ t, m i = y i := by
      intro i hit
      by_cases his : i ∈ s
      · simp [m, his]
      · simpa [m, his] using h i (by simp [his, hit])
    simp only [chunkKernel, ite_eq_left first, ite_eq_left second, ite_eq_left h, Finset.prod_union hst]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [m, hi]
    · exact Finset.prod_congr rfl fun i hi => by
        simp [m, Finset.disjoint_right.mp hst hi]
  · have second : ¬ ∀ i ∉ t, m i = y i := by
      intro ht
      apply h
      intro i hi
      have hn := Finset.notMem_union.mp hi
      exact (first i hn.1).trans (ht i hn.2)
    simp only [chunkKernel, ite_eq_right second, ite_eq_right h, mul_zero]

/-- Scanning a list of distinct chunks multiplies their matrices on precisely
those chunks. The statement also covers an empty scan. -/
theorem chunkKernel_scan (K : ∀ i, Matrix (X i) (X i) R) (order : List ι)
    (hd : order.Nodup) :
    (order.map (fun i => chunkKernel K {i})).prod = chunkKernel K order.toFinset := by
  classical
  induction order with
  | nil =>
      ext x y
      by_cases h : x = y
      · subst y
        simp [chunkKernel]
      · have hd : ¬ ∀ i, x i = y i := fun e => h (funext e)
        simp [chunkKernel, h, hd]
  | cons i l ih =>
      obtain ⟨hi, hl⟩ := List.nodup_cons.mp hd
      simp only [List.map_cons, List.prod_cons, List.toFinset_cons, ih hl]
      rw [chunkKernel_mul_of_disjoint K (by simpa using hi :
        Disjoint ({i} : Finset ι) l.toFinset)]
      simp

/-- A complete scan changes every external chunk once. Its entry between the
two fixed external indices is the product of the individual cell entries. -/
theorem complete_chunk_scan_apply (K : ∀ i, Matrix (X i) (X i) R)
    (order : List ι) (hd : order.Nodup) (covers : ∀ i, i ∈ order) (x y : ∀ i, X i) :
    (order.map (fun i => chunkKernel K {i})).prod x y = ∏ i, K i (x i) (y i) := by
  classical
  have hu : order.toFinset = Finset.univ := Finset.eq_univ_iff_forall.mpr fun i => by
    simpa using covers i
  simp [chunkKernel_scan K order hd, hu, chunkKernel]

/-- The scan checks the old and new value of this chunk against the two
endpoints stored in shared workspace. -/
def checkChunk (p q : ∀ i, X i) (i : ι) : Matrix (X i) (X i) R :=
  fun a b => if p i = a ∧ q i = b then 1 else 0

/-- The complete sequence of local checks accepts exactly the proposed
endpoints for the full register. -/
theorem checkChunk_scan_apply (p q : ∀ i, X i) (order : List ι)
    (hd : order.Nodup) (covers : ∀ i, i ∈ order) (x y : ∀ i, X i) :
    (order.map fun i => chunkKernel (checkChunk (R := R) p q) {i}).prod x y =
      if p = x ∧ q = y then 1 else 0 := by
  classical
  rw [complete_chunk_scan_apply _ order hd covers]
  simp only [checkChunk, Fintype.prod_boole, forall_and, ← funext_iff]

/-- The workspace stores both proposed endpoints. After every chunk has
validated its pair, the evaluator can apply an arbitrary joint weight to
the stored data. Summing the choices gives the desired kernel entry even
when the different chunks have coupled weights. -/
theorem two_phase_scan_apply (K : Matrix (∀ i, X i) (∀ i, X i) R)
    (order : List ι) (hd : order.Nodup) (covers : ∀ i, i ∈ order) (x y : ∀ i, X i) :
    (∑ p, ∑ q, K p q *
      (order.map fun i => chunkKernel (checkChunk p q) {i}).prod x y) = K x y := by
  classical
  simp_rw [checkChunk_scan_apply _ _ order hd covers x y]
  simp [mul_ite, ite_and]

/-- A group visits the entire external index but has workspace only for
the pairs assigned to it. Other coordinates undergo an equality test. -/
noncomputable def checkGroupChunk (active : Finset ι)
    (p q : ∀ i : active, X i) (i : ι) : Matrix (X i) (X i) R := by
  classical
  exact fun a b => if (∀ hi : i ∈ active, p ⟨i, hi⟩ = a ∧ q ⟨i, hi⟩ = b) ∧
    (i ∉ active → a = b) then 1 else 0

private theorem checkGroup_scan_apply (active : Finset ι) (p q : ∀ i : active, X i)
    (order : List ι) (hd : order.Nodup) (covers : ∀ i, i ∈ order) (x y : ∀ i, X i) :
    (order.map fun i => chunkKernel (checkGroupChunk (R := R) active p q) {i}).prod x y =
      if p = (fun i : active => x i) ∧ q = (fun i : active => y i) ∧
        (∀ i ∉ active, x i = y i) then 1 else 0 := by
  classical
  have eq_ends :
      (∀ i, (∀ hi : i ∈ active, p ⟨i, hi⟩ = x i ∧ q ⟨i, hi⟩ = y i) ∧
        (i ∉ active → x i = y i)) ↔
      p = (fun i : active => x i) ∧ q = (fun i : active => y i) ∧
        (∀ i ∉ active, x i = y i) := by
    constructor
    · intro h
      exact ⟨funext fun i => ((h i).1 i.property).1,
        funext fun i => ((h i).1 i.property).2, fun i => (h i).2⟩
    · rintro ⟨rfl, rfl, h⟩
      exact fun i => ⟨fun _ => ⟨rfl, rfl⟩, h i⟩
  rw [complete_chunk_scan_apply _ order hd covers]
  simp only [checkGroupChunk, Fintype.prod_boole, eq_ends]

/-- A scan of the whole memory can apply a joint kernel to an arbitrary set
of scattered positions. Each inactive position keeps its value, and only
the endpoints of the active positions are stored. -/
theorem two_phase_group_scan_apply (active : Finset ι)
    (K : Matrix (∀ i : active, X i) (∀ i : active, X i) R)
    (order : List ι) (hd : order.Nodup) (covers : ∀ i, i ∈ order) (x y : ∀ i, X i) :
    (∑ p, ∑ q, K p q *
      (order.map fun i => chunkKernel (checkGroupChunk active p q) {i}).prod x y) =
      if ∀ i ∉ active, x i = y i then K (fun i => x i) (fun i => y i) else 0 := by
  classical
  simp_rw [checkGroup_scan_apply active _ _ order hd covers x y]
  by_cases h : ∀ i ∉ active, x i = y i
  · rw [ite_eq_left h, Finset.sum_eq_single_of_mem (fun i : active => x i) (Finset.mem_univ _)]
    · rw [Finset.sum_eq_single_of_mem (fun i : active => y i) (Finset.mem_univ _)]
      · rw [ite_eq_left ⟨rfl, rfl, h⟩, mul_one]
      · intro q _ hq
        rw [ite_eq_right (fun e => hq e.2.1), mul_zero]
    · intro p _ hp
      simp [hp]
  · simp only [h, and_false, ite_false, mul_zero, Finset.sum_const_zero]

end ThreeFlat.Diagonal

end OAI
