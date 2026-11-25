import OAI.Optimization.LinearProgramming.Elimination.UniformProbe

/-! An adaptive independent-column scan compiled to a single fixed program. The public
candidate order is `n-1,…,1,0`, matching the list-based solver. The integer counter is maintained by the RAM itself. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression Matrix Submodule
open scoped Matrix

private def suffixOrder (n k : ℕ) := (List.finRange n).drop (n-k)

private theorem suffixOrder_succ {n k : ℕ} (hk:k<n) :
    suffixOrder n (k+1) = (⟨n-(k+1),by omega⟩ : Fin n) :: suffixOrder n k := by
  have h : n-(k+1) < (List.finRange n).length := by simp; omega
  have e : n-(k+1)+1=n-k := by omega
  simpa [suffixOrder,List.getElem_finRange,e] using List.drop_eq_getElem_cons h

private theorem scanMem {K : Type} [Field K] [LinearOrder K] {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (js : List (Fin n)) (i : Fin n) : i∈scanMask G js → i∈js := by
  induction js with
  | nil => simp [scanMask]
  | cons j js ih =>
    intro h
    simp only [scanMask] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases Finset.mem_insert.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

/-- The actual contents represented by the boolean flags after `k` candidate visits. -/
def visitedBasis {K : Type} [Field K] [LinearOrder K] {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (k : ℕ) :=
  scanMask G (suffixOrder n k)

@[simp] theorem visitedBasis_full {K : Type} [Field K] [LinearOrder K] {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) : visitedBasis G n = scanMask G (List.finRange n) := by
  simp [visitedBasis,suffixOrder]

private theorem BasisState.putCounter {K : Type} [Field K] {n : ℕ} {l : BasisLayout n}
    {G : Matrix (Fin n) (Fin n) K} {S : Finset (Fin n)} {m : Memory K} (s : BasisState l G S m)
    (p k : ℕ) (hp : 18<p) : BasisState l G S (m.putIndex p k) := by
  have f (a : ℕ) (ha:a<p) : (m.putIndex p k).index a = m.index a := by simp [Memory.putIndex,ha.ne]
  exact ⟨(f 0 (by omega)).trans s.dim,(f 1 (by omega)).trans s.maskPtr,(f 11 (by omega)).trans s.workAPtr,
    (f 12 (by omega)).trans s.workBPtr,(f 14 (by omega)).trans s.zeroIdx,(f 17 (by omega)).trans s.gramPtr,
    (f 18 (by omega)).trans s.flagsPtr,s.gram,s.flags⟩

def uniformBasisScan : Block := .seq (.op (.addrCopy 19 0))
  (.forRange 20 0 (.seq (.op (.decr 19 19)) uniformBasisProbe))

def basisScanCost (n : ℕ) : ℕ := 1+(n*((1+basisProbeCost n)+3)+2)

/-- One fixed program computes the same basis mask as the executable rectangular solver.
The initial Gram table and its header are preserved and every visited scalar satisfies `P`. -/
theorem uniformBasisScan_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (l : BasisLayout n) (G : Matrix (Fin n) (Fin n) K) (P : K → Prop) (m : Memory K)
    (hs : BasisState l G ∅ m) (hm : ∀i,P (m.data i)) (h0 : P 0) (h1 : P 1) (hneg : ∀ x,P x → P (-x))
    (hreg : ∀S : Finset (Fin n),let T := maskGram G (flag S)
      ∀ k<n,∀ r : BirdRegister n, P (r.read T (birdLayer T k))) :
    ∃ t steps, steps ≤ basisScanCost n ∧ Block.Eval (fun w => ∀i,P (w.data i)) uniformBasisScan m steps t ∧
      BasisState l G (visitedBasis G n) t ∧ (∀p,21≤p → t.index p=m.index p) ∧
      ∀p,7≤p → p<l.flags → t.data p=m.data p := by
  let safe := fun w : Memory K => ∀i,P (w.data i)
  let first := m.putIndex 19 (m.index 0)
  have efirst : Block.Eval safe (.op (.addrCopy 19 0)) m 1 first := Block.Eval.op_addrCopy _ _ _ hm hm
  let I (k : ℕ) (s : Memory K) := BasisState l G (visitedBasis G k) s ∧ s.index 20=k ∧
    s.index 19=n-k ∧ safe s ∧ (∀p,21≤p → s.index p=m.index p) ∧
    ∀p,7≤p → p<l.flags → s.data p=m.data p
  have ini : I 0 (first.putIndex 20 0) := by
    refine ⟨?_,by simp,?_,hm,?_,fun _ _ _ => rfl⟩
    · have z : visitedBasis G 0=∅ := by
        change scanMask G ((List.finRange n).drop (n-0))=∅
        rw [List.drop_eq_nil_iff.mpr (by simp)];rfl
      rw [z];exact (hs.putCounter 19 (m.index 0) (by decide)).putCounter 20 0 (by decide)
    · simp [first,hs.dim]
    · intro p hp; simp [first,Memory.putIndex,show p≠19 by omega,show p≠20 by omega]
  have adv (k : ℕ) (hk : k<n) (s : Memory K) (h : I k s) :
      ∃ t c,c≤1+basisProbeCost n ∧ Block.Eval safe (.seq (.op (.decr 19 19)) uniformBasisProbe) s c t ∧
        I (k+1) (t.putIndex 20 (t.index 20+1)) := by
    let j : Fin n := ⟨n-(k+1),by omega⟩
    let u := s.putIndex 19 (s.index 19-1)
    have eu : Block.Eval safe (.op (.decr 19 19)) s 1 u := Block.Eval.op_decr _ _ _ h.2.2.2.1 h.2.2.2.1
    have uj : u.index 19=j.val := by simp [u,j,h.2.2.1,Nat.sub_sub]
    have hf : j ∉ visitedBasis G k := by
      intro hj
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (scanMem G _ j hj)
      have hv := congrArg Fin.val he
      simp only [suffixOrder,List.getElem_drop,List.getElem_finRange,Fin.val_cast, j] at hv
      omega
    obtain ⟨t,c,hc,he,ht,tj,tf,td⟩ := uniformBasisProbe_spec l G (visitedBasis G k) P u j
      (h.1.putCounter 19 _ (by decide)) uj hf h.2.2.2.1 h0 h1 hneg (hreg _)
    have hs' : BasisState l G (visitedBasis G (k+1)) t := by
      unfold visitedBasis
      rw [suffixOrder_succ hk]
      change BasisState l G (if determinant (maskGram G (flag (insert j (visitedBasis G k))))=0 then visitedBasis G k else insert j (visitedBasis G k)) t
      exact ht
    have tc : t.index 20=k := (tf 20 (by decide)).trans (by simpa [u] using h.2.1)
    exact ⟨t,1+c,Nat.add_le_add_left hc 1,eu.seq he,hs'.putCounter 20 _ (by decide),
      by simp [tc],by simp [tj,j],he.safe_end,fun p hp =>
        (Memory.putIndex_ne _ (by omega) _).trans ((tf p (by omega)).trans
          ((Memory.putIndex_ne _ (by omega) _).trans (h.2.2.2.2.1 p hp))),
      fun p hp hf => (td p hp hf).trans (h.2.2.2.2.2 p hp hf)⟩
  obtain ⟨t,k,hk,he,ht⟩ := Block.Eval.forRange_invariant
    (body:=.seq (.op (.decr 19 19)) uniformBasisProbe) 20 0 n (1+basisProbeCost n) I first hm ini
    (fun _ _ h => ⟨h.2.2.2.1,h.2.1,h.1.dim⟩) adv
  exact ⟨t,1+k,Nat.add_le_add_left hk 1,efirst.seq he,ht.1,ht.2.2.2.2⟩

/-- The visited flags certify independence, full column span and exact rank. -/
theorem visitedBasis_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) K) :
    let S := visitedBasis (Aᵀ*A) n
    LinearIndepOn K A.col (S : Set (Fin n)) ∧ span K (A.col '' (S : Set (Fin n))) = span K (Set.range A.col) ∧
      S.card=A.rank := by
  let S := visitedBasis (Aᵀ*A) n
  obtain ⟨hi,hspan⟩ := scanMask_spec A (suffixOrder n n)
  have hf : span K (A.col '' (S : Set (Fin n))) = span K (Set.range A.col) := by
    apply le_antisymm (span_mono (Set.image_subset_range ..))
    apply span_le.mpr; rintro _ ⟨i,rfl⟩
    exact hspan i (by simp [suffixOrder])
  have hr : Set.range (fun i : S => A.col i) = A.col '' (S : Set (Fin n)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hs,rfl⟩; exact ⟨⟨i,hs⟩,rfl⟩
  refine ⟨hi,hf,?_⟩
  change S.card=A.rank
  have hcard := finrank_span_eq_card hi.linearIndependent
  change Module.finrank K (span K (Set.range (fun i : S => A.col i))) = _ at hcard
  rw [hr,hf,← A.rank_eq_finrank_span_cols] at hcard
  change A.rank=Fintype.card S at hcard
  exact (Fintype.card_coe S).symm.trans hcard.symm

/-- For rational input the same program obeys a fixed polynomial register bound separately
from the dimension-only step bound. The bit budget is reused across all probes. -/
theorem uniformBasisScan_rational {n : ℕ} (l : BasisLayout n) (G : Matrix (Fin n) (Fin n) ℚ)
    (B M : ℕ) (w : Memory ℚ) (hs : BasisState l G ∅ w) (hw : ∀i,ratBits (w.data i) ≤ M)
    (hG : ∀i j,ratBits (G i j) ≤ B) (hB : 3 ≤ B) (hM : detRegisterBits n B ≤ M) :
    ∃ t k,k ≤ basisScanCost n ∧ Block.Eval (fun s => ∀i,ratBits (s.data i) ≤ M) uniformBasisScan w k t ∧
      BasisState l G (visitedBasis G n) t ∧ (∀p,21≤p → t.index p=w.index p) ∧
      ∀p,7≤p → p<l.flags → t.data p=w.data p := by
  have h3 : 3 ≤ M := (Nat.le_add_right 3 _).trans hM
  exact uniformBasisScan_spec l G (fun q => ratBits q ≤ M) w hs hw h3 h3
    (fun x hx => by simpa only [PrimalDual.ratBits_neg] using hx) (fun S => masked_bird_bits G S hG hB hM)

end Elimination
end LinearProgramming
end Optimization
end OAI
