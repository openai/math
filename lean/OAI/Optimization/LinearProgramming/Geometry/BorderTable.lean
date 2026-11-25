import OAI.Optimization.LinearProgramming.Geometry.BorderRecord

/-! Sequentially initialize every signed bordered-determinant request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Matrix Compression.MinorLoad
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r n k : ℕ}

private theorem array_before (base stride a b w : ℕ) (hab : a < b) (hw : w < stride) :
    base+stride*a+w < base+stride*b := by
  have h := Nat.mul_le_mul_left stride (Nat.succ_le_of_lt hab)
  rw [Nat.mul_succ] at h
  omega

structure TablePrefix (L : Layout r n) (D : Matrix (Fin r) (Fin n) K) (hr : k+1 ≤ r)
    (J : Fin k → Fin n) (j : ℕ) (s t : Memory K) : Prop where
  data : t.data=s.data
  outer : t.index 0=j
  minorSize : t.index 7=k+1
  head : t.index 3=L.headers+6*j
  cols : t.index 4=L.cols+(k+1)*j
  ready : L.Ready D J t
  words : ∀ a : Fin n, a.val < j → ∀ w<6, t.index (L.headers+6*a.val+w) = descriptorWord ((L.batch D hr J).query a) w
  selector : ∀ a : Fin n, a.val < j → ∀ i : Fin (k+1), t.index (L.cols+(k+1)*a.val+i.val)=(Fin.lastCases (motive := fun _ => Fin n) a J i).val
  frame : ∀ p, 8 ≤ p → (p < L.headers ∨ L.headers+6*j ≤ p) →
    (p < L.cols ∨ L.cols+(k+1)*j ≤ p) → t.index p=s.index p

theorem descriptorTable_spec (P : K → Prop) (s : Memory K) (hs : s.AllData P)
    (L : Layout r n) (D : Matrix (Fin r) (Fin n) K) (hr : k+1≤r) (J : Fin k → Fin n)
    (ready : L.Ready D J s) (h7 : s.index 7=k+1) (h3 : s.index 3=L.headers) (h4 : s.index 4=L.cols) :
    ∃ t, Block.Eval (Memory.AllData P) (.forRange 0 130 emitRecord) s (n*(k*7+22)+2) t ∧
      TablePrefix L D hr J n s t := by
  have hpg := L.pivots_ge
  have hpe := L.pivots_end
  have hhe := L.headers_end
  have hre := L.rows_end
  let Inv (j : ℕ) (t : Memory K) := TablePrefix L D hr J j s t
  have init : Inv 0 (s.putIndex 0 0) := by
    refine ⟨rfl, by simp, by simpa using h7, by simpa using h3, by simpa using h4,
      ready.of_frame hr rfl (fun p hp _ => Memory.putIndex_ne _ (by omega) _),
      fun _ ha => (Nat.not_lt_zero _ ha).elim, fun _ ha => (Nat.not_lt_zero _ ha).elim,
      fun p hp _ _ => Memory.putIndex_ne _ (by omega) _⟩
  have safe_of {t : Memory K} (h : t.data=s.data) : t.AllData P := by
    change ∀ p, P (t.data p)
    rw [h]
    exact hs
  obtain ⟨t, eval, post⟩ := Block.Eval.forRange_invariant_exact (body := emitRecord) 0 130 n (k*7+19)
    Inv s hs init (fun _ _ h => ⟨safe_of h.data,h.outer,h.ready.width⟩) (fun j hj u h => by
      let a : Fin n := ⟨j,hj⟩
      obtain ⟨v, ev, recEnd⟩ := emitRecord_spec P u (safe_of h.data) L D hr J a h.ready h.outer h.minorSize h.head h.cols
      let z := v.putIndex 0 (v.index 0+1)
      have zv (p : ℕ) (hne : p ≠ 0) : z.index p = v.index p := Memory.putIndex_ne _ hne _
      have endHeader : L.headers+6*j+6 ≤ L.cols := by
        have ht := Nat.mul_le_mul_left 6 (Nat.succ_le_of_lt hj)
        rw [Nat.mul_succ] at ht
        omega
      have hf (p : ℕ) (hl : 8≤p) (hh : p<L.headers+6*j ∨ L.headers+6*j+6≤p)
          (hc : p<L.cols+(k+1)*j ∨ L.cols+(k+1)*j+k+1≤p) : z.index p = u.index p :=
        (zv p (by omega)).trans (recEnd.frame p hl hh hc)
      have rd : L.Ready D J z := h.ready.of_frame hr recEnd.data (fun p hp hl =>
        hf p (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
      refine ⟨v, ev, recEnd.data.trans h.data, ?_, (zv 7 (by decide)).trans recEnd.minorSize,
        (zv 3 (by decide)).trans recEnd.headerCursor, (zv 4 (by decide)).trans recEnd.columnCursor, rd, ?_, ?_, ?_⟩
      · simp only [Memory.putIndex_same,recEnd.outer]
        rfl
      · intro b hb w hw
        by_cases hb' : b.val=j
        · have eq : b=a := Fin.ext hb'
          subst b
          exact (zv _ (by omega)).trans (recEnd.words w hw)
        · have hb'' : b.val<j := by omega
          have prior := array_before L.headers 6 b.val j w hb'' hw
          exact (hf _ (by omega) (Or.inl prior) (Or.inl (by omega))).trans (h.words b hb'' w hw)
      · intro b hb i
        by_cases hb' : b.val=j
        · have eq : b=a := Fin.ext hb'
          subst b
          exact (zv _ (by omega)).trans (recEnd.selector i)
        · have hb'' : b.val<j := by omega
          have prior := array_before L.cols (k+1) b.val j i.val hb'' i.isLt
          exact (hf _ (by omega) (Or.inr (by omega)) (Or.inl prior)).trans (h.selector b hb'' i)
      · intro p hp hh hc
        simp only [Nat.mul_succ] at hh hc
        exact (hf p hp (by omega) (by omega)).trans (h.frame p hp (by omega) (by omega)))
  exact ⟨t, eval, post⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
