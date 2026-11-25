import OAI.Optimization.LinearProgramming.Compression.ServiceLookupProgram
import OAI.Optimization.LinearProgramming.Compression.ServiceStageSlot

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM

structure Located {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (keys : List (NonzeroPairMinor D E)) (q : NonzeroPairMinor D E) (s t : Memory ℚ) : Prop where
  table : Stored D E keys t
  request : SlotAt D E q (slotBase n (keys.length+1)) t
  rank : t.index 19 = GeneratorTable.rank q keys
  found : t.index 1 = (if q∈keys then 1 else 0)
  base : t.index 14 = tableBase n
  count : t.index 17 = keys.length
  width : t.index 18 = stride n
  stop : t.index 20 = slotBase n keys.length
  incoming : t.index 21 = slotBase n (keys.length+1)
  dimension : t.index 22 = n
  indices : ∀a,40 ≤ a → t.index a = s.index a
  data : ∀a,a ≠ 0 → a ≠ 5 → a ≠ 6 → a < tableBase n → t.data a = s.data a

private theorem Stored.lows {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {keys : List (NonzeroPairMinor D E)} {s t : Memory ℚ} (h : Stored D E keys s)
    (hf : ∀a,a ≠ 0 → a ≠ 5 → a ≠ 6 → t.data a = s.data a) : Stored D E keys t :=
  ⟨h.sorted,(hf 4 (by decide) (by decide) (by decide)).trans h.count,
    fun i => (h.slots i).frame (slotBase_ge_seven _ _) hf⟩

private theorem Stored.stage {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {keys : List (NonzeroPairMinor D E)} {q : NonzeroPairMinor D E} {s t : Memory ℚ} (h : Stored D E keys s)
    (hs : SlotStaged D E q (slotBase n (keys.length+1)) s t) : Stored D E keys t := by
  have b := slotBase_ge_seven n (keys.length+1)
  refine ⟨h.sorted,(hs.data 4 (by decide) (by decide) (Or.inl (by omega))).trans h.count,?_⟩
  intro i
  apply (h.slots i).transfer
  intro j hj
  have hi := i.isLt
  have hg := slotBase_ge_seven n i.val
  have step : slotBase n i.val+stride n ≤ slotBase n (keys.length+1) := by
    unfold slotBase
    have h := Nat.mul_le_mul_right (stride n) (show i.val+1 ≤ keys.length+1 by omega)
    rw [Nat.add_mul,one_mul] at h
    omega
  exact hs.data _ (by omega) (by omega) (Or.inl (by omega))

set_option maxHeartbeats 1400000 in
/-- A single native lookup handles all matrix dimensions and generator histories. The
metadata is decoded from persistent scalars, and only the current candidate's words are inputs. -/
theorem lookup_spec (cmp : Block) (C : ℕ→ℕ) (hcmp : SlotComparatorSpec cmp C)
    {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (keys : List (NonzeroPairMinor D E)) (q : NonzeroPairMinor D E) (P : ℚ→Prop) (s : Memory ℚ)
    (hdim : d+e = n) (hkeys : Stored D E keys s) (hn : s.data 3 = (n:ℚ)) (wire : Wire q.val s)
    (hmag : s.data 5=|pairMinorValue D E q.val|) (hs : ∀a,P (s.data a))
    (hv : ∀ j ≤ max (4*(n+1)^2) (keys.length+1),P (j:ℚ)) :
    ∃t l,l ≤ lookupCost C n keys.length ∧ Block.Eval (fun z => ∀a,P (z.data a)) (lookup cmp) s l t ∧
      Located D E keys q s t := by
  have hn' : n ≤ 4*(n+1)^2 := by ring_nf; omega
  have h1 : 1 ≤ 4*(n+1)^2 := by ring_nf; omega
  let bound := max (4*(n+1)^2) (keys.length+1)
  have lown : n ≤ bound := hn'.trans (le_max_left _ _)
  have low1 : 1 ≤ bound := h1.trans (le_max_left _ _)
  have lowg : keys.length ≤ bound := Nat.le_succ _ |>.trans (le_max_right _ _)
  have hone : P 1 := by simpa using hv 1 low1
  obtain ⟨a,ea,prep⟩ := prepareTable_spec P s n keys.length hn hkeys.count hs hone
    (fun j hj => hv j (hj.trans (max_le lown lowg)))
  have ha : Stored D E keys a := hkeys.lows fun j h0 _ h6 => prep.data j h0 h6
  obtain ⟨b,k,hk,eb,sb⟩ := stageSlot_spec D E q P a (slotBase n (keys.length+1)) hdim
    prep.incoming prep.dimension (slotBase_ge_seven _ _) (wire.frame prep.indices)
    ((prep.data 5 (by decide) (by decide)).trans hmag) ea.safe_end (fun j hj => hv j (hj.trans (max_le lown low1)))
  have bx (j : ℕ) (hj : j < 26) : b.index j = a.index j := sb.indices j (by omega) (by omega) (by omega) (by omega) (by omega)
  have hb := ha.stage sb
  obtain ⟨t,l,hl,et,rank,found,ptr,ti,td⟩ := scanLoop_spec cmp C hcmp D E q keys P b hdim hb sb.slot
    ((bx 17 (by decide)).trans prep.count) ((bx 18 (by decide)).trans prep.width) ((bx 20 (by decide)).trans prep.first)
    ((bx 21 (by decide)).trans prep.incoming) ((bx 22 (by decide)).trans prep.dimension)
    ((bx 0 (by decide)).trans prep.one) ((bx 1 (by decide)).trans prep.found) ((bx 2 (by decide)).trans prep.two)
    ((bx 3 (by decide)).trans prep.zero) ((bx 16 (by decide)).trans prep.counter) ((bx 19 (by decide)).trans prep.rank)
    eb.safe_end (fun j hj => hv j (hj.trans (le_max_left _ _)))
  have tx (j : ℕ) (hj : ScanKeep j) (hlo : j < 26) := (ti j hj).trans (bx j hlo)
  refine ⟨t,prepareCost n keys.length+(k+l),by unfold lookupCost; omega,ea.seq (eb.seq et),
    hb.lows td,sb.slot.frame (slotBase_ge_seven _ _) td,rank,found,?_,?_,?_,ptr,?_,?_,?_,?_⟩
  · exact (tx 14 (by simp [ScanKeep]) (by decide)).trans prep.matrixEnd
  · exact (tx 17 (by simp [ScanKeep]) (by decide)).trans prep.count
  · exact (tx 18 (by simp [ScanKeep]) (by decide)).trans prep.width
  · exact (tx 21 (by simp [ScanKeep]) (by decide)).trans prep.incoming
  · exact (tx 22 (by simp [ScanKeep]) (by decide)).trans prep.dimension
  · intro j hj
    exact (ti j (by unfold ScanKeep; omega)).trans ((sb.indices j (by omega) (by omega) (by omega) (by omega) (by omega)).trans (prep.indices j hj))
  · intro j h0 h5 h6 hj
    have before : j < slotBase n (keys.length+1) := by unfold slotBase; omega
    exact (td j h0 h5 h6).trans ((sb.data j h0 h6 (Or.inl before)).trans (prep.data j h0 h6))

/-- The rank can be used immediately as the old coordinate when a key was already present. -/
theorem Located.hit {d e n : ℕ} {D : Matrix (Fin d) (Fin n) ℚ} {E : Matrix (Fin e) (Fin n) ℚ}
    {keys : List (NonzeroPairMinor D E)} {q : NonzeroPairMinor D E} {s t : Memory ℚ}
    (h : Located D E keys q s t) (hit : t.index 1 = 1) : ∃ hi : t.index 19 < keys.length,keys[t.index 19]=q := by
  have mem : q∈keys := by by_contra hm; simp [h.found,hm] at hit
  rw [h.rank]; exact membership_rank h.table.sorted mem

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
