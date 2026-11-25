import OAI.Optimization.LinearProgramming.Compression.RequestRAM
import Mathlib.Data.List.OfFn

/-! The fixed-order scan of the whole reduced graph basis on the scalar RAM. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestScreen

open RAM
open scoped BigOperators

private structure Best {d : ℕ} (p : Fin d → Prop) (k sel : ℕ) : Prop where
  found : sel = d ∨ ∃ i : Fin d, sel = i.val ∧ i.val < k ∧ p i
  first : ∀ i : Fin d, i.val < k → p i → sel ≤ i.val

private theorem best_next {d : ℕ} (p : Fin d → Prop) [DecidablePred p] {k sel : ℕ}
    (h : Best p k sel) (i : Fin d) (hi : i.val = k) :
    Best p (k+1) (if p i then min sel k else sel) := by
  by_cases hpi : p i
  · rw [ite_eq_left hpi]
    constructor
    · by_cases hsk : sel ≤ k
      · rw [min_eq_left hsk]
        rcases h.found with hs | ⟨j,hj,hl,hp⟩
        · exact Or.inl hs
        · exact Or.inr ⟨j,hj,by omega,hp⟩
      · rw [min_eq_right (le_of_not_ge hsk)]
        exact Or.inr ⟨i, hi.symm, by omega, hpi⟩
    · intro j hj hp
      by_cases hjk : j.val < k
      · exact (min_le_left ..).trans (h.first j hjk hp)
      · exact (min_le_right ..).trans (by omega)
  · rw [ite_eq_right hpi]
    constructor
    · rcases h.found with hs | ⟨j,hj,hl,hp⟩
      · exact Or.inl hs
      · exact Or.inr ⟨j,hj,by omega,hp⟩
    · intro j hj hp
      apply h.first j _ hp
      have hn : j.val ≠ k := fun he => hpi ((Fin.ext (he.trans hi.symm) : j = i) ▸ hp)
      omega

/-- Address register 28 remembers the least eligible row, with the row count as sentinel. -/
private def remember : Block :=
  .branch (.addrLT 29 25) (.branch (.addrLT 26 28) (.op (.addrCopy 28 26)) .skip) .skip

private theorem remember_spec (P : ℚ → Prop) (m : Memory ℚ) (hm : m.AllData P)
    (hz : m.index 29 = 0) (hb : m.index 25 = 1 ∨ m.index 25 = 0) :
    ∃ k ≤ 5, ∃ t, Block.Eval (Memory.AllData P) remember m k t ∧
      t.index 28 = (if m.index 25 = 1 then min (m.index 28) (m.index 26) else m.index 28) ∧
      t.data = m.data ∧ ∀ j ≠ 28, t.index j = m.index j := by
  rcases hb with hb | hb
  · have hac : (Cond.addrLT 29 25).test m = true := by simp [Cond.test, hz, hb]
    by_cases hlt : m.index 26 < m.index 28
    · refine ⟨5, le_rfl, _, .branchTrue hac (.branchTrue (by simpa [Cond.test] using hlt)
        (Block.Eval.op_addrCopy m 28 26 hm (hm.putIndex 28 _))), ?_, rfl, ?_⟩
      · simp [hb, min_eq_right hlt.le]
      · intro j hj; exact m.putIndex_ne hj _
    · refine ⟨3, by decide, m, .branchTrue hac (.branchFalse (by simp [Cond.test, hlt]) (.skip hm)),
        ?_, rfl, fun _ _ => rfl⟩
      simp [hb, min_eq_left (le_of_not_gt hlt)]
  · refine ⟨1, by decide, m, .branchFalse (by simp [Cond.test, hz, hb]) (.skip hm),
      ?_, rfl, fun _ _ => rfl⟩
    simp [hb]

/-- Register 27 supplies the number of basis rows. All rows are contiguous, each with
its integer coordinates followed by its rational dot product. -/
def scan : Block :=
  .seq (.op (.addrCopy 28 27)) (.seq (.op (.addrConst 29 0))
    (.forRange 26 27 (.seq block remember)))

private structure ScanAt {n : ℕ} (p : Fin (n+1) → Prop) (entry : Memory ℚ) (k : ℕ)
    (s : Memory ℚ) : Prop where
  left : s.index 20 = entry.index 20 + k*(n+2)
  right : s.index 21 = s.index 20
  width : s.index 23 = n+2
  cursor : s.index 26 = k
  rows : s.index 27 = n+1
  zero : s.index 29 = 0
  cells : ∀ j, j = 0 ∨ j = 2 ∨ 23 < j → s.data j = entry.data j
  best : Best p k (s.index 28)

private theorem full_best {n : ℕ} (w : Fin (n+1) → ℚ) (g : Fin (n+1) → Fin (n+1) → ℤ)
    (s : ℕ) (hs : Best (fun i => g i (Fin.last n) ≠ 0 ∧
      requestGraphSquare w (g i) ≤ (requestCutoff (n+1) : ℚ)^2) (n+1) s) :
    s = ((requestCandidate w g (Fin.last n)).map Fin.val).getD (n+1) := by
  let p := fun i => g i (Fin.last n) ≠ 0 ∧ requestGraphSquare w (g i) ≤ (requestCutoff (n+1) : ℚ)^2
  rcases hs.found with hd | ⟨i,hsi,_,hpi⟩
  · have hnone : requestCandidate w g (Fin.last n) = none := by
      apply List.find?_eq_none.mpr
      intro j _
      change ¬ (decide (p j) = true)
      rw [decide_eq_true_eq]
      intro hj
      have hb := hs.first j j.isLt hj
      omega
    simp [hnone,hd]
  · have hsome : requestCandidate w g (Fin.last n) = some i := by
      change (List.ofFn (fun j : Fin (n+1) => j)).find? (fun j => decide (p j)) = some i
      apply (List.find?_ofFn_eq_some_of_injective (f := fun j : Fin (n+1) => j) Function.injective_id).mpr
      refine ⟨decide_eq_true hpi, ?_⟩
      intro j hji hj
      have hb := hs.first j j.isLt (of_decide_eq_true hj)
      have hlt : j.val < i.val := hji
      omega
    simp [hsome, hsi]

/-- The same scalar RAM program for every dimension returns the deterministic first
eligible basis row. Each row takes a linear number of instructions, including its memory
reads, comparison branches, and loop overhead. -/
theorem scan_spec {n B : ℕ} (w : Fin (n+1) → ℚ) (g : Fin (n+1) → Fin (n+1) → ℤ)
    (m : Memory ℚ)
    (hheight : ∀ i j, ((requestGraphRat w (g i)) j).num.natAbs ≤ B ∧
      ((requestGraphRat w (g i)) j).den ≤ B)
    (hsafe : m.AllData (fun a => ratBits a ≤ affineEvalBits (n+2) B))
    (haddr : 23 < m.index 20) (hmirror : m.index 21 = m.index 20) (hwidth : m.index 23 = n+2)
    (hrows : m.index 27 = n+1)
    (hrow : ∀ (i : Fin (n+1)) (j : Fin (n+2)),
      m.data (m.index 20+i.val*(n+2)+j.val) = requestGraphRat w (g i) j)
    (hcap : m.data 0 = (requestCutoff (n+1) : ℚ)^2) (hzero : m.data 2 = 0) :
    ∃ k ≤ (n+1)*(9*(n+2)+19)+4, ∃ t,
      Block.Eval (Memory.AllData (fun a => ratBits a ≤ affineEvalBits (n+2) B)) scan m k t ∧
      t.index 28 = ((requestCandidate w g (Fin.last n)).map Fin.val).getD (n+1) := by
  let P : ℚ → Prop := fun a => ratBits a ≤ affineEvalBits (n+2) B
  let p := fun i => g i (Fin.last n) ≠ 0 ∧ requestGraphSquare w (g i) ≤ (requestCutoff (n+1) : ℚ)^2
  let s₁ := m.putIndex 28 (m.index 27)
  let s₂ := s₁.putIndex 29 0
  have h₁ : Block.Eval (Memory.AllData P) (.op (.addrCopy 28 27)) m 1 s₁ :=
    .op_addrCopy _ _ _ hsafe (hsafe.putIndex 28 _)
  have h₂ : Block.Eval (Memory.AllData P) (.op (.addrConst 29 0)) s₁ 1 s₂ :=
    .op_addrConst _ _ _ h₁.safe_end (h₁.safe_end.putIndex 29 0)
  let I := fun k s => Memory.AllData P s ∧ ScanAt p m k s
  have hi : I 0 (s₂.putIndex 26 0) := by
    refine ⟨h₂.safe_end.putIndex 26 0, ?_⟩
    constructor <;> simp [s₂,s₁,Memory.putIndex,hmirror,hwidth,hrows]
    exact ⟨Or.inl rfl, fun j h _ => (Nat.not_lt_zero _ h).elim⟩
  obtain ⟨t,k,hk,run,hend⟩ := Block.Eval.forRange_invariant (body := .seq block remember)
    26 27 (n+1) (9*(n+2)+16) I s₂ h₂.safe_end hi
    (fun _ _ h => ⟨h.1,h.2.cursor,h.2.rows⟩) (by
      intro j hj s h
      let i : Fin (n+1) := ⟨j,hj⟩
      have ha : 23 < s.index 20 := by rw [h.2.left]; omega
      have dataRow (l : Fin (n+2)) : s.data (s.index 20+l.val) = requestGraphRat w (g i) l := by
        have hmem := h.2.cells (s.index 20+l.val) (Or.inr (Or.inr (by omega)))
        rw [hmem, h.2.left]
        exact hrow i l
      obtain ⟨rowK,hrowK,u,hrun,hit,binary,hl,hm,huI,huD⟩ := block_spec w (g i) s (hheight i) h.1
        ha h.2.right h.2.width dataRow ((h.2.cells 0 (Or.inl rfl)).trans hcap)
        ((h.2.cells 2 (Or.inr (Or.inl rfl))).trans hzero)
      have hu29 := (huI 29 (by decide) (by decide) (by decide)).trans h.2.zero
      obtain ⟨remK,hremK,v,rrun,rval,rd,ri⟩ := remember_spec P u hrun.safe_end hu29 binary
      have hu26 := (huI 26 (by decide) (by decide) (by decide)).trans h.2.cursor
      have hu28 := huI 28 (by decide) (by decide) (by decide)
      have hv26 := (ri 26 (by decide)).trans hu26
      refine ⟨v, rowK+remK, by omega, .seq hrun rrun, rrun.safe_end.putIndex 26 _, ?_⟩
      constructor
      · simp only [Memory.putIndex_ne _ (by decide : 20 ≠ 26), ri 20 (by decide), hl, h.2.left]
        rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp [Memory.putIndex, ri 20 (by decide), ri 21 (by decide), hm]
      · simp [Memory.putIndex, ri 23 (by decide), huI 23 (by decide) (by decide) (by decide), h.2.width]
      · simp [hv26]
      · simp [Memory.putIndex, ri 27 (by decide), huI 27 (by decide) (by decide) (by decide), h.2.rows]
      · simp [Memory.putIndex, ri 29 (by decide), hu29]
      · intro l hl
        rw [Memory.putIndex_data, rd, huD _ (by rcases hl with h0|h2|hh <;> omega) (by rcases hl with h0|h2|hh <;> omega)]
        exact h.2.cells l hl
      · have hh : u.index 25 = 1 ↔ p i := by exact_mod_cast hit
        simpa [Memory.putIndex, rval, hh, hu26, hu28] using best_next p h.2.best i rfl)
  rw [show 9*(n+2)+16+3 = 9*(n+2)+19 by omega] at hk
  refine ⟨1+(1+k), by omega, t, h₁.seq (h₂.seq run), full_best w g _ hend.2.best⟩

end RequestScreen
end Compression
end LinearProgramming
end Optimization
end OAI
