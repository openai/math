import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Uniform row-major address arithmetic on the scalar/address RAM. Copies of an address
cost one instruction independent of its value. The loops count rows, columns and stride. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Decode the scalar cells of a row-major square matrix. -/
def uniformMatrix {K : Type} (n base : ℕ) (m : RAM.Memory K) : Matrix (Fin n) (Fin n) K :=
  fun i j => m.data (base + i.val * n + j.val)

private def bumpBy (dst ctr bound : ℕ) : Block :=
  .seq (.op (.addrConst ctr 0)) (.loop (.addrLT ctr bound)
    (.seq (.op (.incr dst dst)) (.op (.incr ctr ctr))))

private theorem bumpBy_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : (ℕ → K) → Prop) (m : Memory K) (hm : P m.data) (dst ctr bound : ℕ)
    (hdc : dst ≠ ctr) (hbd : bound ≠ dst) (hbc : bound ≠ ctr) :
    ∃ t, Block.Eval (fun s => P s.data) (bumpBy dst ctr bound) m (4*m.index bound+2) t ∧
      t.data = m.data ∧ (∀ p, p ≠ dst → p ≠ ctr → t.index p = m.index p) ∧
      t.index dst = m.index dst + m.index bound := by
  let I := fun k (s : Memory K) => s.data = m.data ∧ s.index ctr = k ∧
    s.index dst = m.index dst+k ∧ ∀ p, p ≠ dst → p ≠ ctr → s.index p = m.index p
  let start := m.putIndex ctr 0
  have hi : I 0 start := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [start]
    · simp [start, hdc]
    · intro p _ hp
      simp [start, hp]
  have hb (k : ℕ) (hk : k < m.index bound) (s : Memory K) (ih : I k s) :
      (Cond.addrLT ctr bound).test s = true ∧
      ∃ t, Block.Eval (fun u => P u.data) (.seq (.op (.incr dst dst)) (.op (.incr ctr ctr)))
        s 2 t ∧ I (k+1) t := by
    obtain ⟨hsdata, hctr, hdst, hkeep⟩ := ih
    refine ⟨by simpa [Cond.test, hctr, hkeep bound hbd hbc], ?_⟩
    let u := s.putIndex dst (s.index dst+1)
    let t := u.putIndex ctr (u.index ctr+1)
    have hp : P s.data := hsdata ▸ hm
    refine ⟨t, .seq (Block.Eval.op_incr _ _ _ hp hp) (Block.Eval.op_incr _ _ _ hp hp), ?_⟩
    refine ⟨hsdata, ?_, ?_, ?_⟩
    · simp [t, u, Memory.putIndex, hdc.symm, hctr]
    · simp [t, u, Memory.putIndex, hdc, hdst, Nat.add_assoc]
    · intro p hp₁ hp₂
      simp [t, u, Memory.putIndex, hp₁, hp₂, hkeep p hp₁ hp₂]
  have halt (t : Memory K) (ht : I (m.index bound) t) :
      (Cond.addrLT ctr bound).test t = false ∧ P t.data := by
    exact ⟨by simp [Cond.test, ht.2.1, ht.2.2.2 bound hbd hbc], ht.1 ▸ hm⟩
  obtain ⟨t, hloop, ht⟩ := Block.Eval.loop_invariant_exact I start (m.index bound) 2 hi hb halt
  have hstart : Block.Eval (fun u => P u.data) (.op (.addrConst ctr 0)) m 1 start :=
    Block.Eval.op_addrConst m ctr 0 hm hm
  refine ⟨t, ?_, ht.1, ht.2.2.2, ht.2.2.1⟩
  simpa only [bumpBy, show 1+(m.index bound*(2+2)+1) = 4*m.index bound+2 by omega] using hstart.seq hloop

/-- The stride, row and column registers can coincide, but each survives both counters
and the destination register. The base is only read at initialization. -/
def CellScratchOK (dst outer inner n i j : ℕ) : Prop :=
  dst ≠ outer ∧ dst ≠ inner ∧ outer ≠ inner ∧
  ∀ p ∈ [n,i,j], p ≠ dst ∧ p ≠ outer ∧ p ≠ inner

/-- A fixed block for `base + i*n + j`. No multiplication instruction on addresses is needed. -/
def cellAddress (dst outer inner base n i j : ℕ) : Block :=
  .seq (.op (.addrCopy dst base)) (.seq (.op (.addrConst outer 0))
    (.seq (.loop (.addrLT outer i) (.seq (bumpBy dst inner n) (.op (.incr outer outer))))
      (bumpBy dst inner j)))

/-- Precise runtime and frame of row-major address computation. -/
theorem cellAddress_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : (ℕ → K) → Prop) (m : Memory K) (hm : P m.data) (dst outer inner base n i j : ℕ)
    (hs : CellScratchOK dst outer inner n i j) :
    ∃ t, Block.Eval (fun z => P z.data) (cellAddress dst outer inner base n i j)
      m (m.index i * (4*m.index n + 5) + 4*m.index j + 5) t ∧ t.data = m.data ∧
      (∀ p, p ≠ dst → p ≠ outer → p ≠ inner → t.index p = m.index p) ∧
      t.index dst = m.index base + m.index i*m.index n + m.index j := by
  obtain ⟨hdo,hdi,hoi,hregs⟩ := hs
  obtain ⟨hnd,hno,hni⟩ := hregs n (by simp)
  obtain ⟨hid,hio,hii⟩ := hregs i (by simp)
  obtain ⟨hjd,hjo,hji⟩ := hregs j (by simp)
  let u := m.putIndex dst (m.index base)
  let start := u.putIndex outer 0
  let I := fun k (s : Memory K) => s.data = m.data ∧ s.index outer = k ∧
    s.index dst = m.index base + k*m.index n ∧
    ∀ p, p ≠ dst → p ≠ outer → p ≠ inner → s.index p = m.index p
  have hi : I 0 start := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [start]
    · simp [start, u, hdo]
    · intro p hd ho _
      simp [start, u, hd, ho]
  have hb (k : ℕ) (hk : k < m.index i) (s : Memory K) (ih : I k s) :
      (Cond.addrLT outer i).test s = true ∧ ∃ t,
        Block.Eval (fun z => P z.data) (.seq (bumpBy dst inner n) (.op (.incr outer outer)))
          s (4*m.index n+3) t ∧ I (k+1) t := by
    obtain ⟨hsdata, ho, hd, hkeep⟩ := ih
    refine ⟨by simpa [Cond.test, ho, hkeep i hid hio hii], ?_⟩
    obtain ⟨v, hv, hvdata, hvkeep, hvdst⟩ :=
      bumpBy_spec P s (hsdata ▸ hm) dst inner n hdi hnd hni
    let t := v.putIndex outer (v.index outer + 1)
    have he : Block.Eval (fun z => P z.data) (.op (.incr outer outer)) v 1 t :=
      Block.Eval.op_incr _ _ _ (hvdata ▸ hsdata ▸ hm) (hvdata ▸ hsdata ▸ hm)
    have hn := hkeep n hnd hno hni
    refine ⟨t, ?_, hvdata.trans hsdata, ?_, ?_, ?_⟩
    · simpa [hn, Nat.add_assoc] using hv.seq he
    · simp [t, Memory.putIndex, hvkeep outer hdo.symm hoi, ho]
    · simp [t, Memory.putIndex, hdo, hvdst, hd, hn, Nat.succ_mul, Nat.add_assoc]
    · intro p hp₁ hp₂ hp₃
      simp [t, Memory.putIndex, hp₂, hvkeep p hp₁ hp₃, hkeep p hp₁ hp₂ hp₃]
  have halt (t : Memory K) (ht : I (m.index i) t) :
      (Cond.addrLT outer i).test t = false ∧ P t.data := by
    exact ⟨by simp [Cond.test, ht.2.1, ht.2.2.2 i hid hio hii], ht.1 ▸ hm⟩
  obtain ⟨v, hver, hv⟩ := Block.Eval.loop_invariant_exact I start (m.index i) (4*m.index n+3) hi hb halt
  obtain ⟨w, hw, hwdata, hwkeep, hwdst⟩ := bumpBy_spec P v (hv.1 ▸ hm) dst inner j hdi hjd hji
  have he : Block.Eval (fun z => P z.data) (.op (.addrCopy dst base)) m 1 u :=
    Block.Eval.op_addrCopy _ _ _ hm hm
  have ho : Block.Eval (fun z => P z.data) (.op (.addrConst outer 0)) u 1 start :=
    Block.Eval.op_addrConst _ _ _ hm hm
  refine ⟨w, ?_, hwdata.trans hv.1, ?_, ?_⟩
  · have h := he.seq (ho.seq (hver.seq hw))
    rw [hv.2.2.2 j hjd hjo hji] at h
    unfold cellAddress
    convert h using 1
    ring
  · intro p h₁ h₂ h₃
    exact (hwkeep p h₁ h₃).trans (hv.2.2.2 p h₁ h₂ h₃)
  · rw [hwdst, hv.2.2.1, hv.2.2.2 j hjd hjo hji]

end Compression
end LinearProgramming
end Optimization
end OAI
