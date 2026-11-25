import OAI.Optimization.LinearProgramming.Compression.UniformIndex

/-! Fixed RAM initialization from the ordinary row-major determinant input. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Reserve three consecutive, disjoint `n × n` tables above the input and scratch region. -/
def birdReserveBases : Block :=
  .seq (.op (.addrConst 14 0)) (.seq (.op (.addrConst 15 7))
    (.seq (cellAddress 1 8 9 15 0 0 14)
      (.seq (cellAddress 11 8 9 1 0 0 14) (cellAddress 12 8 9 11 0 0 14))))

def reserveCost (n : ℕ) := n*(4*n+5)+5

theorem reserve_one {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n d b : ℕ) (hN : m.index 0=n) (hzero : m.index 14=0)
    (hs : ∀ p, P (m.data p)) (hd : CellScratchOK d 8 9 0 0 14) :
    ∃ t, Block.Eval (fun z => ∀ p, P (z.data p)) (cellAddress d 8 9 b 0 0 14) m (reserveCost n) t ∧
      t.data = m.data ∧ (∀ p, p ≠ d → p ≠ 8 → p ≠ 9 → t.index p=m.index p) ∧
      t.index d = m.index b + n*n := by
  obtain ⟨t, he, hdata, hi, hd⟩ := cellAddress_spec (fun f => ∀ p, P (f p)) m hs d 8 9 b 0 0 14 hd
  exact ⟨t, by simpa [reserveCost,hN,hzero] using he, hdata, hi, by simpa [hN,hzero] using hd⟩

theorem birdReserveBases_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (hN : m.index 0=n) (hs : ∀ p, P (m.data p)) :
    ∃ t, Block.Eval (fun z => ∀ p, P (z.data p)) birdReserveBases m (2+3*(n*(4*n+5)+5)) t ∧
      t.data = m.data ∧ t.index 0=n ∧ t.index 1=n*n+7 ∧ t.index 11=2*(n*n)+7 ∧
      t.index 12=3*(n*n)+7 ∧ t.index 14=0 := by
  let a := m.putIndex 14 0
  let b := a.putIndex 15 7
  have ea : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.addrConst 14 0)) m 1 a :=
    Block.Eval.op_addrConst _ _ _ hs hs
  have eb : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.addrConst 15 7)) a 1 b :=
    Block.Eval.op_addrConst _ _ _ hs hs
  have b0 : b.index 0 = n := by simp [b,a,hN]
  have b14 : b.index 14 = 0 := by simp [b,a]
  have b15 : b.index 15 = 7 := by simp [b]
  obtain ⟨u, eu, du, fu, u1⟩ := reserve_one P b n 1 15 b0 b14 hs (by simp [CellScratchOK])
  have u0 := (fu 0 (by decide) (by decide) (by decide)).trans b0
  have u14 := (fu 14 (by decide) (by decide) (by decide)).trans b14
  obtain ⟨v, ev, dv, fv, v11⟩ := reserve_one P u n 11 1 u0 u14 eu.safe_end (by simp [CellScratchOK])
  have v0 := (fv 0 (by decide) (by decide) (by decide)).trans u0
  have v14 := (fv 14 (by decide) (by decide) (by decide)).trans u14
  obtain ⟨t, et, dt, ft, t12⟩ := reserve_one P v n 12 11 v0 v14 ev.safe_end (by simp [CellScratchOK])
  rw [b15] at u1
  rw [u1] at v11
  rw [v11] at t12
  refine ⟨t, ?_, dt.trans (dv.trans du), (ft 0 (by decide) (by decide) (by decide)).trans v0, ?_, ?_, ?_,
    (ft 14 (by decide) (by decide) (by decide)).trans v14⟩
  · have h := ea.seq (eb.seq (eu.seq (ev.seq et)))
    unfold birdReserveBases
    convert h using 1
    unfold reserveCost; omega
  · rw [ft 1 (by decide) (by decide) (by decide), fv 1 (by decide) (by decide) (by decide), u1]; omega
  · rw [ft 11 (by decide) (by decide) (by decide),v11]; omega
  · omega

/-- Copy scalar address 8 to scalar address 9 and advance both address registers. -/
private def copyEntry : Block :=
  .seq (.op (.load 0 8)) (.seq (.op (.store 9 0)) (.seq (.op (.incr 8 8)) (.op (.incr 9 9))))

/-- The source begins at zero and the destination cursor begins at the reserved input base. -/
def birdCopyInput : Block :=
  .seq (.op (.addrConst 8 0)) (.seq (.op (.addrCopy 9 1)) (.loop (.addrLT 9 11) copyEntry))

private structure CopyFrame {K : Type} (P : K → Prop) (base count k : ℕ) (start s : Memory K) : Prop where
  safe : ∀ p, P (s.data p)
  src : s.index 8 = k
  dst : s.index 9 = base+k
  keep : ∀ p, p ≠ 8 → p ≠ 9 → s.index p = start.index p
  copied : ∀ j < k, s.data (base+j) = start.data j
  pending : ∀ j, k ≤ j → j < count → s.data j = start.data j

private theorem copy_put_safe {K : Type} {P : K → Prop} (m : Memory K) (d : ℕ) (x : K)
    (hm : ∀ j, P (m.data j)) (hx : P x) : ∀ j, P ((m.putData d x).data j) := by
  intro j
  by_cases h : j = d
  · subst j; simpa using hx
  · simpa [h] using hm j

theorem birdCopyInput_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (base count : ℕ)
    (hb : m.index 1=base) (he : m.index 11=base+count) (hlo : count+1 ≤ base)
    (hs : ∀ j, P (m.data j)) :
    ∃ t, Block.Eval (fun z => ∀ p, P (z.data p)) birdCopyInput m (6*count+3) t ∧
      (∀ j < count, t.data (base+j) = m.data j) ∧ (∀ p, p≠8 → p≠9 → t.index p=m.index p) := by
  let a := m.putIndex 8 0
  let b := a.putIndex 9 (a.index 1)
  let I := fun k s => CopyFrame P base count k m s
  have ia : I 0 b := by
    refine ⟨hs, by simp [b,a], by simp [b,a,hb], ?_, by simp, fun _ _ _ => rfl⟩
    intro p h8 h9; simp [b,a,h8,h9]
  have step (k : ℕ) (hk : k < count) (s : Memory K) (h : I k s) :
      (Cond.addrLT 9 11).test s = true ∧
        ∃ t, Block.Eval (fun z => ∀ p, P (z.data p)) copyEntry s 4 t ∧ I (k+1) t := by
    refine ⟨?_, ?_⟩
    · have h11 := (h.keep 11 (by decide) (by decide)).trans he
      simp [Cond.test,h.dst,h11,hk]
    · let u := s.putData 0 (s.data (s.index 8))
      let v := u.putData (u.index 9) (u.data 0)
      let w := v.putIndex 8 (v.index 8+1)
      let t := w.putIndex 9 (w.index 9+1)
      have us : ∀ p, P (u.data p) := copy_put_safe s _ _ h.safe (h.safe _)
      have vs : ∀ p, P (v.data p) := copy_put_safe u _ _ us (us _)
      have e₁ : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.load 0 8)) s 1 u :=
        Block.Eval.op_load _ _ _ h.safe us
      have e₂ : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.store 9 0)) u 1 v :=
        Block.Eval.op_store _ _ _ us vs
      have e₃ : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.incr 8 8)) v 1 w :=
        Block.Eval.op_incr _ _ _ vs vs
      have e₄ : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.incr 9 9)) w 1 t :=
        Block.Eval.op_incr _ _ _ vs vs
      have write : t.data (base+k) = m.data k := by
        simp [t,w,v,u,h.dst,h.src,h.pending k (by omega) hk]
      have keep (j : ℕ) (h0 : j≠0) (hd : j≠base+k) : t.data j=s.data j := by
        simp [t,w,v,u,h.dst,hd,h0]
      refine ⟨t, e₁.seq (e₂.seq (e₃.seq e₄)), vs, by simp [t,w,v,u,h.src],
        by simp [t,w,v,u,h.dst,Nat.add_assoc], ?_, ?_, ?_⟩
      · intro p h8 h9; simp [t,w,v,u,h8,h9,h.keep p h8 h9]
      · intro j hj
        by_cases eq : j=k
        · simpa [eq] using write
        · exact (keep _ (by omega) (by omega)).trans (h.copied j (by omega))
      · intro j hlow hj
        exact (keep _ (by omega) (by omega)).trans (h.pending j (by omega) hj)
  have stop (t : Memory K) (ht : I count t) :
      (Cond.addrLT 9 11).test t = false ∧ ∀ p, P (t.data p) := by
    have h11 := (ht.keep 11 (by decide) (by decide)).trans he
    exact ⟨by simp [Cond.test,ht.dst,h11], ht.safe⟩
  obtain ⟨t, et, ht⟩ := Block.Eval.loop_invariant_exact I b count 4 ia step stop
  have ea : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.addrConst 8 0)) m 1 a :=
    Block.Eval.op_addrConst _ _ _ hs hs
  have eb : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.addrCopy 9 1)) a 1 b :=
    Block.Eval.op_addrCopy _ _ _ hs hs
  refine ⟨t, ?_, ht.copied, ht.keep⟩
  unfold birdCopyInput
  convert ea.seq (eb.seq et) using 1
  omega

/-- A dimension-independent block packing the unmodified input matrix into the
read-only table consumed by the uniform Bird determinant loops. -/
def birdInputBlock : Block := .seq birdReserveBases birdCopyInput

/-- Exact operation count (including all control steps and address arithmetic). -/
def birdInputCost (n : ℕ) : ℕ := 18*n^2 + 15*n + 20

theorem birdInputBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (n : ℕ) (flat : List K) (hs : ∀ p : ℕ, P (flat[p]?.getD 0)) :
    let m := (start [n] flat).memory
    ∃ t, Block.Eval (fun z => ∀ p, P (z.data p)) birdInputBlock m (birdInputCost n) t ∧
      t.index 0=n ∧ t.index 1=n*n+7 ∧ t.index 11=2*(n*n)+7 ∧
      t.index 12=3*(n*n)+7 ∧ t.index 14=0 ∧
      (∀ k < n*n, t.data (t.index 1+k) = flat[k]?.getD 0) ∧
      uniformMatrix n (t.index 1) t = (fun i j => flat[i.val*n+j.val]?.getD 0) := by
  let m := (start [n] flat).memory
  obtain ⟨u, eu, udata, u0, u1, u11, u12, u14⟩ := birdReserveBases_spec P m n rfl hs
  have e11 : u.index 11 = (n*n+7)+n*n := by omega
  obtain ⟨t,et,hcopy,keep⟩ := birdCopyInput_spec P u (n*n+7) (n*n) u1 e11 (by omega) eu.safe_end
  have t1 := (keep 1 (by decide) (by decide)).trans u1
  have copied (k : ℕ) (hk : k<n*n) : t.data (t.index 1+k) = flat[k]?.getD 0 := by
    rw [t1,hcopy k hk,udata]
    rfl
  refine ⟨t, ?_, (keep 0 (by decide) (by decide)).trans u0, t1,
    (keep 11 (by decide) (by decide)).trans u11, (keep 12 (by decide) (by decide)).trans u12,
    (keep 14 (by decide) (by decide)).trans u14, copied, ?_⟩
  · unfold birdInputBlock birdInputCost
    convert eu.seq et using 1
    ring
  · ext i j
    have h : i.val*n+j.val<n*n := calc
      _ < i.val*n+n := Nat.add_lt_add_left j.isLt _
      _ = (i.val+1)*n := by ring
      _ ≤ n*n := Nat.mul_le_mul_right _ i.isLt
    simpa [uniformMatrix,Nat.add_assoc] using copied _ h

end Compression
end LinearProgramming
end Optimization
end OAI
