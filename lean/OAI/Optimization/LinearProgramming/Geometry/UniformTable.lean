import OAI.Optimization.LinearProgramming.Compression.UniformIndex
import OAI.Optimization.LinearProgramming.RAM.Array

/-! A fixed rectangular table emitter. The callback supplies scalar 6, while
the emitter handles the loop variables, the row-major write and its cost. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Compression

def TableControl (p : ℕ) : Prop := p = 30 ∨ p = 31 ∨ p = 32 ∨ p = 33 ∨ p = 35
def TableParameter (p : ℕ) : Prop := p = 31 ∨ p = 33 ∨ p = 35
def TableScratch (p : ℕ) : Prop := p = 30 ∨ p = 32 ∨ p = 34 ∨ p = 36 ∨ p = 37
instance (p : ℕ) : Decidable (TableControl p) := by unfold TableControl; infer_instance
instance (p : ℕ) : Decidable (TableParameter p) := by unfold TableParameter; infer_instance
instance (p : ℕ) : Decidable (TableScratch p) := by unfold TableScratch; infer_instance

/-- The host may give the callback its own temporary arrays. The predicate
care selects the external scalar cells that survive the callback, including
the output area. Keep selects additional protected address registers. -/
def TableCallbackSpec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cell : Block) (P : K → Prop) (care keep : ℕ → Prop) (start : Memory K)
    (rows cols out : ℕ) (target : Matrix (Fin rows) (Fin cols) K) (bound : ℕ) : Prop :=
  ∀ (i : Fin rows) (j : Fin cols) (s : Memory K), s.AllData P →
    s.index 30 = i.val → s.index 32 = j.val →
    (∀ p, TableParameter p ∨ keep p → s.index p = start.index p) →
    (∀ p, care p → (p < out ∨ out + rows*cols ≤ p) → s.data p = start.data p) →
    ∃ t k, k ≤ bound ∧ Block.Eval (Memory.AllData P) cell s k t ∧
      t.data 6 = target i j ∧ (∀ p, care p → t.data p = s.data p) ∧
      ∀ p, TableControl p ∨ keep p → t.index p = s.index p

def uniformTableWrite (cell : Block) : Block :=
  .seq cell (.seq (cellAddress 34 36 37 35 33 30 32) (.op (.store 34 6)))

def uniformTableBlock (cell : Block) : Block := .forRowsCols 30 31 32 33 (uniformTableWrite cell)

def uniformEntryTime (rows cols bound : ℕ) := bound + rows*(4*cols+5) + 4*cols+6

def uniformTableTime (rows cols bound : ℕ) := rows*(cols*(uniformEntryTime rows cols bound+3)+5)+2

/-- View a rectangular array of actual scalar registers in row-major order. -/
def uniformRect {K : Type*} (rows cols base : ℕ) (m : Memory K) : Matrix (Fin rows) (Fin cols) K :=
  fun i j => m.data (base + i.val*cols + j.val)

/-- Relative address of a rectangle cell is in bounds. -/
theorem rectOffset_lt {m n : ℕ} (i : Fin m) (j : Fin n) : i.val*n+j.val < m*n := by
  simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using (finProdFinEquiv (i,j)).isLt

private theorem rectOffset_injective {m n : ℕ} {i i' : Fin m} {j j' : Fin n}
    (h : i.val*n+j.val = i'.val*n+j'.val) : i=i' ∧ j=j' := by
  have h' : finProdFinEquiv (i,j) = finProdFinEquiv (i',j') := by
    apply Fin.ext
    simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using h
  exact Prod.mk.inj (finProdFinEquiv.injective h')

private structure TableFrame {K : Type} (P : K → Prop) (care keep : ℕ → Prop) {m n : ℕ}
    (out filled : ℕ) (V : Matrix (Fin m) (Fin n) K) (start now : Memory K) : Prop where
  safe : now.AllData P
  idx : ∀ p, TableParameter p ∨ keep p → now.index p = start.index p
  done : ∀ i j, i.val*n+j.val < filled → now.data (out+i.val*n+j.val) = V i j
  other : ∀ p, care p → (p < out ∨ out+filled ≤ p) → now.data p = start.data p

private theorem TableFrame.putCursor {K : Type} {P : K → Prop} {care keep : ℕ→Prop}
    {m n out filled : ℕ} {V : Matrix (Fin m) (Fin n) K} {start now : Memory K}
    (h : TableFrame P care keep out filled V start now) {a val : ℕ} (ha : a=30 ∨ a=32)
    (hkeep : ∀ p, keep p → ¬ TableScratch p) : TableFrame P care keep out filled V start (now.putIndex a val) := by
  refine ⟨h.safe, ?_, h.done, h.other⟩
  intro p hp
  have hpa : p ≠ a := by
    rcases hp with hp | hp
    · unfold TableParameter at hp; omega
    · have := hkeep _ hp; unfold TableScratch at this; omega
  simpa [hpa] using h.idx p hp

private theorem uniformTableWrite_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {cell : Block} {P : K → Prop} {care keep : ℕ→Prop} {start : Memory K} {m n out B : ℕ}
    {V : Matrix (Fin m) (Fin n) K} (hc : TableCallbackSpec cell P care keep start m n out V B)
    (hkeep : ∀ p, keep p → ¬ TableScratch p) (hN : start.index 33 = n) (hOut : start.index 35 = out)
    (i : Fin m) (j : Fin n) (s : Memory K) (h : TableFrame P care keep out (i.val*n+j.val) V start s)
    (hi : s.index 30 = i.val) (hj : s.index 32 = j.val) :
    ∃ t k, k ≤ uniformEntryTime m n B ∧ Block.Eval (Memory.AllData P) (uniformTableWrite cell) s k t ∧
      t.data (out+i.val*n+j.val) = V i j ∧
      (∀ p, care p → p ≠ out+i.val*n+j.val → t.data p = s.data p) ∧
      ∀ p, TableControl p ∨ keep p → t.index p = s.index p := by
  obtain ⟨u,k,hk,ec,hv,hf,hu⟩ := hc i j s h.safe hi hj h.idx
    (fun p hp hr => h.other p hp (by have := rectOffset_lt i j; omega))
  let aq := cellAddress 34 36 37 35 33 30 32
  obtain ⟨z,ez,zd,zi,za⟩ := cellAddress_spec (fun data => ∀ p, P (data p)) u ec.safe_end
    34 36 37 35 33 30 32 (by simp [CellScratchOK])
  have h30 := (hu 30 (Or.inl (by decide))).trans hi
  have h32 := (hu 32 (Or.inl (by decide))).trans hj
  have h33 := (hu 33 (Or.inl (by decide))).trans ((h.idx 33 (Or.inl (by decide))).trans hN)
  have h35 := (hu 35 (Or.inl (by decide))).trans ((h.idx 35 (Or.inl (by decide))).trans hOut)
  rw [h35,h30,h33,h32] at za
  rw [h30,h33,h32] at ez
  let w := z.putData (z.index 34) (z.data 6)
  have ew : Block.Eval (Memory.AllData P) (.op (.store 34 6)) z 1 w :=
    Block.Eval.op_store _ _ _ ez.safe_end (Memory.AllData.putData ez.safe_end _ (ez.safe_end 6))
  have htime : k+(i.val*(4*n+5)+4*j.val+5+1) ≤ uniformEntryTime m n B := by
    have hrow := Nat.mul_le_mul_right (4*n+5) i.isLt.le
    have hcol := Nat.mul_le_mul_left 4 j.isLt.le
    unfold uniformEntryTime; omega
  refine ⟨w,_,htime,ec.seq (ez.seq ew), ?_, ?_, ?_⟩
  · change Function.update z.data (z.index 34) (z.data 6) _ = _
    rw [za, Function.update_self, zd, hv]
  · intro p hp hne
    change Function.update z.data (z.index 34) _ p = _
    rw [za, Function.update_of_ne hne, zd, hf p hp]
  · intro p hp
    change z.index p = s.index p
    have hn : p ≠ 34 ∧ p ≠ 36 ∧ p ≠ 37 := by
      rcases hp with p' | p'
      · unfold TableControl at p'; omega
      · have := hkeep _ p'; unfold TableScratch at this; omega
    exact (zi p hn.1 hn.2.1 hn.2.2).trans (hu p hp)

/-- Traverse a rectangular table using a single program independent of both
dimensions. The time includes all loop, address-generation and write costs. -/
theorem uniformTableBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cell : Block) (P : K → Prop) (care keep : ℕ → Prop) (s : Memory K) (m n out : ℕ)
    (V : Matrix (Fin m) (Fin n) K) (B : ℕ) (hc : TableCallbackSpec cell P care keep s m n out V B)
    (hkeep : ∀ p, keep p → ¬ TableScratch p)
    (hcare : ∀ i : Fin m, ∀ j : Fin n, care (out+i.val*n+j.val))
    (hm : s.index 31=m) (hn : s.index 33=n) (ho : s.index 35=out) (hs : s.AllData P) :
    ∃ t k, k ≤ uniformTableTime m n B ∧ Block.Eval (Memory.AllData P) (uniformTableBlock cell) s k t ∧
      uniformRect m n out t = V ∧
      (∀ p, care p → (p < out ∨ out+m*n ≤ p) → t.data p = s.data p) ∧
      ∀ p, TableParameter p ∨ keep p → t.index p = s.index p := by
  let frame (filled : ℕ) := TableFrame P care keep out filled V s
  let R (a : ℕ) (u : Memory K) := frame (a*n) u ∧ u.index 30 = a
  let C (a b : ℕ) (u : Memory K) := frame (a*n+b) u ∧ u.index 30=a ∧ u.index 32=b
  have initial : R 0 (s.putIndex 30 0) := by
    have h : frame 0 s := ⟨hs,fun _ _ => rfl,by simp,fun _ _ _ => rfl⟩
    exact ⟨by simpa using h.putCursor (val:=0) (Or.inl rfl) hkeep,by simp⟩
  have startRow (a : ℕ) (_ : a < m) (u : Memory K) (h : R a u) : C a 0 (u.putIndex 32 0) :=
    ⟨by simpa using h.1.putCursor (val:=0) (Or.inr rfl) hkeep,by simpa using h.2,by simp⟩
  have endRow (a : ℕ) (_ : a<m) (u : Memory K) (h : C a n u) :
      R (a+1) (u.putIndex 30 (u.index 30+1)) :=
    ⟨by simpa [Nat.succ_mul] using h.1.putCursor (val:=u.index 30+1) (Or.inl rfl) hkeep,
      by simp [h.2.1]⟩
  have step (a : ℕ) (ha : a<m) (b : ℕ) (hb : b<n) (u : Memory K) (h : C a b u) :
      ∃ t k, k ≤ uniformEntryTime m n B ∧ Block.Eval (Memory.AllData P) (uniformTableWrite cell) u k t ∧
        C a (b+1) (t.putIndex 32 (t.index 32+1)) := by
    let i : Fin m := ⟨a,ha⟩
    let j : Fin n := ⟨b,hb⟩
    obtain ⟨t,k,hk,he,hv,hf,hi'⟩ := uniformTableWrite_spec hc hkeep hn ho i j u h.1 h.2.1 h.2.2
    have hf' : frame (a*n+(b+1)) t := by
      refine ⟨he.safe_end,fun p hp => (hi' p ?_).trans (h.1.idx p hp),?_,?_⟩
      · rcases hp with hp | hp
        · exact Or.inl (by dsimp [TableControl,TableParameter] at *; omega)
        · exact Or.inr hp
      · intro i' j' hlt
        by_cases old : i'.val*n+j'.val < a*n+b
        · have hne : out+i'.val*n+j'.val ≠ out+i.val*n+j.val := by dsimp [i,j]; omega
          exact (hf _ (hcare i' j') hne).trans (h.1.done _ _ old)
        · have same : i'.val*n+j'.val = i.val*n+j.val := by dsimp [i,j]; omega
          obtain ⟨rfl,rfl⟩ := rectOffset_injective same
          exact hv
      · intro p hp range
        have ne : p ≠ out+i.val*n+j.val := by dsimp [i,j]; omega
        exact (hf p hp ne).trans (h.1.other _ hp (by omega))
    exact ⟨t,k,hk,he,hf'.putCursor (Or.inr rfl) hkeep,
      by simpa using (hi' 30 (Or.inl (by decide))).trans h.2.1,
      by simp [hi' 32 (Or.inl (by decide)),h.2.2]⟩
  obtain ⟨t,k,hk,he,h⟩ := Block.Eval.forRowsCols_invariant (body:=uniformTableWrite cell)
    30 31 32 33 m n (uniformEntryTime m n B) R C s hs initial
    (fun _ _ h => ⟨h.1.safe,h.2,(h.1.idx 31 (Or.inl (by decide))).trans hm⟩) startRow
    (fun _ _ _ h => ⟨h.1.safe,h.2.2,(h.1.idx 33 (Or.inl (by decide))).trans hn⟩) step endRow
  exact ⟨t,k,hk,he,by ext i j; exact h.1.done i j (rectOffset_lt i j),h.1.other,h.1.idx⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
