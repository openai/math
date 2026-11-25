import OAI.Optimization.LinearProgramming.Recovery.PairBuilderProgram

/-! Framed header invariants for the three matrix workers and their two result orders. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder
open RAM RAM.Call RAM.Callable RAM.Tape Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

variable {K : Type}
variable {h n k s a b : ℕ} {l : Layout h n} {m t : Memory K}

structure Internal (l : Layout h n) (k s a b : ℕ) (m : Memory K) : Prop extends InputRegs l m where
  cap : m.index 210=capacity h n l.previous
  firstRank : m.index 206=k
  lastRank : m.index 207=s
  firstBase : m.index 211=a
  lastBase : m.index 212=b
  firstFits : k ≤ n
  lastFits : s ≤ n
  firstBaseFits : a ≤ l.scratch
  lastBaseFits : b ≤ l.scratch

theorem InputRegs.transfer (v : InputRegs l m) (eq : ∀j : Fin 220,j∈({200,201,202,203,204,205}:Finset (Fin 220))→t.index j=m.index j) : InputRegs l t :=
  ⟨(eq 200 (by decide)).trans v.height,(eq 201 (by decide)).trans v.width,(eq 202 (by decide)).trans v.source,
   (eq 203 (by decide)).trans v.target,(eq 204 (by decide)).trans v.workspace,(eq 205 (by decide)).trans v.previous⟩

theorem Internal.transfer (v : Internal l k s a b m) (eq : ∀j : Fin 220,j∈usable→t.index j=m.index j) : Internal l k s a b t :=
  ⟨v.toInputRegs.transfer (fun j hj=>eq j ((by decide : ({200,201,202,203,204,205}:Finset (Fin 220)) ⊆ usable) hj)),
  (eq 210 (by decide)).trans v.cap,(eq 206 (by decide)).trans v.firstRank,(eq 207 (by decide)).trans v.lastRank,
  (eq 211 (by decide)).trans v.firstBase,(eq 212 (by decide)).trans v.lastBase,v.firstFits,v.lastFits,v.firstBaseFits,v.lastBaseFits⟩

private theorem internal_other (j : Fin 220) (hj : j∈usable) : 180 ≠ j.val ∧ 181 ≠ j.val ∧ 183 ≠ j.val ∧ 1 ≠ j.val := by
  simp only [usable, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem Internal.traced (v : Internal l k s a b m) (same : ∀p,p≠180→p≠181→p≠183→t.index p=m.index p) : Internal l k s a b t :=
  v.transfer (fun j hj=>same j (internal_other j hj).1.symm (internal_other j hj).2.1.symm (internal_other j hj).2.2.1.symm)

theorem Internal.unchanged (v : Internal l k s a b m) (i j : ℕ) (eq : ∀p : Fin 220,p∈usable → p.val≠i) : Internal l k s a b (m.putIndex i j) :=
  v.transfer (fun p hp=>Memory.putIndex_ne m (eq p hp) j)

theorem Internal.tagged (v : Internal l k s a b m) : Internal l k s a b (m.putIndex 1 0) :=
  v.unchanged _ _ (fun i hi=>(internal_other i hi).2.2.2.symm)

theorem Internal.pointed (v : Internal l k s a b m) (src : ℕ) : Internal l k s a b (m.putIndex 180 src) :=
  v.unchanged _ _ (fun i hi=>(internal_other i hi).1.symm)

private theorem base_kept (which : ℕ) (ok : which=206 ∨ which=207) :
    ∀p : Fin 220,p∈({200,201,202,203,204,205}:Finset (Fin 220))→p.val≠which := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> rcases ok with rfl|rfl <;> decide

theorem Internal.setFirst (v : Internal l k s a b m) (u : ℕ) (fit : u ≤ n) : Internal l u s a b (m.putIndex 206 u) := by
  refine ⟨v.toInputRegs.transfer (fun j hj=>Memory.putIndex_ne m (base_kept 206 (Or.inl rfl) j hj) u),?_,?_,?_,?_,?_,fit,v.lastFits,v.firstBaseFits,v.lastBaseFits⟩
  all_goals simp [v.cap,v.lastRank,v.firstBase,v.lastBase]

theorem Internal.setLast (v : Internal l k s a b m) (u : ℕ) (fit : u ≤ n) : Internal l k u a b (m.putIndex 207 u) := by
  refine ⟨v.toInputRegs.transfer (fun j hj=>Memory.putIndex_ne m (base_kept 207 (Or.inr rfl) j hj) u),?_,?_,?_,?_,?_,v.firstFits,fit,v.firstBaseFits,v.lastBaseFits⟩
  all_goals simp [v.cap,v.firstRank,v.firstBase,v.lastBase]

structure MetaEffect (p : Phase) (m t : Memory K) : Prop where
  data : t.data=m.data
  updated : ∀i : Fin 220,t.index i=(plan p).output (fun j=>m.index j) i
  kept : ∀i : Fin 220,i∉written (plan p) → t.index i=m.index i
  held : ∀i,Held i→t.index i=m.index i

theorem MetaEffect.kept_on {p : Phase} (e : MetaEffect p m t) {registers : Finset (Fin 220)}
    (empty : registers ∩ written (plan p) = ∅) {i : Fin 220} (hi : i ∈ registers) : t.index i = m.index i := by
  apply e.kept i
  intro writtenHere
  have both : i ∈ registers ∩ written (plan p) := Finset.mem_inter.mpr ⟨hi, writtenHere⟩
  rw [empty] at both
  exact Finset.notMem_empty i both

theorem meta_run [Field K] [LinearOrder K] [IsStrictOrderedRing K] {p : Phase} (native m : Memory K) (P : K→Prop) (hn : native.AllData P) (hm : m.AllData P)
    (B : ℕ) (fit : ∀i∈needed (plan p),m.index i ≤ B) :
    ∃t,(«meta» p).Run P (Odd.memory native m) (metaBudget.eval B) (Odd.memory native t) ∧ t.AllData P ∧ MetaEffect p m t := by
  obtain ⟨t,k,run,clock,safe,data,lo,unchanged,hi⟩:=header_run (plan p) (meta_static p) native m P hn hm B fit
  refine ⟨t,run.mono (clock.trans (meta_budget p B)),safe,data,lo,unchanged,?_⟩
  intro i hh
  by_cases small : i<220
  · exact unchanged ⟨i,small⟩ (keeps_held p ⟨i,small⟩ hh)
  · exact hi i (by rcases hh with h|h|h|h <;> omega)

/-- Relate a finite plan register to its physical address before applying its stored value. -/
theorem bound_read (m : Memory K) (slot : Fin 220) {address value bound : ℕ}
    (read : m.index address = value) (physical : slot.val = address) (fit : value ≤ bound) :
    m.index slot ≤ bound :=
  (congrArg m.index physical).le.trans (read.le.trans fit)

theorem Internal.bound (v : Internal l k s a b m) (i : Fin 220) (hi : i∈usable) : m.index i ≤ limit l := by
  obtain ⟨⟨vh,vn,vsrc,vout,vwork,vprev⟩,vCap,vk,vs,va,vb,hk,hs,ha,hb⟩:=v
  have h₁ := l.sourceRoom; have h₂ := l.outputRoom; have hp:=old_fits h n l.previous
  simp only [usable,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact bound_read m 200 vh (by decide) (by unfold limit; omega)
  · exact bound_read m 201 vn (by decide) (by unfold limit; omega)
  · exact bound_read m 202 vsrc (by decide) (by unfold limit; omega)
  · exact bound_read m 203 vout (by decide) (by unfold limit; omega)
  · exact bound_read m 204 vwork (by decide) (by unfold limit; omega)
  · exact bound_read m 205 vprev (by decide) (by unfold limit; omega)
  · exact bound_read m 206 vk (by decide) (by unfold limit; omega)
  · exact bound_read m 207 vs (by decide) (by unfold limit; omega)
  · exact bound_read m 210 vCap (by decide) (by unfold limit; omega)
  · exact bound_read m 211 va (by decide) (by unfold limit; omega)
  · exact bound_read m 212 vb (by decide) (by unfold limit; omega)

theorem Internal.metaRun [Field K] [LinearOrder K] [IsStrictOrderedRing K] (v : Internal l k s a b m) (p : Phase) (native : Memory K) (P : K→Prop)
    (hn : native.AllData P) (hm : m.AllData P) :
    ∃t,(«meta» p).Run P (Odd.memory native m) (metaBudget.eval (limit l)) (Odd.memory native t) ∧ t.AllData P ∧ MetaEffect p m t :=
  meta_run native m P hn hm _ (fun i hi=>v.bound i (needed_usable p hi))

def Quiet : Phase→Prop
  | .init | .place _ => False
  | _ => True

theorem MetaEffect.quiet {p : Phase} (u : Quiet p) (v : Internal l k s a b m) (e : MetaEffect p m t) : Internal l k s a b t := by
  have empty : usable ∩ written (plan p) = ∅ := by
    cases p with | init | place => contradiction | finish r => cases r <;> decide | _ => decide
  exact v.transfer (fun _ hj => e.kept_on empty hj)

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
