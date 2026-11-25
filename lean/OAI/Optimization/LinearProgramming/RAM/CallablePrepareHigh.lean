import OAI.Optimization.LinearProgramming.RAM.CallablePrepareStep

/-! The high-bank pass copies or clears every cell from logical index five up
to the declared finite footprint. The low five even locations are used as scratch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

def prepareHighInit : Block :=
  .seq (.op (.addrConst 0 11)) (.seq (copyIndexPlus 2 111 10)
    (.seq (copyIndexPlus 4 115 10) (.op (.addrConst 6 10))))

def prepareHigh : Block := .seq prepareHighInit (.loop (.addrLT 0 121) prepareStep)

def highInitMem {K : Type*} (m : Memory K) (sb ab : ℕ) : Memory K :=
  (((m.putIndex 0 11).putIndex 2 (2*sb+1+10)).putIndex 4 (2*ab+1+10)).putIndex 6 10

structure HighHeads {K : Type*} (m : Memory K) (sb ab j : ℕ) : Prop where
  counter : m.index 0 = 2*j+1
  scalar : m.index 2 = 2*(sb+j)+1
  address : m.index 4 = 2*(ab+j)+1
  dest : m.index 6 = 2*j

def entryReady {K : Type*} [Zero K] (m : Memory K) (xs : List K) (dims : List ℕ)
    (j : ℕ) : Prop := m.data (2*j)=(xs[j]?.getD 0) ∧ m.index (2*j)=2*(dims[j]?.getD 0)

theorem HighHeads.advance {K : Type*} (m : Memory K) (sb ab j : ℕ) (x : K) (v : ℕ)
    (h : HighHeads m sb ab j) (hj : 5≤j) :
    HighHeads (afterPrepareStep m j x v) sb ab (j+1) := by
  obtain ⟨h0,h2,h4,h6⟩ := h
  have p0 : 0≠2*j := by omega
  have p2 : 2≠2*j := by omega
  have p4 : 4≠2*j := by omega
  have p6 : 6≠2*j := by omega
  constructor <;> simp_all [afterPrepareStep,advanceMem,addressStepMem,scalarStepMem] <;> omega

theorem afterPrepareStep_value {K : Type*} [Zero K] (m : Memory K) (xs : List K) (dims : List ℕ)
    (j : ℕ) (hj : 5≤j) :
    entryReady (afterPrepareStep m j (xs[j]?.getD 0) (dims[j]?.getD 0)) xs dims j := by
  have p0 : 2*j≠0 := by omega
  have p2 : 2*j≠2 := by omega
  have p4 : 2*j≠4 := by omega
  have p6 : 2*j≠6 := by omega
  constructor <;> simp_all [afterPrepareStep,advanceMem,addressStepMem,scalarStepMem]

theorem afterPrepareStep_other {K : Type*} (m : Memory K) (j q : ℕ) (x : K) (v : ℕ)
    (hq : 5≤q) (hne : q≠j) :
    (afterPrepareStep m j x v).data (2*q)=m.data (2*q) ∧
    (afterPrepareStep m j x v).index (2*q)=m.index (2*q) := by
  have p0 : 2*q≠0 := by omega
  have p2 : 2*q≠2 := by omega
  have p4 : 2*q≠4 := by omega
  have p6 : 2*q≠6 := by omega
  have p8 : 2*q≠8 := by omega
  have pq : 2*q≠2*j := by omega
  constructor <;> simp_all [afterPrepareStep,advanceMem,addressStepMem,scalarStepMem]

theorem highInit_heads {K : Type*} (m : Memory K) (sb ab : ℕ) :
    HighHeads (highInitMem m sb ab) sb ab 5 := by
  constructor <;> simp [highInitMem] <;> omega

theorem highInit_odd {K : Type*} (m : Memory K) (sb ab : ℕ) :
    OddFrame m (highInitMem m sb ab) :=
  ((((OddFrame.refl m).putIndex 0 _).putIndex 1 _).putIndex 2 _).putIndex 3 _

theorem highInit_other {K : Type*} (m : Memory K) (sb ab q : ℕ) (hq : 5≤q) :
    (highInitMem m sb ab).data (2*q)=m.data (2*q) ∧
    (highInitMem m sb ab).index (2*q)=m.index (2*q) := by
  have p0 : 2*q≠0 := by omega
  have p2 : 2*q≠2 := by omega
  have p4 : 2*q≠4 := by omega
  have p6 : 2*q≠6 := by omega
  constructor <;> simp_all [highInitMem]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem prepareHighInit_spec (m : Memory K) (sb ab B : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hs : m.AllData P) :
    Block.Eval (Memory.AllData P) prepareHighInit m 24 (highInitMem m sb ab) := by
  let a := m.putIndex 0 11
  let b := a.putIndex 2 (a.index 111+10)
  let c := b.putIndex 4 (b.index 115+10)
  have h := (Block.Eval.op_addrConst (safe := Memory.AllData P) m 0 11 hs hs).seq
    ((copyIndexPlus_spec a 2 111 10 hs).seq ((copyIndexPlus_spec b 4 115 10 hs).seq
      (Block.Eval.op_addrConst (safe := Memory.AllData P) c 6 10 hs hs)))
  simpa [prepareHighInit,highInitMem,c,b,a,src.scalarBase,src.addressBase] using h

/-- Every high cell is set to the corresponding raw input word (or its zero extension).
The source address is doubled, and the caller's odd bank is preserved in full. -/
theorem prepareHigh_spec (m : Memory K) (sb ab B : ℕ) (xs : List K) (dims : List ℕ)
    (src : PrepareSource m sb ab B xs dims) (hs : m.AllData P) (hz : P 0)
    (hxs : xs.length≤B) (hdims : dims.length≤B)
    (tail : ∀ q, B≤q → m.data (2*q)=0 ∧ m.index (2*q)=0) :
    ∃ t k, k ≤ 19*B+25 ∧ Block.Eval (Memory.AllData P) prepareHigh m k t ∧
      OddFrame m t ∧ ∀ q, 5≤q → entryReady t xs dims q := by
  let I (i : ℕ) (s : Memory K) : Prop :=
    HighHeads s sb ab (5+i) ∧ OddFrame m s ∧ s.AllData P ∧
    (∀ q, 5≤q → q<5+i → entryReady s xs dims q) ∧
    (∀ q, 5≤q → B≤q → s.data (2*q)=0 ∧ s.index (2*q)=0)
  let a := highInitMem m sb ab
  have init := prepareHighInit_spec m sb ab B xs dims src hs
  have start : I 0 a := by
    refine ⟨highInit_heads ..,highInit_odd ..,init.safe_end,fun q hq he => by omega,?_⟩
    intro q hq he
    obtain ⟨hd,hi⟩ := highInit_other m sb ab q hq
    exact ⟨hd.trans (tail q he).1,hi.trans (tail q he).2⟩
  have body : ∀ i < B-5, ∀ s, I i s → (Cond.addrLT 0 121).test s=true ∧
      ∃ t k, k≤17 ∧ Block.Eval (Memory.AllData P) prepareStep s k t ∧ I (i+1) t := by
    intro i hi s hsI
    obtain ⟨head,odd,safe,done,out⟩ := hsI
    let j := 5+i
    let t := afterPrepareStep s j (xs[j]?.getD 0) (dims[j]?.getD 0)
    have sj := src.ofOdd odd
    have hj : j<B := by dsimp [j]; omega
    have five : 5≤j := by dsimp [j]; omega
    have cond : (Cond.addrLT 0 121).test s=true := by
      simp [Cond.test,head.counter,sj.bound]; omega
    obtain ⟨k,hk,run⟩ := prepareStep_spec s sb ab B j xs dims sj head.counter head.scalar
      head.address head.dest safe hz
    refine ⟨cond,t,k,hk,run,head.advance s sb ab j _ _ five,odd.trans (odd_afterPrepareStep ..),run.safe_end,?_,?_⟩
    · intro q hq he
      by_cases eq : q=j
      · subst q; exact afterPrepareStep_value s xs dims j five
      · have other := afterPrepareStep_other s j q (xs[j]?.getD 0) (dims[j]?.getD 0) hq eq
        obtain ⟨hd,ha⟩ := done q hq (by dsimp [j] at eq; omega)
        exact ⟨other.1.trans hd,other.2.trans ha⟩
    · intro q hq he
      have other := afterPrepareStep_other s j q (xs[j]?.getD 0) (dims[j]?.getD 0) hq (by omega)
      exact ⟨other.1.trans (out q hq he).1,other.2.trans (out q hq he).2⟩
  have stop : ∀ s, I (B-5) s → (Cond.addrLT 0 121).test s=false ∧ s.AllData P := by
    intro s h
    have bd := (src.ofOdd h.2.1).bound
    exact ⟨by simp [Cond.test,h.1.counter,bd]; omega,h.2.2.1⟩
  obtain ⟨t,k,hk,ev,ht⟩ := Block.Eval.loop_invariant I a (B-5) 17 start body stop
  refine ⟨t,24+k,by omega,init.seq ev,ht.2.1,?_⟩
  intro q hq
  by_cases he : q<5+(B-5)
  · exact ht.2.2.2.1 q hq he
  · have hB : B≤q := by omega
    obtain ⟨hd,hi⟩ := ht.2.2.2.2 q hq hB
    simp [entryReady,hd,hi,List.getElem?_eq_none (hxs.trans hB),List.getElem?_eq_none (hdims.trans hB)]

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
