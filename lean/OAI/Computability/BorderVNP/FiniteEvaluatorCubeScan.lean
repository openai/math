import OAI.Computability.BorderVNP.RoutingISAFiniteScalarBatch

/-! # Finite-field scalar calls on the owned cube vertices

The native scan reads the vertex count from frame word 46 and the start of the
stored scalar column from frame word 71. Each iteration supplies a single
consecutive memory word to private routine one.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeScan

open VPVNP.BurstRAM RoutingISA RoutingISA.CellDispatch
open private noBursts from OAI.Computability.BorderVNP.RoutingISAFiniteScalarBatch

/-- Load the owned vertex count and scalar pointer, and initialize the row counter. -/
def setup : Code := .block [readFrame 42 62 63 46,readFrame 41 62 63 71,.constant 43 0,.constant 47 1]

/-- Each successful private return advances both the pointer and the row counter. -/
def body : Code := .block [.call 1 41 47,.binary .add 41 41 47,.binary .add 43 43 47]

/-- Fixed code of the scalar scan over the local vertex column. -/
def code : Code := .seq setup (.whileLt 43 42 body)

/-- The private event at address `a` records the actual previous memory word. -/
def event {w : ℕ} (m : Memory w) (a : ℕ) : TeamRAM.Event w :=
  FiniteScalarCall.event a [m a]

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The cursor at the terminating guard may wrap when the column fills the
word address space. Every address supplied to the routine is in range. -/
private def Ready (base count i : ℕ) (s : Bank w) : Prop :=
  (s 41).val = (base+i) % 2^w ∧ (s 42).val=count ∧ (s 43).val=i ∧ (s 47).val=1

private theorem setup_run {base count : ℕ} (s : Bank w) (m : Memory w)
    (frame : (pub 0).val+71 < 2^w) (num : (m ((pub 0).val+46)).val=count)
    (ptr : (m ((pub 0).val+71)).val=base) :
    ∃ es t, Runs pub mac setup s m es t m ∧ traceCost es ≤ setup.slots ∧ Ready base count 0 t := by
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [setup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,readings]
    have pos : w ≠ 0 := by rintro rfl; simp at frame
    omega
  obtain ⟨es,t,r,c,hr⟩ := setup.runReadOnly pub mac m s safe
  refine ⟨es,t,r,c,?_⟩
  change readings t 41 = _ ∧ readings t 42 = _ ∧ readings t 43 = _ ∧ readings t 47 = _
  have fit : base < 2^w := ptr ▸ (m ((pub 0).val+71)).isLt
  rw [hr]
  simp (config := {decide := true}) [setup,readFrame,Code.block,Code.evalNat,addressOp,readings,num,ptr,Nat.mod_eq_of_lt fit]

private theorem body_run {base count i : ℕ} (s : Bank w) (m : Memory w) (ready : Ready base count i s)
    (lt : i<count) (space : base+count ≤ 2^w)
    (scalar : ∀ bs, mac 1 [m (base+i)] bs = if bs.isEmpty then some .plus else none) :
    let es := [event m (base+i),tick w,tick w]
    ∃ t, Runs pub mac body s m es t m ∧ Ready base count (i+1) t ∧
      ∀ fs z mz, Runs pub mac body s m fs z mz → fs=es ∧ z=t ∧ mz=m := by
  intro es
  obtain ⟨ptr,num,idx,one⟩ := ready
  rw [Nat.mod_eq_of_lt (by omega)] at ptr
  have read : TeamRAM.previous m (.burst (base+i) 1) = [m (base+i)] := rfl
  have call : Runs pub mac (.call 1 41 47) s m [event m (base+i)] s m := by
    rw [private_iff]
    dsimp only
    rw [ptr,one,read]
    exact ⟨by omega,rfl,rfl,([], .plus),by simpa only [List.isEmpty_nil,ite_true] using scalar [],rfl⟩
  let u := Function.update s (41 : Reg) (PrivateRAM.BinaryOp.add.eval (s 41) (s 47))
  let t := Function.update u (43 : Reg) (PrivateRAM.BinaryOp.add.eval (u 43) (u 47))
  have a : Runs pub mac (.binary .add 41 41 47) s m [tick w] u m := .localStep _ rfl rfl
  have b : Runs pub mac (.binary .add 43 43 47) u m [tick w] t m := .localStep _ rfl rfl
  refine ⟨t,call.seq (a.seq b),?_,?_⟩
  · have limit := num ▸ (s 42).isLt
    simp (config := {decide := true}) [Ready,u,t,PrivateRAM.BinaryOp.eval,Fin.val_add,
      ptr,num,idx,one,Nat.mod_eq_of_lt (by omega : i+1 < 2^w),Nat.add_assoc]
  · intro fs z mz r
    obtain ⟨v,mv,gs,hs,rfl,first,rest⟩ := Runs.seq_iff.mp r
    obtain ⟨_,rfl,rfl,o,path,rfl⟩ := private_iff.mp first
    rw [ptr,one,read,scalar] at path
    obtain ⟨choices,sign⟩ : o.1=[] ∧ o.2=.plus := by cases h : o.1 <;> simp_all
    obtain ⟨rfl,rfl,rfl⟩ := (a.seq b).unique_of_deterministic (by decide) rest
    rw [ptr,one,read,choices,sign]
    exact ⟨rfl,rfl,rfl⟩

private theorem loop {base count : ℕ} (m : Memory w) (space : base+count ≤ 2^w)
    (scalar : ∀ i<count, ∀ bs, mac 1 [m (base+i)] bs = if bs.isEmpty then some .plus else none)
    (i : ℕ) (hi : i≤count) (s : Bank w) (ready : Ready base count i s) :
    ∃ es t, Runs pub mac (.whileLt 43 42 body) s m es t m ∧ traceCost es = 5*(count-i)+1 ∧
      FiniteScalarBatch.bursts es = (List.range' i (count-i)).map (fun j => event m (base+j)) ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      ∀ fs z mz, Runs pub mac (.whileLt 43 42 body) s m fs z mz → fs=es ∧ z=t ∧ mz=m := by
  have num := ready.2.1
  have idx := ready.2.2.1
  by_cases done : i=count
  · rw [done]
    have guard : ¬ s 43 < s 42 := show ¬ (s 43).val < (s 42).val by omega
    refine ⟨_,s,.whileDone guard,?_,?_,?_,fun _ _ _ r => while_last r guard⟩
    · simp only [Nat.sub_self,Nat.mul_zero,Nat.zero_add]; rfl
    · simp [FiniteScalarBatch.bursts,FiniteScalarBatch.isBurst,tick]
    · simp [tick]
  · have lt : i<count := by omega
    have guard : s 43 < s 42 := show (s 43).val < (s 42).val by omega
    obtain ⟨u,first,next,unique⟩ := body_run (pub:=pub) s m ready lt space (scalar i lt)
    obtain ⟨ys,t,rest,cost,bursts,clean,only⟩ := loop m space scalar (i+1) lt u next
    refine ⟨_,t,.whileStep guard first rest,?_,?_,?_,?_⟩
    · change 1+(2+(1+(1+traceCost ys))) = _
      omega
    · have h : count-i = (count-(i+1))+1 := by omega
      change event m (base+i) :: FiniteScalarBatch.bursts ys = _
      rw [bursts,h,List.range'_succ,List.map_cons]
    · intro e he
      simp only [List.cons_append,List.nil_append,List.mem_cons] at he
      rcases he with rfl | rfl | rfl | rfl | h
      all_goals first | exact ⟨rfl,rfl⟩ | exact clean _ h
    · intro fs z mz r
      obtain ⟨gs,b,mb,zs,rfl,step,tailRun⟩ := while_next r guard
      obtain ⟨rfl,rfl,rfl⟩ := unique _ _ _ step
      obtain ⟨rfl,rfl,rfl⟩ := only _ _ _ tailRun
      exact ⟨rfl,rfl,rfl⟩
termination_by count-i

/-- All returning runs have the same trace, terminal bank, and original memory.
Their ordered bursts call routine one on exactly the stored local scalar words.
The charge is at most ten setup ticks, five ticks per word, and one final guard. -/
theorem run {base count : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (frame : (pub 0).val+71 < 2^w)
    (num : (m ((pub 0).val+46)).val=count) (ptr : (m ((pub 0).val+71)).val=base)
    (space : base+count ≤ 2^w)
    (scalar : ∀ i<count, ∀ bs, mac 1 [m (base+i)] bs = if bs.isEmpty then some .plus else none) :
    ∃ es t, Runs pub mac code s m es t m ∧ traceCost es ≤ setup.slots+5*count+1 ∧
      FiniteScalarBatch.bursts es = (List.range count).map (fun i => event m (base+i)) ∧
      (∀ e ∈ es, e.choices=[] ∧ e.sign=.plus) ∧
      ∀ fs z mz, Runs pub mac code s m fs z mz → fs=es ∧ z=t ∧ mz=m := by
  obtain ⟨gs,u,first,setupCost,ready⟩ := setup_run (mac:=mac) s m frame num ptr
  obtain ⟨ys,t,rest,cost,bursts,clean,only⟩ := loop (pub:=pub) m space scalar 0 (Nat.zero_le _) u ready
  refine ⟨_,t,first.seq rest,?_,?_,?_,?_⟩
  · rw [show traceCost (gs++ys) = traceCost gs+traceCost ys from VPVNP.RAMBuckets.cost_append ..]
    omega
  · have empty := noBursts first (by decide)
    change FiniteScalarBatch.bursts (gs++ys) = _
    rw [show FiniteScalarBatch.bursts (gs++ys) = FiniteScalarBatch.bursts gs++FiniteScalarBatch.bursts ys from List.filter_append ..,
      empty,List.nil_append,bursts]
    simp [List.range_eq_range']
  · exact fun e h => (List.mem_append.mp h).elim (first.unsigned_events (by decide) e) (clean e)
  · intro fs z mz r
    obtain ⟨v,mv,ts,ss,rfl,init,last⟩ := Runs.seq_iff.mp r
    obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic (by decide) init
    obtain ⟨rfl,rfl,rfl⟩ := only _ _ _ last
    exact ⟨rfl,rfl,rfl⟩

/-- Every native instruction of the scan respects a cap of one extra word. -/
theorem burst_bound {m : Memory w} {base count : ℕ} {es : List (TeamRAM.Event w)}
    (calls : FiniteScalarBatch.bursts es = (List.range count).map (fun i => event m (base+i))) :
    ∀ e ∈ es, e.action.extra ≤ 1 := by
  intro e he
  cases ha : e.action with
  | ordinary => exact Nat.zero_le 1
  | burst a n =>
    have h : e ∈ FiniteScalarBatch.bursts es :=
      List.mem_filter.mpr ⟨he,by simp [FiniteScalarBatch.isBurst,ha]⟩
    rw [calls] at h
    obtain ⟨i,_,hi⟩ := List.mem_map.mp h
    rw [← hi] at ha
    cases ha
    exact le_rfl

end FiniteEvaluator.CubeScan

end BorderVNP
end Computability
end OAI
