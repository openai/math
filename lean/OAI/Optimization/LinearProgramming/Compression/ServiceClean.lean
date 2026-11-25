import OAI.Optimization.LinearProgramming.Compression.ServiceClearAddress
import OAI.Optimization.LinearProgramming.RAM.FrameClear

/-! Clear the virtual numerical solver's finite scalar and address windows without
touching a saved caller scalar. On entry scalar register 1 is already disposable. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceClean

open RAM GeneratorTable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def scalarSetup : List AddressSet := [.fix 3 0,.next 5 113,.fix 7 0]
private def clearEven : Block :=
  .seq (.op (.const 1 0)) (.seq (addressPlan scalarSetup) (Call.clearWindow true))

structure Cleaned (L F g n rank member cap : ℕ) (old t : Memory K) : Prop where
  metadata : Metadata L F g n rank member cap t
  evenData : ∀ i,2*i ≤ cap → t.data (2*i)=0
  evenIndex : ∀ i,2*i ≤ cap → t.index (2*i)=0
  oddData : ∀ i,i ≠ 0 → t.data (2*i+1)=old.data (2*i+1)
  oddIndex : ∀ i, 2*i+1 ≤ cap → 2*i+1∉savedSlots → 2*i+1 ≠ 7 → t.index (2*i+1)=0
  clearedEnd : t.index 7=2*(cap+1)

private theorem clearEven_spec (P : K → Prop) {L F g n rank member cap : ℕ} (s : Memory K)
    (metadata : Metadata L F g n rank member cap s) (zeros : ∀ i ≤ cap,i∉savedSlots → s.index i=0)
    (hs : ∀i,P (s.data i)) (hz : P 0) :
    ∃ t, Block.Eval (fun m => ∀i,P (m.data i)) clearEven s (1+(3+(6*(cap+1)+1))) t ∧
      Cleaned L F g n rank member cap s t ∧ ∀ i∈savedSlots,t.index i=s.index i := by
  let a := s.putData 1 ((0 : ℚ) : K)
  let b := applyPlan scalarSetup a
  have zero : P ((0 : ℚ) : K) := by simpa using hz
  have ha : Ingress.Good P a := Ingress.safeWrite (P := P) (m := s) (i := 1) hs zero
  have ea : Block.Eval (fun m : Memory K => ∀ i, P (m.data i)) (.op (.const 1 0)) s 1 a :=
    Block.Eval.op_const s 1 0 hs ha
  have eb : Block.Eval (fun m : Memory K => ∀ i, P (m.data i)) (addressPlan scalarSetup) a 3 b :=
    addressPlan_spec (fun f : ℕ → K => ∀i,P (f i)) scalarSetup a ha
  have b3 : b.index 3=0 := by simp [b,scalarSetup,applyPlan,AddressSet.apply]
  have b7 : b.index 7=2*0 := by simp [b,scalarSetup,applyPlan,AddressSet.apply]
  have b5 : b.index 5=cap+1 := by simp [b,scalarSetup,applyPlan,AddressSet.apply,a,metadata.capacity]
  have bf (i : ℕ) (i3 : i ≠ 3) (i5 : i ≠ 5) (i7 : i ≠ 7) : b.index i=s.index i := by
    simp [b,scalarSetup,applyPlan,AddressSet.apply,a,i3,i5,i7]
  obtain ⟨t,run,t7,t5,idx,dat⟩ := Call.clearWindow_correct (P := P) true b 0 (cap+1)
    eb.safe_end b3 (fun _ => by simp [b,scalarSetup,a,applyPlan,AddressSet.apply]) b7 b5
  have scalarInvariant : RAM.Tape.Good P = (fun m : Memory K => ∀ i, P (m.data i)) := by
    funext m
    rfl
  rw [scalarInvariant] at run
  have tfr (i : ℕ) (i3 : i ≠ 3) (i5 : i ≠ 5) (i7 : i ≠ 7) : t.index i=s.index i := by
    simpa using (idx i i5 i7).trans (by simpa using bf i i3 i5 i7)
  have metadata' : Metadata L F g n rank member cap t := metadata.transfer (fun i hi => by
    simp only [savedSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
    exact tfr i (by omega) (by omega) (by omega))
  refine ⟨t,ea.seq (eb.seq run),⟨metadata',?_,?_,?_,?_,by simpa using t7⟩,?_⟩
  · intro i hi
    have inc : Call.inEvenWindow 0 (cap+1) (2*i) := by unfold Call.inEvenWindow; omega
    simpa [inc] using dat (2*i)
  · intro i hi
    rw [tfr _ (by omega) (by omega) (by omega)]
    exact zeros _ hi (by simp only [savedSlots,List.mem_cons,List.not_mem_nil,or_false]; omega)
  · intro i hi
    have hn : ¬Call.inEvenWindow 0 (cap+1) (2*i+1) := by unfold Call.inEvenWindow; omega
    calc
      t.data (2*i+1) = a.data (2*i+1) := by
        simpa [hn, b, applyPlan_data] using dat (2*i+1)
      _ = s.data (2*i+1) := Memory.putData_ne s (by omega : 2*i+1 ≠ 1) _
  · intro i hi hm i7
    by_cases i5 : 2*i+1=5
    · simpa [i5] using t5
    by_cases i3 : 2*i+1=3
    · simpa [i3,b3] using idx 3 (by decide) (by decide)
    · exact (tfr _ i3 i5 i7).trans (zeros _ hi hm)

  · intro i hi
    simp only [savedSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
    exact tfr i (by omega) (by omega) (by omega)

def clearForNumeric : Block := .seq capture (.seq clearAddresses clearEven)

def clearCost (cap : ℕ) := 11+(addressClearCost cap+(1+(3+(6*(cap+1)+1))))

theorem clearCost_le (cap : ℕ) : clearCost cap ≤ 10*cap+150 := by
  have h := addressClearCost_le cap
  unfold clearCost
  omega

/-- All physical addresses up to the input cap are controlled before entering a
dimension-independent numerical ROM. The exterior may be an arbitrary caller heap. -/
theorem clearForNumeric_spec (P : K → Prop) (s : Memory K) (hc : 114 ≤ s.index 27)
    (hs : ∀ i,P (s.data i)) (hz : P 0) :
    ∃ t, Block.Eval (fun m => ∀ i,P (m.data i)) clearForNumeric s (clearCost (s.index 27)) t ∧
      Cleaned (s.index 7) (s.index 5) (s.index 17) (s.index 22) (s.index 19) (s.index 1) (s.index 27) s t ∧
      TableWords (s.index 14) (s.index 18) (s.index 20) (s.index 21) t := by
  obtain ⟨a,ea,ad,metadata,table⟩ := capture_spec P s hs
  obtain ⟨b,eb,bd,keep,zeros⟩ := clearAddresses_spec P a (s.index 27) hc metadata.capacity ea.safe_end
  obtain ⟨t,et,final,stays⟩ := clearEven_spec P b (metadata.transfer keep) zeros eb.safe_end hz
  refine ⟨t,ea.seq (eb.seq et),⟨final.metadata,final.evenData,final.evenIndex,?_,final.oddIndex,final.clearedEnd⟩,
    (table.transfer keep).transfer stays⟩
  intro i hi
  exact (final.oddData i hi).trans (congrFun (bd.trans ad) _)

end ServiceClean
end Compression
end LinearProgramming
end Optimization
end OAI
