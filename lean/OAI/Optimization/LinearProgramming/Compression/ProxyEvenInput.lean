import OAI.Optimization.LinearProgramming.Compression.ProxyEvenDoubles
import OAI.Optimization.LinearProgramming.Compression.ProxyEvenCopy
import OAI.Optimization.LinearProgramming.Compression.ServiceClearAddress

/-! Assemble the physical even bank for the normal numerical proxy service call. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceFill

variable {K : Type*}

open RAM GeneratorTable

/-- Scratch pointers, including the two words that may hold the outer capacity. -/
def clearedCursors : List ℕ := [5,7,11,13,15,17,113]

private def finishPlan : List AddressSet :=
  [.read 1 101, .read 3 109, .fix 5 0, .fix 7 0, .fix 11 0, .fix 13 0, .fix 15 0,
   .fix 17 0, .fix 113 0]

private def finishInput (s : Memory K) : Memory K := applyPlan finishPlan s

private theorem finish_values (s : Memory K) :
    (finishInput s).index 1 = s.index 101 ∧ (finishInput s).index 3 = s.index 109 ∧
    ∀ j ∈ clearedCursors, (finishInput s).index j = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [finishInput,finishPlan,applyPlan,AddressSet.apply]
  · simp [finishInput,finishPlan,applyPlan,AddressSet.apply]
  · intro j hj
    simp only [clearedCursors,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [finishInput,finishPlan,applyPlan,AddressSet.apply]

private theorem finish_frame (s : Memory K) (j : ℕ) (h₁ : j ≠ 1) (h₃ : j ≠ 3)
    (h : j ∉ clearedCursors) : (finishInput s).index j = s.index j := by
  simp only [clearedCursors,List.mem_cons,List.not_mem_nil,or_false,not_or] at h
  simp (disch := omega) [finishInput,finishPlan,applyPlan,AddressSet.apply]

/-- The source may hold arbitrary capacity-sized values at physical indices 7 and
113. Both are reset after every output word has been produced. -/
def evenInput : Block := .seq prepareEvenInput (.seq copyEvenInput (addressPlan finishPlan))

def oddAddressBudget (live n : ℕ) : ℕ := max (2*live+114) (2*n+114)

def evenInputSteps (n g member rank F : ℕ) : ℕ := 4*(n+g+member+rank+F)+9*g+33

theorem evenInputSteps_le (n g member rank F live : ℕ) (hF : F ≤ live) (hr : rank ≤ g)
    (hg : g ≤ live) (hm : member ≤ 1) : evenInputSteps n g member rank F ≤ 40*(n+live+1) := by
  unfold evenInputSteps
  omega

/-- The virtual scalar and address tapes match the usual numerical entry while the
odd bank keeps the physical caller's data and a bounded return interface. -/
structure EvenReady {K : Type*} [Zero K] (live g n rank member cap : ℕ)
    (mag : Fin (g+1) → K) (s t : Memory K) : Prop where
  evenScalar (i : ℕ) : 2*i ≤ cap → t.data (2*i) = (start [n,g,member,rank] (List.ofFn mag)).data i
  evenAddress (i : ℕ) : 2*i ≤ cap → t.index (2*i) = 2*(start [n,g,member,rank] (List.ofFn mag)).index i
  oddScalar (i : ℕ) : t.data (2*i+1) = s.data (2*i+1)
  oddAddress (i : ℕ) : 2*i+1 ≤ cap → t.index (2*i+1) ≤ oddAddressBudget live n
  liveWord : t.index 1 = live
  rankWord : t.index 3 = rank
  scratchClear (j : ℕ) : j ∈ clearedCursors → t.index j = 0
  oddKept (j : ℕ) : j ∈ ([93,95,97,99] : List ℕ) → t.index j = s.index j
  evenScalarTail (i : ℕ) : g < i → t.data (2*i) = s.data (2*i)
  evenAddressTail (i : ℕ) : 4 ≤ i → t.index (2*i) = s.index (2*i)

theorem EvenReady.tableWords {K : Type*} [Zero K] {live g n rank member cap base stride stop next : ℕ}
    {mag : Fin (g+1) → K} {s t : Memory K} (ready : EvenReady live g n rank member cap mag s t)
    (table : ServiceClean.TableWords base stride stop next s) : ServiceClean.TableWords base stride stop next t :=
  ⟨(ready.oddKept 93 (by decide)).trans table.baseWord, (ready.oddKept 95 (by decide)).trans table.strideWord,
   (ready.oddKept 97 (by decide)).trans table.stopWord, (ready.oddKept 99 (by decide)).trans table.nextWord⟩

/-- A cleared sparse incoming odd bank meets the upper bound required by the filler. -/
theorem oddAddressBudget_of_clear {K : Type*} (s : Memory K) (live F g n rank member cap : ℕ)
    (metadata : ServiceClean.Metadata live F g n rank member cap s)
    (hF : F ≤ live) (hr : rank ≤ g) (hg : g ≤ live) (hm : member ≤ 1)
    (table : ∀ j ∈ ([93,95,97,99] : List ℕ), s.index j ≤ live)
    (cleared : ∀ i, 2*i+1 ≤ cap → 2*i+1 ∉ ServiceClean.savedSlots → 2*i+1 ≠ 7 → s.index (2*i+1) = 0) :
    ∀ i, 2*i+1 ≤ cap → 2*i+1 ≠ 7 → 2*i+1 ≠ 113 → s.index (2*i+1) ≤ oddAddressBudget live n := by
  intro i hi h7 h113
  have hL : live ≤ oddAddressBudget live n := by unfold oddAddressBudget; omega
  by_cases saved : 2*i+1 ∈ ServiceClean.savedSlots
  · simp only [ServiceClean.savedSlots,List.mem_cons,List.not_mem_nil,or_false] at saved
    rcases saved with p|p|p|p|p|p|p|p|p|p|p <;> try contradiction
    all_goals rw [p]
    all_goals first
      | exact (table _ (by decide)).trans hL
      | exact metadata.length.le.trans hL
      | exact metadata.source.le.trans (hF.trans hL)
      | exact metadata.count.le.trans (hg.trans hL)
      | (rw [metadata.columns]; unfold oddAddressBudget; omega)
      | exact metadata.position.le.trans (hr.trans (hg.trans hL))
      | (rw [metadata.present]; unfold oddAddressBudget; omega)
  · rw [cleared i hi saved h7]
    exact Nat.zero_le _

theorem evenInput_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (live F g n rank member cap : ℕ) (mag : Fin (g+1) → K)
    (metadata : ServiceClean.Metadata live F g n rank member cap s)
    (hF : F ≤ live) (hr : rank ≤ g) (hg : g ≤ live) (hm : member ≤ 1)
    (zeroData : ∀ i, 2*i ≤ cap → s.data (2*i) = 0)
    (zeroIndex : ∀ i, 2*i ≤ cap → s.index (2*i) = 0)
    (oddBound : ∀ i, 2*i+1 ≤ cap → 2*i+1 ≠ 7 → 2*i+1 ≠ 113 →
      s.index (2*i+1) ≤ oddAddressBudget live n)
    (values : ∀ i : Fin (g+1), s.data (2*(F+i.val)+1) = mag i) (hs : s.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) evenInput s (evenInputSteps n g member rank F) t ∧
      EvenReady live g n rank member cap mag s t ∧ evenInputSteps n g member rank F ≤ 40*(n+live+1) := by
  let a := preparedEvenInput s
  have da : a.data = s.data := preparedEvenInput_data s
  have ea := prepareEvenInput_eval P s hs
  rw [metadata.columns,metadata.count,metadata.present,metadata.position,metadata.source] at ea
  have prepared := preparedEvenInput_words s
  rw [metadata.columns,metadata.count,metadata.present,metadata.position,metadata.source] at prepared
  obtain ⟨a0,a2,a4,a6,a11,a13,a15,a105⟩ := prepared
  obtain ⟨c,ec,cp,odd,tail,addr⟩ := copyEvenInput_eval P a F g a11 a13 a15 a105 ea.safe_end
  let t := finishInput c
  have et : Block.Eval (Memory.AllData P) (addressPlan finishPlan) c 9 t :=
    addressPlan_spec (fun f => ∀ i, P (f i)) _ _ ec.safe_end
  have dt : t.data = c.data := applyPlan_data _ _
  have outer (j : ℕ) (h : j ∉ ([0,2,4,5,6,11,13,15,17] : List ℕ)) : c.index j = s.index j := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at h
    exact (addr j (by omega) (by omega) (by omega)).trans
      (preparedEvenInput_frame s j (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; omega))
  obtain ⟨one,three,cleared⟩ := finish_values c
  have liveWord : t.index 1 = live := one.trans ((outer 101 (by decide)).trans metadata.length)
  have rankWord : t.index 3 = rank := three.trans ((outer 109 (by decide)).trans metadata.position)
  have kept (j : ℕ) (hj : j ∈ ([93,95,97,99] : List ℕ)) : t.index j = s.index j := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    exact (finish_frame c j (by omega) (by omega)
      (by simp only [clearedCursors,List.mem_cons,List.not_mem_nil,or_false,not_or]; omega)).trans
      (outer j (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; omega))
  have even (i : ℕ) : t.index (2*i) = a.index (2*i) :=
    (finish_frame c _ (by omega) (by omega)
      (by simp only [clearedCursors,List.mem_cons,List.not_mem_nil,or_false,not_or]; omega)).trans
      (addr _ (by omega) (by omega) (by omega))
  have evenTail (i : ℕ) (hi : 4 ≤ i) : t.index (2*i) = s.index (2*i) :=
    (even i).trans (preparedEvenInput_frame s _ (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; omega))
  have dataTail (i : ℕ) (hi : g < i) : t.data (2*i) = s.data (2*i) := by
    rw [dt,tail i hi,da]
  refine ⟨t, ?_, ?_, evenInputSteps_le n g member rank F live hF hr hg hm⟩
  · rw [show evenInputSteps n g member rank F = (4*(n+g+member+rank+F)+19)+(9*g+5+9) by
      unfold evenInputSteps; omega]
    exact ea.seq (ec.seq et)
  · refine ⟨?_,?_,?_,?_,liveWord,rankWord,cleared,kept,dataTail,evenTail⟩
    · intro i hi
      by_cases inside : i < g+1
      · rw [dt,cp i (by omega),da]
        change _ = ((List.ofFn mag)[i]?).getD 0
        rw [List.getElem?_ofFn, dite_eq_left inside]
        exact values ⟨i,inside⟩
      · rw [dataTail i (by omega),zeroData i hi]
        change 0 = ((List.ofFn mag)[i]?).getD 0
        rw [List.getElem?_eq_none (by simpa using (Nat.le_of_not_gt inside)), Option.getD_none]
    · intro i hi
      match i with
      | 0 => simpa [start] using (even 0).trans a0
      | 1 => simpa [start] using (even 1).trans a2
      | 2 => simpa [start] using (even 2).trans a4
      | 3 => simpa [start] using (even 3).trans a6
      | j+4 =>
        rw [evenTail _ (by omega),zeroIndex _ hi]
        simp [start]
    · intro i
      rw [dt,odd i,da]
    · intro i hi
      by_cases h1 : 2*i+1 = 1
      · rw [h1,liveWord]; unfold oddAddressBudget; omega
      by_cases h3 : 2*i+1 = 3
      · rw [h3,rankWord]; unfold oddAddressBudget; omega
      by_cases scratch : 2*i+1 ∈ clearedCursors
      · rw [cleared _ scratch]; exact Nat.zero_le _
      have skip := scratch
      simp only [clearedCursors,List.mem_cons,List.not_mem_nil,or_false,not_or] at skip
      rw [show t.index (2*i+1) = c.index (2*i+1) from finish_frame c _ h1 h3 scratch,
        outer _ (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]; omega)]
      exact oddBound i hi (by omega) (by omega)

end ServiceFill
end Compression
end LinearProgramming
end Optimization
end OAI
