import OAI.Optimization.LinearProgramming.Compression.SignWireCached
import OAI.Optimization.LinearProgramming.Compression.SignWireWindow
import OAI.Optimization.LinearProgramming.Compression.SignWireCallback
import OAI.Optimization.LinearProgramming.Compression.SignWireOuterStage
import OAI.Optimization.LinearProgramming.Compression.CachedForms
import OAI.Optimization.LinearProgramming.Compression.DyadicCallable

/-! The three-valued native callback at the physical BitRAM boundary. Its
numerical inputs are ordinary data-position facts about an initialized finite
window; its conclusion is an execution of the fixed packed comparator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable MinorProxyCache
open scoped BigOperators

structure NumericInputs {n : ℕ} (row : Fin (n+1) → ℤ) (mag : ℕ → ℚ) (L : Buffers)
    (fuel prec C R : ℕ) (P : ℚ → Prop) (old m : Memory ℚ) : Prop where
  cache : StableCache m L n fuel prec mag
  workspace : SymbolicQueryLayout m n fuel
  reservation : SymbolicCacheReservation m L n fuel
  coeff : ∀ i, m.data (m.index 67+i.val)=(row i:ℚ)
  callerSafe : m.AllData P
  nativeSafe : old.AllData P
  nativeBound : Footprint C (old.atPC 0)
  capacity : m.index 60=C+1
  callerBound : ∀ i,m.index i ≤ R

def numericalCachedTagger : Fragment := .seq (.ofBlock outerRowStage) isolatedCachedCompare

/-- The pre-stage environment specifies only the scalar/physical address
alignment after the fixed stride copy. The numerical result is derived by
executing the comparator on these operands. -/
def OuterJobData {n : ℕ} (mag : ℕ → ℚ) (L : Buffers) (fuel prec C R cap src base : ℕ)
    (P : ℚ → Prop) (m : Memory ℚ) : Prop :=
  m.index 51=n+1 ∧ m.index 55=4*base+2 ∧ 3 ≤ m.index 47 ∧ 0<src ∧
  (∀ i j, i<j → j<n+1 → 4*(base+i)+2 ≠ src+j) ∧
  ∀ (row : Fin (n+1) → ℤ), (∀ i, m.data (src+i.val)=(row i:ℚ)) →
    ∀ t : Memory ℚ, OuterRowStaged m t src base (n+1) → t.AllData P →
      EvenParity t ∧ ∃ old logical : Memory ℚ, WindowImage t cap (Odd.memory old logical) ∧
        NumericInputs row mag L fuel prec C R P old logical

/-- The returned native memory, including the actual dirty bank, cached row
frame and unchanged outside-window physical cells. This information is kept
when the outer controller must serve a second request. -/
def NumericReceipt {n : ℕ} (mag : ℕ → ℚ) (L : Buffers) (fuel prec C R cap src base : ℕ)
    (P : ℚ → Prop) (row : Fin (n+1) → ℤ) (m t : Memory ℚ) : Prop :=
  let tag := comparisonTag (formOrdering (DyadicRAM.cachedForm fuel prec mag row))
  ∃ stage old logical last work : Memory ℚ,
    OuterRowStaged m stage src base (n+1) ∧ NumericInputs row mag L fuel prec C R P old logical ∧
    WindowImage stage cap (Odd.memory old logical) ∧ Footprint C (last.atPC 0) ∧ last.AllData P ∧ work.AllData P ∧ SymbolicQueryFrame n fuel logical work ∧
    (cachedProxySignFragment (.index 14)).Run P (Odd.memory old logical) (cachedProxySignSteps n fuel C)
      (Odd.memory last (work.putIndex 14 tag)) ∧
    t=(Call.pack (windowMemory cap (evenView stage)
      (((Odd.memory last (work.putIndex 14 tag)).putIndex 0 3).putIndex 2 5)) (Call.savedOddFrame stage)).putIndex 14 tag

theorem numericalCachedTagger_reads_capture {n : ℕ} (fuel prec B C R addr cap src base : ℕ)
    (A : ℤ) (mag : ℕ → ℚ) (L : Buffers) (P : ℚ → Prop)
    (bits : ∀ i : Fin n, ratBits (mag i) ≤ B) (cut : (2:ℤ)^prec*A ≤ 2^fuel)
    (hcap : symbolicQueryCap n fuel ≤ C)
    (hq : ∀ q,ratBits q ≤ symbolicQueryBits n fuel prec B → P q)
    (prog : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ addr)
    (envelope : max (2*C) (2*R+1) ≤ addr) (reserve : addr+(cachedProxySignSteps n fuel C+5) ≤ cap) :
    ReadsTaggedWith (p:=n+1) numericalCachedTagger
      (fun row : Fin (n+1) → ℤ => formOrdering (DyadicRAM.cachedForm (n:=n) fuel prec mag row)) src
      (numericalTagCost n fuel C) P (OuterJobData (n:=n) mag L fuel prec C R cap src base P)
      (DyadicRAM.coefficientBudget (n:=n) A) (NumericReceipt (n:=n) mag L fuel prec C R cap src base P) := by
  classical
  intro row allowed m hm henv srcPtr rowData
  obtain ⟨dimension,nested,reply,positive,separate,himage⟩ := henv
  obtain ⟨t,stage,st⟩ := outerRowStage_spec P m src base (n+1) hm dimension srcPtr nested
    (Or.inr positive) separate
  obtain ⟨parity,old,logical,image,inp⟩ := himage row rowData t st stage.safe_end
  let av (j : ℕ) : ℤ := if h : j<n then row (Fin.castSucc ⟨j,h⟩) else 0
  let c := row (Fin.last n)
  have av_eq (i : Fin n) : av i=row i.castSucc := by
    calc
      av i = row ((⟨i.val,i.isLt⟩ : Fin n).castSucc) := dite_eq_left i.isLt
      _ = row i.castSucc := congrArg row (Fin.ext rfl)
  have budget : |c|+∑ i : Fin n, |av i| ≤ A := by
    simpa only [DyadicRAM.coefficientBudget,c,av_eq] using allowed
  have coeff (j : ℕ) (hj : j<n) : logical.data (logical.index 67+j)=(av j:ℚ) := by
    simpa [av,hj] using inp.coeff (Fin.castSucc ⟨j,hj⟩)
  have rhs : logical.data (logical.index 67+n)=(c:ℚ) := by simpa [c] using inp.coeff (Fin.last n)
  obtain ⟨last,s,compute,previous,keep⟩ := cachedProxySignFragment_run fuel prec B C c av mag old logical P
    (.index 14) L inp.cache inp.workspace bits budget cut coeff rhs inp.callerSafe inp.nativeSafe
    inp.nativeBound inp.capacity hcap hq (fun _ _ => inp.callerSafe)
  let x := DyadicRAM.cachedForm fuel prec mag row
  let tag := comparisonTag (formOrdering x)
  have tagEq : tag = if ((c:ℝ)+∑ i:Fin n,(av i:ℝ)*logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i)))<0
      then 0 else if 0<((c:ℝ)+∑ i:Fin n,(av i:ℝ)*logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i)))
      then 2 else 1 := by simp only [tag,x,comparisonTag_formOrdering,DyadicRAM.cachedForm,c,av_eq]
  have inner : (cachedProxySignFragment (.index 14)).Run P (Odd.memory old logical) (cachedProxySignSteps n fuel C)
      (Odd.memory last (s.putIndex 14 tag)) := by simpa only [tagEq,TagSink.store] using compute
  have ht : (Odd.memory last (s.putIndex 14 tag)).index 29=2*comparisonTag (formOrdering x)+1 := by
    change (Odd.memory last (s.putIndex 14 tag)).index (Odd.slot 14)=_
    exact (Odd.index_slot last (s.putIndex 14 tag) 14).trans rfl
  let actual := (Call.pack (windowMemory cap (evenView t)
    (((Odd.memory last (s.putIndex 14 tag)).putIndex 0 3).putIndex 2 5)) (Call.savedOddFrame t)).putIndex 14 tag
  have native : isolatedCachedCompare.Run P t (isolatedCachedCost n fuel C) actual :=
    isolatedSign_window_run inner (formOrdering x) ht image parity stage.safe_end prog
      (fun i => (cacheImage_address inp.nativeBound inp.callerBound i).trans envelope) reserve
  have preservedOdd (i : ℕ) (odd : i%2=1) : actual.index i=m.index i := by
    have h : actual.index i=t.index i := by
      obtain ⟨j,rfl⟩ : ∃ j, i=2*j+1 := ⟨i/2,by omega⟩
      change ((Call.pack _ (Call.savedOddFrame t)).putIndex 14 tag).index (2*j+1)=t.index (2*j+1)
      exact (Memory.putIndex_ne _ (by omega) _).trans (Call.index_odd ..)
    exact h.trans (st.odd i odd)
  refine ⟨actual,(Fragment.Run.ofBlock stage).seq native,by simp [actual,tag,x],?_,?_,
    t,old,logical,last,s,st,inp,image,previous,DyadicRAM.callee_safe inner.safe_end,DyadicRAM.caller_safe inner.safe_end,
    keep,inner,rfl⟩
  · rw [preservedOdd 47 (by decide)];exact reply
  · intro i _ h _ _;exact preservedOdd i h

theorem numericalCachedTagger_reads {n : ℕ} (fuel prec B C R addr cap src base : ℕ)
    (A : ℤ) (mag : ℕ → ℚ) (L : Buffers) (P : ℚ → Prop)
    (bits : ∀ i : Fin n, ratBits (mag i) ≤ B) (cut : (2:ℤ)^prec*A ≤ 2^fuel)
    (hcap : symbolicQueryCap n fuel ≤ C)
    (hq : ∀ q,ratBits q ≤ symbolicQueryBits n fuel prec B → P q)
    (prog : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14))) ≤ addr)
    (envelope : max (2*C) (2*R+1) ≤ addr) (reserve : addr+(cachedProxySignSteps n fuel C+5) ≤ cap) :
    ReadsTagged (p:=n+1) numericalCachedTagger
      (fun row : Fin (n+1) → ℤ => formOrdering (DyadicRAM.cachedForm (n:=n) fuel prec mag row)) src
      (numericalTagCost n fuel C) P (OuterJobData (n:=n) mag L fuel prec C R cap src base P)
      (DyadicRAM.coefficientBudget (n:=n) A) :=
  (numericalCachedTagger_reads_capture fuel prec B C R addr cap src base A mag L P bits cut hcap hq
    prog envelope reserve).forget

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
