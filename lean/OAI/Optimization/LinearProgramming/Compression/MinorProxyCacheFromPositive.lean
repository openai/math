import OAI.Optimization.LinearProgramming.Compression.MinorProxyCache
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheAllocate

/-! Prepare every header and the shared denominator from a dense positive magnitude
tape, then invoke the native cached-log loop. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Callable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def fromPositive : Fragment := Fragment.seq (.ofBlock allocate) materialize

def fromPositiveCost (n fuel prec src addressEnd : ℕ) :=
  allocationCost n fuel prec src addressEnd+cacheCost n fuel prec

/-- High caller records remain readable outside the newly allocated arrays, and the two
staging pointers survive the header arithmetic, the magnitude copy, and every native call. -/
structure Retained (m t : Memory K) (L : Buffers) (n limit : ℕ) : Prop where
  scalar : ∀j,limit≤j → (j<L.magBase ∨ L.scalePtr<j) → t.data j=m.data j
  address : ∀j,128≤j → (j<L.flagBase ∨ L.flagBase+n≤j) → t.index j=m.index j
  scalarStaging : t.index 87=m.index 87
  addressStaging : t.index 88=m.index 88
  driver : ∀j,90≤j → j<128 → t.index j=m.index j

theorem fromPositive_framed (P allowed : K→Prop) (n fuel prec src addressEnd : ℕ) (mag : ℕ→K)
    (m : Memory K) (safe : m.AllData P) (hz : P 0) (h0 : m.index 0=n) (h1 : m.index 1=fuel)
    (h2 : m.index 2=prec) (h3 : m.index 3=src) (h4 : m.index 4=addressEnd)
    (input : ∀i<n,m.data (src+i)=mag i) (positive : ∀i<n,0<mag i) (eligible : ∀i<n,allowed (mag i))
    (powers : ∀j≤prec,P ((2:K)^(j+2))) (native : NativeSafe P allowed fuel prec)
    (codes : ∀i<n,P (numeratorWord (fieldProxyNumerator fuel prec (mag i)))) :
    let L := buffers n fuel prec src addressEnd
    ∃ t, fromPositive.Run P m (fromPositiveCost n fuel prec src addressEnd) t ∧
      StableCache t L n fuel prec mag ∧ t.index 60=m.index 60 ∧ Retained m t L n (cap fuel prec) := by
  obtain ⟨a,k,hk,alloc,head,limit,scale,words,capacity,allocFrame⟩ :=
    allocate_framed P m safe n fuel prec src addressEnd h0 h1 h2 h3 h4 powers
  obtain ⟨t,run,out,capRet,addrFrame,scalarFrame⟩ := materialize_framed P allowed fuel prec n _ mag a alloc.safe_end hz head
    (buffers_separated n fuel prec src addressEnd) limit scale (fun i hi => (words i hi).trans (input i hi))
    positive eligible native codes
  let L := buffers n fuel prec src addressEnd
  have flags : 128≤L.flagBase := (buffers_separated n fuel prec src addressEnd).flagHigh
  refine ⟨t,((Fragment.Run.ofBlock alloc).seq run).mono (Nat.add_le_add_right hk _),out,capRet.trans capacity,?_,?_,?_,?_,?_⟩
  · intro j hj outside
    have keep : j<L.gridBase ∨ L.gridBase+n≤j := by dsimp [L,buffers] at outside ⊢; omega
    exact (scalarFrame j hj keep).trans (allocFrame.scalar j hj outside)
  · intro j hj far
    exact (addrFrame j (by omega) far).trans (allocFrame.address j hj)
  · exact (addrFrame 87 (by decide) (.inl (by change 87<L.flagBase; omega))).trans allocFrame.scalarStaging
  · exact (addrFrame 88 (by decide) (.inl (by change 88<L.flagBase; omega))).trans allocFrame.addressStaging
  · intro j hj lo
    exact (addrFrame j (by omega) (.inl (by change j<L.flagBase; omega))).trans (allocFrame.driver j hj lo)

theorem fromPositive_run (P allowed : K→Prop) (n fuel prec src addressEnd : ℕ) (mag : ℕ→K)
    (m : Memory K) (safe : m.AllData P) (hz : P 0) (h0 : m.index 0=n) (h1 : m.index 1=fuel)
    (h2 : m.index 2=prec) (h3 : m.index 3=src) (h4 : m.index 4=addressEnd)
    (input : ∀i<n,m.data (src+i)=mag i) (positive : ∀i<n,0<mag i) (eligible : ∀i<n,allowed (mag i))
    (powers : ∀j≤prec,P ((2:K)^(j+2))) (native : NativeSafe P allowed fuel prec)
    (codes : ∀i<n,P (numeratorWord (fieldProxyNumerator fuel prec (mag i)))) :
    let L := buffers n fuel prec src addressEnd
    ∃ t, fromPositive.Run P m (fromPositiveCost n fuel prec src addressEnd) t ∧
      StableCache t L n fuel prec mag ∧ t.index 60=m.index 60 := by
  obtain ⟨t,run,out,capacity,_⟩ := fromPositive_framed P allowed n fuel prec src addressEnd mag m safe hz
    h0 h1 h2 h3 h4 input positive eligible powers native codes
  exact ⟨t,run,out,capacity⟩

/-- The zero-padded finite tape gives a total mathematical lookup for the packed array. -/
def tapeMagnitude {K : Type*} [Zero K] {n : ℕ} (mag : Fin n→K) (i : ℕ) : K :=
  ((List.ofFn mag)[i]?).getD 0

@[simp] theorem tapeMagnitude_fin {F : Type*} [Zero F] {n : ℕ} (mag : Fin n→F) (i : Fin n) :
    tapeMagnitude mag i.val=mag i := by simp [tapeMagnitude,i.isLt]

theorem fromPositive_field {n : ℕ} (fuel prec : ℕ) (mag : Fin n→K) (positive : ∀i,0<mag i) :
    let m := start [n,fuel,prec,0,0] (List.ofFn mag)
    ∃ k≤fromPositiveCost n fuel prec 0 0+1, ∃ tr : Fin (k+1)→State K,
      Trace (fromPositive.program 0) m k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      StableCache (tr (Fin.last k)).memory (buffers n fuel prec 0 0) n fuel prec (tapeMagnitude mag) := by
  let m := start [n,fuel,prec,0,0] (List.ofFn mag)
  obtain ⟨t,run,out,_⟩ := fromPositive_run (fun _ => True) (fun _ => True) n fuel prec 0 0
    (tapeMagnitude mag) m.memory (fun _ => True.intro) True.intro rfl rfl rfl rfl rfl
    (fun i _ => by change tapeMagnitude mag (0+i)=tapeMagnitude mag i; rw [Nat.zero_add]) (fun i hi => (tapeMagnitude_fin mag ⟨i,hi⟩) ▸ positive ⟨i,hi⟩)
    (fun _ _ => True.intro) (fun _ _ => True.intro) (by intro; intros; trivial) (fun _ _ => True.intro)
  obtain ⟨k,hk,tr,trace,tag,mem,_⟩ := Fragment.run_halt run 0
  exact ⟨k,hk,tr,trace,tag,mem ▸ out⟩

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
