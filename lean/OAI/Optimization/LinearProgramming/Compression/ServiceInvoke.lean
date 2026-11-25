import OAI.Optimization.LinearProgramming.RAM.CallableScopedRun
import OAI.Optimization.LinearProgramming.RAM.CallableInvoke

/-! Invoke a closed numerical ROM on the finite physical region prepared by the
persistent service. The arbitrary exterior is kept as caller memory. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceInvoke

open RAM RAM.Callable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Return tag zero or one goes to an odd scratch address. No even output word changes. -/
def numerical (p : Program) := Fragment.invoke p 2 (.index 11)

private def frame (cap : ℕ) (m : Memory K) : Memory K where
  data i := m.data (2*i+1)
  index i := if 2*i+1 ≤ cap then m.index (2*i+1) else 0

private theorem evens_odds {P : ℕ → Prop} (even : ∀ j,P (2*j)) (odd : ∀ j,P (2*j+1)) :
    ∀ j,P j := by
  intro j
  by_cases he : j%2=0
  · exact (show 2*(j/2)=j by omega) ▸ even (j/2)
  · exact (show 2*(j/2)+1=j by omega) ▸ odd (j/2)

structure Returned (old last t : Memory K) (cap tag : ℕ) : Prop where
  flag : t.index 11=tag
  scalar : ∀ i, 2*i ≤ cap → t.data (2*i)=last.data i
  address : ∀ i, 2*i ≤ cap → t.index (2*i)=2*last.index i
  oddScalar : ∀ i,t.data (2*i+1)=old.data (2*i+1)
  oddAddress : ∀ i, 2*i+1 ≠ 11 → t.index (2*i+1)=old.index (2*i+1)

/-- A finite cleared low bank suffices; no hypothesis is imposed on any physical
cell beyond `cap` except the global scalar size bound. The proof installs the unmodified
native return word and preserves both even-bank results and all odd saved data. -/
theorem run (p : Program) (P : K → Prop) (m : Memory K) (ds : List ℕ) (xs : List K)
    (cap b k tag : ℕ) (trace : Fin (k+1) → State K) (safe : ∀ i,P (m.data i))
    (inputSafe : ∀ i,P ((start ds xs).data i))
    (evenScalar : ∀ i,2*i ≤ cap → m.data (2*i)=(start ds xs).data i)
    (evenIndex : ∀ i,2*i ≤ cap → m.index (2*i)=2*(start ds xs).index i)
    (evenBound : ∀ i,2*(start (K := K) ds xs).index i ≤ b)
    (oddBound : ∀ i,2*i+1 ≤ cap → m.index (2*i+1) ≤ b)
    (space : max (numerical p).localBudget b+(2*k+2) ≤ cap) (cap11 : 11 ≤ cap)
    (htrace : Trace p (start ds xs) k trace) (ht : (trace (Fin.last k)).output=some tag)
    (tagged : tag < 2) (traceSafe : ∀ i j,P ((trace i).data j)) :
    ∃ t,(numerical p).Run P m (2*k+2) t ∧ Returned m (trace (Fin.last k)).memory t cap tag := by
  let v := (start ds xs).memory
  let f := frame cap m
  let z := Call.pack v f
  let last := trace (Fin.last k)
  let out := Fragment.returnMemory (.index 11) tag z last
  have fData (i : ℕ) : f.data i=m.data (2*i+1) := rfl
  have fIndex (i : ℕ) : f.index i=(if 2*i+1 ≤ cap then m.index (2*i+1) else 0) := rfl
  have zs : ∀ i,P (z.data i) := evens_odds
    (fun j => by simpa [z,v,State.memory] using inputSafe j) (fun j => by simpa [z,fData] using safe (2*j+1))
  have zi : ∀ i,z.index i ≤ b := evens_odds
    (fun j => by simpa [z,v,State.memory] using evenBound j) (fun j => by
      simp only [z,Call.index_odd,fIndex]
      split_ifs with hj
      · exact oddBound _ hj
      · exact Nat.zero_le _)
  have saved : Call.savedOddFrame z=f := savedOddFrame_pack v f
  have outEq : out=(Call.pack last.memory f).putIndex 11 tag := by simp [out,Fragment.returnMemory,saved,TagSink.store]
  have good : ∀ i,P (out.data i) := by
    rw [outEq]
    exact evens_odds (fun j => by simpa [last,State.memory] using traceSafe (Fin.last k) j)
      (fun j => by simpa [fData] using safe (2*j+1))
  have exactRun : (numerical p).Run P z (2*k+2) out :=
    Fragment.invoke_prepared 2 (.index 11) P z ds xs trace tagged
      (fun j => by simp [z,v,State.memory]) (fun j => by simp [z,v,State.memory])
      zs htrace traceSafe ht good
  have patched : windowMemory cap m z=m := by
    apply congrArg₂ Memory.mk
    · funext j
      apply evens_odds (P := fun j => (windowMemory cap m z).data j=m.data j) _ _ j
      · intro i; by_cases hi : 2*i ≤ cap
        · simpa [windowMemory,hi,z,v,State.memory] using (evenScalar i hi).symm
        · simp [windowMemory,hi]
      · intro i; by_cases hi : 2*i+1 ≤ cap <;> simp [windowMemory,hi,z,fData]
    · funext j
      apply evens_odds (P := fun j => (windowMemory cap m z).index j=m.index j) _ _ j
      · intro i; by_cases hi : 2*i ≤ cap
        · simpa [windowMemory,hi,z,v,State.memory] using (evenIndex i hi).symm
        · simp [windowMemory,hi]
      · intro i; by_cases hi : 2*i+1 ≤ cap <;> simp [windowMemory,hi,z,fIndex]
  let : (numerical p).FixedAccess := by
    change (Fragment.invoke p 2 (.index 11)).FixedAccess
    infer_instance
  have actual := exactRun.fixed_window zi space m (fun j _ => safe j)
  rw [patched] at actual
  refine ⟨windowMemory cap m out,actual,?_,?_,?_,?_,?_⟩
  · simp [windowMemory,cap11,outEq]
  · intro i hi
    simp [windowMemory,hi,outEq,last]
  · intro i hi
    have away : 2*i ≠ 11 := by omega
    simp [windowMemory, hi, outEq, last, away]
  · intro i
    by_cases hi : 2*i+1 ≤ cap <;> simp [windowMemory,hi,outEq,fData]
  · intro i in11
    by_cases hi : 2*i+1 ≤ cap <;> simp [windowMemory,hi,outEq,in11,fIndex]

end ServiceInvoke
end Compression
end LinearProgramming
end Optimization
end OAI
