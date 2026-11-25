import OAI.Hierarchy.FactorPinIntervals
import OAI.Hierarchy.TraceIntervalFibers

namespace OAI
/-! # The input-length word in the actual certified resource matrix -/

namespace Hierarchy.GridPinPublisher
open FactorPinIntervals TraceAdmission
open scoped Classical

/-- The bit count computed from the native lane-destination array is exactly
the field required by the occurrence-ordered prefix writer. -/
theorem inputLength_from_resource {full S N pairSpan : ℕ}
    (dest : Fin full→Fin N) (origin : Fin S→Fin N) (bucket : Fin S→Fin full)
    (pos : 0<pairSpan) (room : S≤full*(2*pairSpan))
    (quotient : ∀ j,(bucket j).val=j.val/(2*pairSpan)) (owners : ∀ j,dest (bucket j)=origin j)
    (v : Fin N) : inputCount dest v S pairSpan=(intervalBits origin v).length := by
  let code := fun j=>if h : j<S then origin ⟨j,h⟩ else v
  rw [inputCount_eq_card dest v S pairSpan pos room code,length_intervalBits]
  · apply Finset.card_bij (fun j hj=>⟨j,Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩)
    · intro j hj
      obtain ⟨inside,equal⟩ := Finset.mem_filter.mp hj
      have bound := Finset.mem_range.mp inside
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [code,bound] using equal⟩
    · intro i _ j _ equal
      exact congrArg Fin.val equal
    · intro j hj
      have found : j.val∈(Finset.range S).filter (fun x=>code x=v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt,by simpa [code,j.isLt] using (Finset.mem_filter.mp hj).2⟩
      exact ⟨j.val,found,rfl⟩
  · intro x hx q hq
    have bound:=Finset.mem_range.mp hx
    let j : Fin S:=⟨x,bound⟩
    have eqn : bucket j=q := Fin.ext ((quotient j).trans hq)
    simpa only [code,dite_eq_left bound,←eqn] using (owners j).symm

end Hierarchy.GridPinPublisher

end OAI
