import OAI.Optimization.LinearProgramming.Compression.SignWireResidentLow
import OAI.Optimization.LinearProgramming.Compression.SignWireCallerBound
import OAI.Optimization.LinearProgramming.Compression.SignWireReturnedShell

/-! Reuse the exact post-comparison cache and bounded native memory at the next
outer BitRAM request. The saved caller's address bound increases additively. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire

open RAM RAM.Callable MinorProxyCache

def nextResidentBound (n fuel C R : ℕ) : ℕ :=
  max (max C R) (addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14)))) +
    cachedProxySignSteps n fuel C + 5

theorem nextResidentBound_of_le (n fuel C R : ℕ) (hC : C≤R)
    (hprog : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14)))≤R) :
    nextResidentBound n fuel C R=R+cachedProxySignSteps n fuel C+5 := by
  simp [nextResidentBound,max_eq_right hC,max_eq_left hprog]

/-- An epoch of signed queries can reserve one fixed numerical window from the
number of calls and the uniform instruction bound. -/
theorem nextResidentBound_step (n fuel C R j : ℕ) (hC : C≤R)
    (hprog : addressBudget (tagReturningProgram (cachedProxySignFragment (.index 14)))≤R) :
    let S := cachedProxySignSteps n fuel C+5
    nextResidentBound n fuel C (R+j*S)=R+(j+1)*S := by
  let S := cachedProxySignSteps n fuel C+5
  change nextResidentBound n fuel C (R+j*S)=R+(j+1)*S
  rw [nextResidentBound_of_le _ _ _ _ (by omega) (by omega),Nat.succ_mul]
  dsimp only [S]
  omega

theorem cap_for_resident_steps (R S C q j : ℕ) (hC : C≤R) (hj : j<q) :
    max (2*C) (2*(R+j*S)+1) + S ≤ 2*(R+q*S)+1 := by
  have hmul : (j+1)*S≤q*S := Nat.mul_le_mul_right S hj
  rw [Nat.succ_mul] at hmul
  omega

/-- A low tag write lies outside all addresses covered by the comparator's
persistent-memory frame. -/
private theorem frame_after_tag {n fuel : ℕ} {m t : Memory ℚ} (f : SymbolicQueryFrame n fuel m t)
    (tag : ℕ) : SymbolicQueryFrame n fuel m (t.putIndex 14 tag) := by
  refine ⟨f.data,?_⟩
  intro i low a b c d e g h k l z
  exact (Memory.putIndex_ne _ (by omega : i≠14) _).trans (f.index i low a b c d e g h k l z)

/-- The actual native receipt returns all data required by a subsequent
adaptive query, even though the comparator reuses its working registers. -/
theorem NumericReceipt.toResidentHigh {n : ℕ} {mag : ℕ → ℚ} {L : Buffers}
    {fuel prec C R cap src base : ℕ} {P : ℚ → Prop} {row : Fin (n+1) → ℤ} {m t : Memory ℚ}
    (receipt : NumericReceipt mag L fuel prec C R cap src base P row m t)
    (initial : ResidentHigh (n:=n) mag L fuel prec C R cap base P m) (hrow : 135 ≤ cap) :
    ResidentHigh (n:=n) mag L fuel prec C (nextResidentBound n fuel C R) cap base P t := by
  let o := formOrdering (DyadicRAM.cachedForm fuel prec mag row)
  let tag := comparisonTag o
  obtain ⟨preOld,preCaller,pre,high⟩ := initial
  obtain ⟨stage,old,logical,last,work,st,inputs,image,bounded,hsLast,hsWork,fr,run,out⟩ := receipt
  let final := work.putIndex 14 tag
  have ptr : logical.index 67=base := by
    have iLo : 32≤Odd.slot 67 := by decide
    have iHi : Odd.slot 67≤cap := hrow
    have q := (image (Odd.slot 67) iHi).2
    have q' := high.index (Odd.slot 67) iLo iHi
    rw [st.high _ (by decide),Odd.index_slot] at q
    rw [Odd.index_slot,pre.rowPtr] at q'
    unfold Odd.slot at q q'
    omega
  have frame : SymbolicQueryFrame n fuel logical final := frame_after_tag fr tag
  have headers (i : ℕ) (low : 60≤ i) (upper : i<91) (stable : i<70 ∨ 75< i) :
      final.index i=logical.index i := frame.header inputs.workspace i low (by omega) stable
  have tagPort : (Odd.memory last final).index 29=2*comparisonTag o+1 := by
    change (Odd.memory last (work.putIndex 14 tag)).index (Odd.slot 14)=_
    exact (Odd.index_slot last (work.putIndex 14 tag) 14).trans rfl
  refine ⟨last,final,?_,?_⟩
  · exact {
      cache := frame.stableCache inputs.cache inputs.workspace inputs.reservation
      workspace := inputs.workspace.transfer_headers headers
      reservation := inputs.reservation.transfer_headers headers
      rowPtr := (headers 67 (by decide) (by decide) (by decide)).trans ptr
      apart := pre.apart
      callerSafe := hsWork
      nativeSafe := hsLast
      nativeBound := bounded
      capacity := (headers 60 (by decide) (by decide) (by decide)).trans inputs.capacity
      callerBound := tagReturning_callerBound run o tagPort inputs.nativeBound inputs.callerBound }
  · rw [out]
    exact returned_shell stage last final cap base (n+1) tag

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
