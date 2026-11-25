import OAI.Computability.BorderVNP.PackedReportWriter
import OAI.Computability.BorderVNP.CellPacketChunk

/-! # Native copying of scalar bundle-directory sections -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BundleDirectory

open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket
open BottomReports.Writer (write write_outside)

/-- Copy one scalar and advance both physical addresses. -/
def copyStep : Code := .block [.load 53 50,.store 52 53,.binary .add 50 50 63,.binary .add 52 52 63]

/-- Copy the half-open sorted section, omitting its markers. -/
def copySection : Code := .whileLt 50 51 copyStep

/-- Only the two cursors and the scalar temporary are changed by the copy loop. -/
theorem copy_keeps {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} (h : Runs pub mac copySection s m es t mt)
    (r : Reg) (h50 : r ≠ 50) (h52 : r ≠ 52) (h53 : r ≠ 53) : t r = s r := by
  exact h.keepsReg (by simp [copySection,copyStep,Code.block,Code.keeps,h50,h52,h53])

/-- Exact chronological word copy, including the guard on an empty range and
both possible orders of the two disjoint allocations. -/
theorem copy_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (a d : ℕ) (xs : List ℕ)
    (src : (s 50).val = a) (stop : (s 51).val = a+xs.length) (dst : (s 52).val = d)
    (one : (s 63).val = 1) (stored : WordsAt (readings m) a xs)
    (apart : a+xs.length ≤ d ∨ d+xs.length ≤ a) (fit : d+xs.length < 2^w) :
    BoundedRun pub mac copySection s m (5*xs.length+1) (fun z =>
      z.reg 50 = a+xs.length ∧ z.reg 52 = d+xs.length ∧ z.mem = write (readings m) d xs) := by
  induction xs generalizing a d s m with
  | nil =>
    simp only [List.length_nil,Nat.add_zero] at stop ⊢
    exact ⟨_,s,m,.whileDone (show ¬(s 50).val<(s 51).val by omega),le_rfl,src,dst,rfl⟩
  | cons x xs ih =>
    simp only [List.length_cons] at stop apart fit
    have hstop := (s 51).isLt
    have val : readings m a = x := by simpa using stored ⟨0,by simp⟩
    have safe : copyStep.fixedSafe w (readings pub) (.ofWords s m) := by
      simp [copyStep,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
        addressOpFits,NatState.ofWords,readings,Function.update,src,dst,one]; omega
    obtain ⟨es,t,mt,step,hc,hr⟩ := copyStep.runFixed pub mac s m safe
    have reg (i : Reg) := congrFun (congrArg NatState.reg hr) i
    have hm := congrArg NatState.mem hr
    have next : readings mt = Function.update (readings m) d x := by
      simpa [copyStep,Code.block,Code.fixedEval,Code.evalNat,Function.update,NatState.ofWords,
        src,dst,readings,show (m a).val=x from val] using hm
    have ha : (t 50).val = a+1 := by
      simpa [copyStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,
        Function.update,readings,src,one] using reg 50
    have hd : (t 52).val = d+1 := by
      simpa [copyStep,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,
        Function.update,readings,dst,one] using reg 52
    have hn : (t 51).val = a+1+xs.length := by
      simpa [copyStep,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,Function.update,
        readings,stop,Nat.add_assoc,Nat.add_comm 1] using reg 51
    have hu : (t 63).val = 1 := by
      simpa [copyStep,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,Function.update,readings,one]
        using reg 63
    have ht : WordsAt (readings mt) (a+1) xs := by
      intro i
      have := i.isLt
      rw [next,Function.update_of_ne (by rcases apart with h | h <;> omega : a+1+i.val ≠ d)]
      simpa [Nat.add_assoc,Nat.add_comm 1] using stored i.succ
    obtain ⟨fs,u,mu,tail,hf,us,ud,um⟩ := ih t mt (a+1) (d+1) ha hn hd hu ht
      (by rcases apart with h | h <;> omega) (by omega)
    refine ⟨_,u,mu,.whileStep (show (s 50).val < (s 51).val by omega) step tail,?_,?_,?_,?_⟩
    · change 1+traceCost (es++fs) ≤ 5*(xs.length+1)+1
      rw [show traceCost (es++fs) = traceCost es+traceCost fs from VPVNP.RAMBuckets.cost_append ..]
      change traceCost es ≤ 4 at hc
      omega
    · simpa [Nat.add_assoc,Nat.add_comm 1] using us
    · simpa [Nat.add_assoc,Nat.add_comm 1] using ud
    · rw [write,←next]; exact um

end Packing.BundleDirectory

end BorderVNP
end Computability
end OAI
