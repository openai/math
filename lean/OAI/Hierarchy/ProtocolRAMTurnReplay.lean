import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Sparse native replay into a zero-initialized paid gate shelf -/

namespace Hierarchy.ProtocolRAMTurnReplay
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorScan
open ProtocolRAM ProtocolRAMGeneratedWrite
open scoped Fin.CommRing

variable {W n : ℕ}

theorem read_agree (addr : Fin n→ℕ) (word : Fin n→Word W) (m : Memory W) (a : ℕ) (v : Word W)
    (agree : ∀ i,addr i=a → word i=v) (t : ℕ)
    (hit : m a=v ∨ ∃ i : Fin n,i.val<t ∧ addr i=a) :
    ProtocolRAMIndexedWrite.image addr word m t a=v := by
  induction t with
  | zero => rcases hit with h|⟨i,h,_⟩; exact h; omega
  | succ t ih =>
    by_cases ht : t<n
    · let j : Fin n := ⟨t,ht⟩
      by_cases ha : addr j=a
      · simp only [ProtocolRAMIndexedWrite.image,dite_eq_left ht,←ha,j,Function.update_self]
        exact agree j ha
      · rw [ProtocolRAMIndexedWrite.image,dite_eq_left ht,Function.update_of_ne (Ne.symm ha)]
        apply ih
        rcases hit with h|⟨i,hi,h⟩
        · exact Or.inl h
        · refine Or.inr ⟨i,?_,h⟩
          have ne : i.val≠t := fun e => ha ((congrArg addr (show i=j from Fin.ext e)).symm.trans h)
          omega
    · rw [ProtocolRAMIndexedWrite.image,dite_eq_right ht]
      apply ih
      rcases hit with h|⟨i,_,h⟩
      · exact Or.inl h
      · exact Or.inr ⟨i,by have := i.isLt;omega,h⟩

def program (W base length scratch n : ℕ) (A V : Expr) : Procedure W :=
  (scan W base length (.lit 0)).seq (ProtocolRAMGeneratedWrite.program W scratch (scratch+n) n A V)

def work (length n : ℕ) (A V : Expr) := (4+6*length)+ProtocolRAMGeneratedWrite.work n A V

/-- The native stream may write the same sink repeatedly. The only circuit inputs here are two
row expressions; their values on the initial memory determine the entire sparse stream. -/
theorem run (base length scratch sink : ℕ) (A V : Expr) (m : Memory W)
    (addr : Fin n→ℕ) (word : Fin n→Word W) (result : Fin length→Word W)
    (af : A.Fits W base) (vf : V.Fits W base) (before : base+length≤ scratch)
    (fits : scratch+n+n<2^W) (sinkBefore : sink<scratch)
    (dataA : ∀ i : Fin n, A.eval m (i.val:Word W)=(addr i:Word W))
    (dataV : ∀ i : Fin n, V.eval m (i.val:Word W)=word i)
    (range : ∀ i,addr i=sink ∨ (base≤addr i ∧ addr i<base+length))
    (agree : ∀ i (j : Fin length),addr i=base+j.val → word i=result j)
    (cover : ∀ j,result j=0 ∨ ∃ i,addr i=base+j.val) :
    ∃ out,(program W base length scratch n A V).Exec m out (work length n A V) ∧
      (∀ j : Fin length,out (base+j.val)=result j) ∧
      ∀ t,(t<base ∨ base+length≤t) → (t<scratch ∨ scratch+n+n≤t) → t≠sink → out t=m t := by
  let clear := ProtocolRAM.image base length (.lit 0) m
  let first := ProtocolRAM.image scratch n A clear
  let last := ProtocolRAM.image (scratch+n) n V first
  let out := ProtocolRAMIndexedWrite.image addr word last n
  have clearFrame a (away : a<base ∨ base+length≤a) : clear a=m a :=
    frame_image base length (.lit 0) m a away
  have clearRun : (scan W base length (.lit 0)).Exec m clear (4+6*length) := by
    have h : (scan W base length (.lit 0)).Exec m clear (4+length*(2*Expr.work (.lit 0)+4)) :=
      scan_exec base length (.lit 0) m trivial (by omega)
    have he : 4+length*(2*Expr.work (.lit 0)+4)=4+6*length := by simp [Expr.work,Nat.mul_comm]
    rwa [he] at h
  have destSmall i : addr i<scratch := by rcases range i with h|h <;> omega
  have exec : (ProtocolRAMGeneratedWrite.program W scratch (scratch+n) n A V).Exec clear out
      (ProtocolRAMGeneratedWrite.work n A V) :=
    ProtocolRAMGeneratedWrite.run scratch (scratch+n) A V addr word clear
      (fits_mono A (by omega) af) (fits_mono V (by omega) vf) le_rfl fits
      (fun i=>(eval_below A _ m clear af (fun t ht=>clearFrame t (.inl ht))).trans (dataA i))
      (fun i=>(eval_below V _ m clear vf (fun t ht=>clearFrame t (.inl ht))).trans (dataV i))
      (fun i=>by have := destSmall i;omega) (fun i j=>by have := destSmall j;omega)
      (fun i j=>by have := destSmall j;omega)
  have lastFrame a (h : a<scratch ∨ scratch+n+n≤a) : last a=clear a :=
    (frame_image (scratch+n) n V first a (by omega)).trans (frame_image scratch n A clear a (by omega))
  refine ⟨out,?_,?_,?_⟩
  · intro P R K M pc rg pub exit ins publicData cfg mem start eq
    exact Procedure.Exec.then clearRun exec M pc rg pub exit ins publicData cfg mem start eq
  · intro j
    apply read_agree addr word last _ _ (fun i h=>agree i j h)
    rcases cover j with h|⟨i,hi⟩
    · apply Or.inl
      rw [lastFrame _ (.inl (by have := j.isLt;omega)),h]
      exact read_image base length (.lit 0) m j
    · exact Or.inr ⟨i,i.isLt,hi⟩
  · intro t outside separate different
    exact (ProtocolRAMIndexedWrite.frame addr word last n t (fun i h=>by
      rcases range i with hs|hb <;> omega)).trans ((lastFrame t separate).trans (clearFrame t outside))

end Hierarchy.ProtocolRAMTurnReplay

end OAI
