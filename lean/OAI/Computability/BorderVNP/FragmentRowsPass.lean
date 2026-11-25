import OAI.Computability.BorderVNP.FragmentRowsState

/-! # Iterating one stable pass of the native sparse fragment row writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open Diagonal.ExternalSew.Fragments VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open Packing.BottomReports.Writer (write write_append write_outside)

/-- Source rows accepted by the first `i` iterations of a single pass. -/
def Pass.rows (l : Layout) (before : ℕ → ℕ) (p : Pass) (i : ℕ) : List Quad :=
  (List.range i).filterMap (p.row l before)

@[simp] theorem Pass.rows_zero (l : Layout) (before : ℕ → ℕ) (p : Pass) : p.rows l before 0 = [] := rfl

theorem Pass.rows_succ (l : Layout) (before : ℕ → ℕ) (p : Pass) (i : ℕ) :
    p.rows l before (i+1) = p.rows l before i ++ (p.row l before i).toList := by
  simp [rows,List.range_succ]
  cases h : p.row l before i <;> simp [h]

theorem Pass.rows_length (l : Layout) (before : ℕ → ℕ) (p : Pass) (i : ℕ) :
    (p.rows l before i).length ≤ i := by simpa [rows] using
      (List.length_filterMap_le (f := p.row l before) (l := List.range i))

/-- Each accepted row occupies exactly four consecutive scalar words. -/
theorem quadWords_length (qs : List Quad) : (qs.flatMap Quad.words).length=4*qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [Quad.words,ih,Nat.mul_succ]

/-- Exact cumulative register and memory state after any prefix of the three scans. -/
def Layout.Emitted (l : Layout) (before : ℕ → ℕ) (qs : List Quad) (z : NatState) : Prop :=
  l.Ready z ∧ z.reg 14=qs.length ∧ z.mem=write before l.quads (qs.flatMap Quad.words)

private theorem frozen_of_emitted {l : Layout} {before : ℕ → ℕ} {qs : List Quad} {z : NatState}
    {w : ℕ} (fit : l.Fits w before) (cap : qs.length ≤ 2*l.host.count+l.count)
    (h : l.Emitted before qs z) : l.Frozen before z.mem := by
  intro a ha
  rw [h.2.2]
  apply write_outside
  rw [quadWords_length]
  rcases fit.outside a ha with h | h <;> omega

/-- Run the actual finite loop from an already emitted prefix. At each iteration the
complete memory image protects the original input rows and supplies the next free slot. -/
theorem pass_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (before : ℕ → ℕ) (p : Pass) (prior : List Quad)
    (fit : l.Fits w before) (start : l.Emitted before prior (.ofWords r m))
    (room : prior.length+p.count l ≤ 2*l.host.count+l.count)
    (one : ∀ (t : Bank w) (mt : Memory w) (i used : ℕ), l.Ready (.ofWords t mt) →
      l.Frozen before (readings mt) → readings t 15=i → readings t 14=used → i<p.count l →
      used<2*l.host.count+l.count → BoundedRun pub mac p.step t mt p.step.slots
        (StepResult l (readings mt) i used (p.row l before i))) :
    BoundedRun pub mac (FragmentBucket.forEach 15 p.boundReg p.step) r m (2+p.count l*(p.step.slots+1))
      (l.Emitted before (prior++p.rows l before (p.count l))) := by
  let Q := fun i => prior++p.rows l before i
  let I := fun i (z : NatState) => l.Emitted before (Q i) z ∧ z.reg 15=i
  apply (FragmentBucket.forEach_run pub mac 15 p.boundReg p.step (p.count l) p.step.slots I r m ?_ ?_ ?_).mono
    le_rfl (fun _ h => h.1)
  · obtain ⟨ready,used,mem⟩ := start
    refine ⟨⟨?_,?_,?_⟩,?_⟩
    · intro j hj
      have ne : j≠15 := by intro eq; subst j; norm_num at hj
      simpa [Code.fixedEval,Code.evalNat,Function.update,ne] using ready j hj
    · simpa [Q,Code.fixedEval,Code.evalNat,Function.update] using used
    · simpa [Q,Code.fixedEval] using mem
    · simp [Code.fixedEval,Code.evalNat]
  · rintro i z ⟨⟨ready,_,_⟩,idx⟩
    exact ⟨idx,by cases p with
      | cable _ => exact ready 7 (by decide)
      | data => exact ready 9 (by decide)⟩
  · rintro i t mt ⟨old,idx⟩
    have hl := p.rows_length l before i.val
    have hi := i.isLt
    have count : (Q i.val).length<2*l.host.count+l.count := by simp only [Q,List.length_append]; omega
    have frozen := frozen_of_emitted fit count.le old
    have step := one t mt i.val _ old.1 frozen idx old.2.1 hi count
    apply step.mono le_rfl
    rintro z ⟨ready,next,used,mem⟩
    have qs : Q (i.val+1) = Q i.val ++ (p.row l before i.val).toList := by
      simp [Q,Pass.rows_succ,List.append_assoc]
    refine ⟨⟨ready,by rwa [qs,List.length_append],?_⟩,next⟩
    have old_mem : readings mt = write before l.quads ((Q i.val).flatMap Quad.words) := old.2.2
    rw [mem,old_mem,qs]
    conv_rhs => rw [List.flatMap_append,write_append,quadWords_length]

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
