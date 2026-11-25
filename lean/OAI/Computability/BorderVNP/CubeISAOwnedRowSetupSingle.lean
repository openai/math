import OAI.Computability.BorderVNP.CubeISAOwnedRowSetupModel

/-! # Native setup for the two orientations of an owned singleton row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedRowSetup

open VPVNP.BurstRAM Cube.Physical.Owned

/-- Shared-frame reads compute the grouping place, number of trials and scalar width. -/
theorem prepare_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (l : Layout) (i : Fin (n+1)) (loaded : l.Loaded n (readings pub) (readings m))
    (fit : l.Fits w n (readings pub 0)) (h0 : readings s 0 = 0) (h1 : readings s 1 = 1)
    (axis : readings s 4 = i.val) : BoundedRun pub mac single s m single.slots (fun z =>
      Prepared l n i.val z.reg ∧ (∀ j, Held j → z.reg j = readings s j) ∧ z.mem = readings m) := by
  obtain ⟨d,axes,bc,power,header,blocks,bank,powers⟩ := loaded
  simp only [frameField] at d axes bc power header
  have pi := powers i.val (Nat.le_of_lt_succ i.isLt)
  have pn := powers n le_rfl
  have frame (dst : Reg) (f : Word 8) (st : NatState) (h : f.val ≤ 63) :
      (readFrame dst 62 63 f).fixedSafe w (readings pub) st := readFrame_fixedSafe _ _ _ _ _
        ((Nat.add_le_add_left h _).trans_lt fit.primary)
  have room : single.fixedSafe w (readings pub) (.ofWords s m) := by
    simp (config := {decide := true}) [single,Code.block,Code.fixedSafe,Code.safeReadOnly,Code.fixedEval,
      Code.evalNat,addressOp,addressOpFits,readFrame_fixedEval,NatState.ofWords,d,axes,bc,power,header,
      blocks,bank,pn,axis,h1,fit.header,fit.powers,fit.endpoints,fit.single,
      frame _ _ _ (by decide : (59 : Word 8).val ≤ 63),frame _ _ _ (by decide : (60 : Word 8).val ≤ 63),
      frame _ _ _ (by decide : (61 : Word 8).val ≤ 63),frame _ _ _ (by decide : (62 : Word 8).val ≤ 63),
      frame _ _ _ (by decide : (63 : Word 8).val ≤ 63)]
    have hi := i.isLt
    have hh := fit.header
    have hp := fit.powers
    omega
  apply (Code.runFixed single pub mac s m room).mono le_rfl
  rintro _ rfl
  refine ⟨?_,?_,?_⟩
  · constructor <;> simp (config := {decide := true}) [single,Code.block,readFrame_fixedEval,Code.fixedEval,
      Code.evalNat,addressOp,NatState.ofWords,d,axes,bc,power,header,blocks,bank,pi,pn,axis,h0,h1,singlePairTrials]
  · intro j hj
    simp only [Held,List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with h|h|h|h|h|h|h|h|h|h|h <;> subst j <;>
      simp (config := {decide := true}) [single,Code.block,readFrame_fixedEval,Code.fixedEval,Code.evalNat,NatState.ofWords]
  · simp [single,Code.block,readFrame_fixedEval,Code.fixedEval,NatState.ofWords]

/-- Singleton row setup supplies the full iterator contract and the endpoint scalar-bit count. -/
theorem single_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (l : Layout) (i : Fin (n+1)) (a b : Fin l.d)
    (loaded : l.Loaded n (readings pub) (readings m)) (fit : l.Fits w n (readings pub 0))
    (h0 : readings s 0 = 0) (h1 : readings s 1 = 1) (axis : readings s 4 = i.val)
    (ha : readings s 14 = a.val) (hb : readings s 15 = b.val) :
    BoundedRun pub mac single s m single.slots (fun z => Owned.singleReady i a b 0 z ∧ z.reg 5 = n ∧
      z.reg 21 = l.blocks*l.bc ∧ (∀ j, Held j → z.reg j = readings s j) ∧ z.mem = readings m) := by
  apply (prepare_run pub mac s m l i loaded fit h0 h1 axis).mono le_rfl
  rintro z ⟨p,keep,mem⟩
  exact ⟨⟨(keep _ (by decide)).trans h0,(keep _ (by decide)).trans h1,p.radix,p.labels,p.place,
    (keep _ (by decide)).trans ha,(keep _ (by decide)).trans hb,p.cursor,p.trials⟩,p.dim,p.bits,keep,mem⟩

/-- Reverse the two endpoint symbols for the second orientation. -/
def swap : Code := .block [.copy 54 14,.copy 14 15,.copy 15 54]

/-- The reversed row has exactly the interchanged endpoint symbols, with memory, trial
cursor and every other caller register preserved. -/
theorem swap_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :
    BoundedRun pub mac swap s m 3 (fun z => z.reg 14 = readings s 15 ∧ z.reg 15 = readings s 14 ∧
      (∀ j : Reg, j ≠ 14 → j ≠ 15 → j ≠ 54 → z.reg j = readings s j) ∧ z.mem = readings m) := by
  apply (Code.runFixed swap pub mac s m (by exact ⟨trivial,trivial,trivial⟩)).mono le_rfl
  rintro _ rfl
  simp (config := {decide := true}) [swap,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords]
  intro j h14 h15 h54
  simp [h14,h15,h54]

/-- Both singleton setup and symbol reversal are deterministic. -/
theorem single_swap_deterministic : single.deterministic = true ∧ swap.deterministic = true := by decide

end RoutingISA.OwnedRowSetup

end BorderVNP
end Computability
end OAI
