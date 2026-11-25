import OAI.Computability.BorderVNP.RoutingISACellControlRows

/-! # Exact row fields for the pre-sidecar native scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellControlRows

open VPVNP.BurstRAM TypedTaskBuilder

/-- Physical register values produced at the current global cell. -/
structure Layout.Gathered (l : Layout) (mem : ℕ → ℕ) (i j : ℕ) (z : NatState) : Prop where
  /-- The low immutable registers and cursors. -/
  ready : l.Ready i j z
  /-- Team owning the actual cell. -/
  owner : z.reg 21=l.owner mem i
  /-- Live original-bundle scan row. -/
  six : [22,23,24,25,26,27].map z.reg=l.rowSix mem i
  /-- Supplemental packet writer row. -/
  four : [28,29,30,31].map z.reg=l.rowFour i

set_option maxHeartbeats 1200000 in
/-- Each physical field comes from the declared memory or its fixed scalar offset. -/
theorem gather_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (mem : ℕ → ℕ) (fit : l.Room w) (i j : ℕ) (hi : i < l.cells)
    (ready : l.Ready i j (.ofWords s m)) (read : ∀ a, l.inputs i a → readings m a=mem a) :
    BoundedRun pub mac gather s m gather.slots (fun z => l.Gathered mem i j z ∧ z.mem=readings m) := by
  let z := NatState.ofWords s m
  have hr := ready
  unfold Layout.Ready at hr
  have safe : gather.fixedSafe w (readings pub) z := by
    change gather.fixedSafe w (readings pub) (.ofWords s m)
    simp (config := {decide:=true}) [gather,Code.block,Code.fixedEval,Code.fixedSafe,Code.safeReadOnly,
      Code.evalNat,addressOpFits,addressOp,hr,Layout.regValue]
    have := fit.fields; have := fit.input
    have := Nat.mul_le_mul_left l.stride hi.le
    omega
  apply (gather.runFixed pub mac s m safe).mono le_rfl
  rintro t rfl
  have regs (r : Reg) (h : r.val < 20) : readings s r=l.regValue i j r := ready r h
  have h1 := read _ (.inl rfl)
  have h2 := read _ (.inr (.inl rfl))
  have h3 := read _ (.inr (.inr (.inl rfl)))
  have h4 := read _ (.inr (.inr (.inr (.inl rfl))))
  have h5 := read _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  have h6 := read _ (.inr (.inr (.inr (.inr (.inr rfl)))))
  refine ⟨⟨fun r h => (Code.fixedEval_protected gather (readings pub) z (by decide) r h).trans (ready r h),?_,?_,?_⟩,?_⟩
  all_goals simp (config := {decide:=true}) [gather,Code.block,Code.fixedEval,Code.evalNat,addressOp,
    regs,Layout.regValue,Layout.rowSix,Layout.rowFour,TypedTaskBuilder.Layout.owner,NatState.ofWords,h1,h2,h3,h4,h5,h6]

end RoutingISA.CellControlRows

end BorderVNP
end Computability
end OAI
