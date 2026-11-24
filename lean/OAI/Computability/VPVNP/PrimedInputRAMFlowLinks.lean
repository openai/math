import OAI.Computability.VPVNP.PrimedInputRAMFlowRun

/-!
# Linked conditionals and loop tests of the private RAM

Both arms of a conditional inherit its normal and rejecting exits. The guard executes
one native opcode, retaining all registers and memory. A deterministic guard emits
one tick, while a nondeterministic branch emits precisely the bit it consumes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Flow

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w r k p : ℕ} {M : Machine w p r k} {a b : PrimedInputRAM.Flow r k}
  {l q : Fin r} {stop bad : Fin p}

private theorem linkedArm {whole arm : PrimedInputRAM.Flow r k} {label : whole.Label → Fin p}
    (hl : Linked M whole label stop bad) (embed : arm.Label → whole.Label)
    (he : ∀ i, whole.code (embed i) = (arm.code i).map (Option.map embed)) :
    Linked M arm (label ∘ embed) stop bad := by
  constructor
  intro i
  change M.code (label (embed i)) = _
  rw [hl.atLabel, he, Jump.map_map]
  congr 3
  funext t
  cases t <;> rfl

theorem Linked.ifEqYes {label : (Flow.ifEq l q a b).Label → Fin p}
    (hl : Linked M (.ifEq l q a b) label stop bad) :
    Linked M a (label ∘ Sum.inr ∘ Sum.inl) stop bad :=
  linkedArm hl _ (fun _ ↦ rfl)

theorem Linked.ifEqNo {label : (Flow.ifEq l q a b).Label → Fin p}
    (hl : Linked M (.ifEq l q a b) label stop bad) :
    Linked M b (label ∘ Sum.inr ∘ Sum.inr) stop bad :=
  linkedArm hl _ (fun _ ↦ rfl)

theorem Linked.ifLtYes {label : (Flow.ifLt l q a b).Label → Fin p}
    (hl : Linked M (.ifLt l q a b) label stop bad) :
    Linked M a (label ∘ Sum.inr ∘ Sum.inl) stop bad :=
  linkedArm hl _ (fun _ ↦ rfl)

theorem Linked.ifLtNo {label : (Flow.ifLt l q a b).Label → Fin p}
    (hl : Linked M (.ifLt l q a b) label stop bad) :
    Linked M b (label ∘ Sum.inr ∘ Sum.inr) stop bad :=
  linkedArm hl _ (fun _ ↦ rfl)

theorem Linked.branchYes {label : (Flow.branch a b).Label → Fin p}
    (hl : Linked M (.branch a b) label stop bad) :
    Linked M a (label ∘ Sum.inr ∘ Sum.inl) stop bad :=
  linkedArm hl _ (fun _ ↦ rfl)

theorem Linked.branchNo {label : (Flow.branch a b).Label → Fin p}
    (hl : Linked M (.branch a b) label stop bad) :
    Linked M b (label ∘ Sum.inr ∘ Sum.inr) stop bad :=
  linkedArm hl _ (fun _ ↦ rfl)

theorem Linked.execute_ifEq {label : (Flow.ifEq l q a b).Label → Fin p}
    (hl : Linked M (.ifEq l q a b) label stop bad) (state : Word w) (priv : Word w → Word w)
    (fuel : ℕ) (rs : Regs w r) (m : Memory w) (bits : List Bool) :
    BurstRAM.execute M.program (fuel+1) ⟨label (.inl ()),state,rs,priv⟩ m bits =
      (BurstRAM.execute M.program fuel ⟨if rs l = rs q then label (.inr (.inl a.entry))
        else label (.inr (.inr b.entry)),state,rs,priv⟩ m bits).map (Report.prepend .tick) := by
  rw [BurstRAM.execute]
  simp only [Machine.program]
  rw [hl.atLabel (.inl ())]
  rfl

theorem Linked.execute_ifLt {label : (Flow.ifLt l q a b).Label → Fin p}
    (hl : Linked M (.ifLt l q a b) label stop bad) (state : Word w) (priv : Word w → Word w)
    (fuel : ℕ) (rs : Regs w r) (m : Memory w) (bits : List Bool) :
    BurstRAM.execute M.program (fuel+1) ⟨label (.inl ()),state,rs,priv⟩ m bits =
      (BurstRAM.execute M.program fuel ⟨if rs l < rs q then label (.inr (.inl a.entry))
        else label (.inr (.inr b.entry)),state,rs,priv⟩ m bits).map (Report.prepend .tick) := by
  rw [BurstRAM.execute]
  simp only [Machine.program]
  rw [hl.atLabel (.inl ())]
  rfl

theorem Linked.execute_branch {label : (Flow.branch a b).Label → Fin p}
    (hl : Linked M (.branch a b) label stop bad) (state : Word w) (priv : Word w → Word w)
    (fuel : ℕ) (rs : Regs w r) (m : Memory w) (bit : Bool) (bits : List Bool) :
    BurstRAM.execute M.program (fuel+1) ⟨label (.inl ()),state,rs,priv⟩ m (bit::bits) =
      (BurstRAM.execute M.program fuel ⟨if bit then label (.inr (.inl a.entry))
        else label (.inr (.inr b.entry)),state,rs,priv⟩ m bits).map (Report.prepend (.choice bit)) := by
  rw [BurstRAM.execute]
  simp only [Machine.program]
  rw [hl.atLabel (.inl ())]
  rfl

theorem Linked.execute_branch_nil {label : (Flow.branch a b).Label → Fin p}
    (hl : Linked M (.branch a b) label stop bad) (state : Word w) (priv : Word w → Word w)
    (fuel : ℕ) (rs : Regs w r) (m : Memory w) :
    BurstRAM.execute M.program (fuel+1) ⟨label (.inl ()),state,rs,priv⟩ m [] = none := by
  rw [BurstRAM.execute]
  simp only [Machine.program]
  rw [hl.atLabel (.inl ())]
  rfl

theorem Linked.execute_whileLt {label : (Flow.whileLt l q a).Label → Fin p}
    (hl : Linked M (.whileLt l q a) label stop bad) (state : Word w) (priv : Word w → Word w)
    (fuel : ℕ) (rs : Regs w r) (m : Memory w) (bits : List Bool) :
    BurstRAM.execute M.program (fuel+1) ⟨label (.inl ()),state,rs,priv⟩ m bits =
      (BurstRAM.execute M.program fuel ⟨if rs l < rs q then label (.inr a.entry) else stop,
        state,rs,priv⟩ m bits).map (Report.prepend .tick) := by
  rw [BurstRAM.execute]
  simp only [Machine.program]
  rw [hl.atLabel (.inl ())]
  rfl

end PrimedInputRAM.Flow

end VPVNP
end Computability
end OAI
