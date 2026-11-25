import OAI.Hierarchy.TaggedWideDatedLayout

namespace OAI
/-! # The original transport width is published at its measured row's fixed stride -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.CoreBoard.HistoryRoles RoleProgram
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
variable {W T : ℕ} (p : Dated T) (rom work : ℕ)
local notation "B" => p.maskStart work+1
local notation "N" => p.rawEdges
local notation "s" => p.widthPage rom work
local notation "flag" => RoleROM.bank (p.maskROM rom) N

theorem width_run_flags (m : Memory W) (live : Fin N→Bool) (width : Fin N→ℕ)
    (origins : ∀i : Fin N,(flag).read m (i.val:Word W)=(live i).toNat)
    (data : ∀i : Fin N,p.measured.read m ((3*i.val:ℕ):Word W)=(width i:Word W))
    (old : p.measured.Fits W B) (marked : (flag).Fits W B)
    (room : p.slotStart work<2^W) (one : 1<2^W) :
    ∃out,((s).code W).Exec m out (s).ticks ∧
      (∀i : Fin N,(p.stageWidth work).read out ((3*i.val:ℕ):Word W)=((if live i then width i else 0:ℕ):Word W)) ∧
      ∀a,a<p.maskStart work ∨ p.slotStart work≤a→ out a=m a := by
  let enter (i : Fin N) : Fin (3*N) := ⟨3*i.val,by have:=i.isLt;omega⟩
  let inject : Function.Injective enter := fun a b eq=>Fin.ext (by have:=congrArg Fin.val eq;dsimp [enter] at this;omega)
  let word (i : Fin N) : Word W := ((if live i then width i else 0:ℕ):Word W)
  let result := Function.extend enter word (fun _=>0)
  have val (i : Fin N) : (s).value.eval m (i.val:Word W)=word i := by
    have tri : triple.eval m (i.val:Word W)=((3*i.val:ℕ):Word W) := by
      simp [triple,Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_mul];ring
    have nz : (1:Word W)≠0 := by
      intro eq
      have bad:=congrArg Fin.val eq
      change 1 % (2^W) = 0 at bad
      rw [Nat.mod_eq_of_lt one] at bad
      omega
    cases hit:live i <;> simp [Dated.widthPage,Expr.eval,Comparison.test,origins,word,hit,tri,nz]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using data i
  have high : B+3*N+N+N<2^W := by unfold Dated.slotStart at room;omega
  have ran := ProtocolRAMTurnReplay.run (W:=W) B (3*N) (B+3*N) (p.maskStart work) (s).address (s).value m
    (fun i : Fin N=>B+(enter i).val) word result (by trivial)
    (show (s).value.Fits W B from ⟨⟨marked,trivial⟩,trivial,trivial,⟨old,by trivial⟩⟩)
    le_rfl high (by omega)
    (by intro i;simp [Dated.widthPage,enter,triple,Expr.eval,RowOp.opcode,BinaryOp.eval,Nat.cast_add,Nat.cast_mul];ring)
    val (by intro i;right;have:=(enter i).isLt;omega)
    (by intro i j eq
        have h:enter i=j:=Fin.ext (by omega)
        rw [←h];exact (inject.extend_apply _ _ i).symm)
    (by intro j
        by_cases h:j∈Set.range enter
        · obtain ⟨i,rfl⟩:=h;exact Or.inr ⟨i,rfl⟩
        · left;exact Function.extend_apply' _ _ _ h)
  obtain ⟨out,exec,reads,frame⟩:=ran
  refine ⟨out,exec,?_,?_⟩
  · intro i
    have lo : 3*i.val<(p.stageWidth work).size := (enter i).isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)
    have inWord : 3*i.val<2^W := by have:=(enter i).isLt;omega
    change out (B+((3*i.val:ℕ):Word W).val%(p.stageWidth work).size)=_
    rw [Fin.val_cast_of_lt inWord,Nat.mod_eq_of_lt lo]
    exact (reads (enter i)).trans (inject.extend_apply _ _ i)
  · intro a away
    unfold Dated.slotStart at away
    exact frame a (by omega) (by omega) (by omega)

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
