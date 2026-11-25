import OAI.Hierarchy.DescentResetScalarChart
import OAI.Hierarchy.DescentResetPaddedStencil

namespace OAI
/-! # The old host depth, last legal prefix level and hub bit in each packed output row -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentGL DescentColonies DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel
open DescentPlainTerminal.Suffix DescentPackedFlowPair.Padded
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k H n w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (name : V≃Fin H)
variable (L : PortLevels.AddressBook)

structure Heads where
  count : Expr
  levels : Bank
  hubs : Bank

def Heads.field (C : Heads) (L : PortLevels.AddressBook) (g c : ℕ) (j : Fin 3) :=
  let l:=L.host
  let kind:=if j.val=0 then PortLevels.relative c (L.levelAt C.levels l)
            else if j.val=1 then Expr.lit (L.dimension-g-c) else .lookup C.hubs l
  Expr.branch .lt l C.count kind (.lit 0)

theorem Heads.at_host (C : Heads) (ph : H≤L.hosts) (c g : ℕ) (depth : V→ℕ) (out : ℕ) (mem : Memory w)
    (static : L.chart.Resident mem) (rows : L.pos.Fits w out) (slot : L.depth.Fits w out)
    (level : C.levels.Fits w out) (hub : C.hubs.Fits w out) (levelsFit : L.hosts*(L.dimension+1)≤C.levels.size)
    (hubsFit : L.hosts≤C.hubs.size) (large : L.hosts<2^w) (span : L.dimension-c<2^n) (one : 1<2^n)
    (bounds : ∀v,c≤depth v ∧ depth v≤L.dimension)
    (count : ∀p:Row L.hosts L.groups L.batch,C.count.eval mem ((row _ _ _ p).val:Word w)=(H:Word w))
    (smoothed : ∀v,mem (C.levels.base+(name v).val*(L.dimension+1))=(depth v:Word w))
    (hubs : ∀v,mem (C.hubs.base+(name v).val)=((A.hub v).toNat:Word w))
    (j : Fin 3) (p : Row L.hosts L.groups L.batch) :
    (C.field L g c j).eval mem ((row _ _ _ p).val:Word w)=
      ((hostHeader (m:=L.dimension) (c:=c) (n:=n) A name depth g p.1 j).val:Word w) := by
  let tick:Word w:=(row _ _ _ p).val
  change (C.field L g c j).eval mem tick = _
  have countAt : C.count.eval mem tick=(H:Word w) := count p
  have read:L.host.eval mem tick=(p.1.val:Word w):=L.host_word mem out static rows p
  have wH:=ph.trans_lt large
  have wr:=p.1.isLt.trans large
  by_cases ok:p.1.val<H
  · let v:=name.symm ⟨p.1.val,ok⟩
    have same : (name v).val=p.1.val:=by simp [v]
    have hit:project H p.1=some (name v):=by simp [project,ok,v]
    have index:p.1.val*(L.dimension+1)<C.levels.size:=by
      have h:=Nat.mul_le_mul_right (L.dimension+1) p.1.isLt
      rw [Nat.succ_mul] at h
      omega
    have ds : (L.levelAt C.levels L.host).eval mem tick=(depth v:Word w):=
      (L.level_at C.levels L.host mem tick out p.1 static slot level index read).trans (by simpa only [same] using smoothed v)
    have hs : (Expr.lookup C.hubs L.host).eval mem tick=((A.hub v).toNat:Word w):=by
      simp only [Expr.eval,read,bank_read C.hubs mem (p.1.isLt.trans_le hubsFit) hub]
      simpa only [same] using hubs v
    have br : DescriptorExpr.Comparison.lt.test (p.1.val:Word w) (H:Word w)=true:=by
      simp [DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt wr,Fin.val_cast_of_lt wH,ok]
    have narrow:depth v-c<2^n:=(Nat.sub_le_sub_right (bounds v).2 c).trans_lt span
    have mid:L.dimension-g-c<2^n:=(Nat.sub_le_sub_right (Nat.sub_le ..) c).trans_lt span
    have hb:(A.hub v).toNat<2^n:=by cases A.hub v <;> simp_all
    simp only [Heads.field,Expr.eval,read,countAt,br,ite_true,hostHeader,hit,Option.elim_some,Equiv.symm_apply_apply]
    split_ifs with zero first
    · simpa only [Fin.val_cast_of_lt narrow] using PortLevels.read_relative c (depth v) _ mem tick (bounds v).1 ds
    · simp only [Expr.eval,Fin.val_cast_of_lt mid]
    · simpa only [Fin.val_cast_of_lt hb] using hs
  · have hit:project H p.1=none:=by simp [project,ok]
    have br : DescriptorExpr.Comparison.lt.test (p.1.val:Word w) (H:Word w)=false:=by
      simp [DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt wr,Fin.val_cast_of_lt wH,ok]
    simp [Heads.field,Expr.eval,read,countAt,br,hostHeader,hit]

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
