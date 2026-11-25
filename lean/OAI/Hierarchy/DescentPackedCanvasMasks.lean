import OAI.Hierarchy.DescentPackedCanvasLift
import OAI.Hierarchy.DescentHostMaskCore

namespace OAI
/-! # Retain the real header and erase ghost depth and gain by the authenticated common-host count -/
namespace Hierarchy.DescentPackedRectangle.Canvas
open DescentSIMDLookup DescentMeasuredWeights DescentMeasuredHeader DescentPackedExchange DescentHostCount
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H P D k w : ℕ}
local notation "N" => P*(k+1)+P*D
local notation "ord" => rowOrd P k D
local notation "Q" => Rows P k D

def masked (owners count source : Bank) := DescentHostCount.expression owners count (.lookup source .row) 0

def masks (owners count srcDepth srcGain : Bank) (outD outG P k D w : ℕ) :=
  let n := P*(k+1)+P*D
  (scan w outD n (masked owners count srcDepth)).seq (scan w outG n (masked owners count srcGain))

theorem native_masks (owners count srcDepth srcGain : Bank) (outD outG : ℕ) (mem : Memory w)
    (within : H≤P) (wide : P<2^w) (room : outG+N<2^w) (gap : outD+N≤outG)
    (safe : ∀B∈[owners,count,srcDepth,srcGain],B.Fits w outD)
    (rows : ∀B∈[owners,srcDepth,srcGain],N≤B.size)
    (pin : ∀t:Q,mem (owners.base+(ord t).val)=((owner t).val:Word w))
    (card : mem count.base=(H:Word w)) :
    ∃dst : Memory w,(masks owners count srcDepth srcGain outD outG P k D w).Exec mem dst
       ((4+48*N)+(4+48*N)) ∧
      (∀t:Q,dst (outD+(ord t).val)=if liveHost (H:=H) t then mem (srcDepth.base+(ord t).val) else 0) ∧
      (∀t:Q,dst (outG+(ord t).val)=if liveHost (H:=H) t then mem (srcGain.base+(ord t).val) else 0) ∧
      ∀a,(a<outD ∨ outG+N≤a)→dst a=mem a := by
  have mono : outD≤outG:=by omega
  let own (j : Fin N) : Fin P := owner ((rowOrd P k D).symm j)
  have ownerPin (i : Fin N) : mem (owners.base+i.val)=((own i).val:Word w) := by
    simpa only [own,Equiv.apply_symm_apply] using pin ((rowOrd P k D).symm i)
  have f (src : Bank) (good : src∈[owners,count,srcDepth,srcGain]) : (masked owners count src).Fits w outD :=
    ⟨⟨safe owners (by simp),trivial⟩,⟨safe count (by simp),trivial⟩,⟨safe src good,trivial⟩,trivial⟩
  obtain ⟨start,depth,saved⟩ := DescentHostCount.issued (H:=P)
    owners count (.lookup srcDepth .row) 0 outD N H own mem (f srcDepth (by simp))
    (by omega) (rows owners (by simp)) wide within ownerPin card
  let mid := image outD N (masked owners count srcDepth) mem
  have same (B : Bank) (inside : B∈[owners,count,srcDepth,srcGain]) (i : ℕ) (legal : i<B.size) :
      mid (B.base+i)=mem (B.base+i) :=
    saved _ (.inl ((Nat.add_lt_add_left legal B.base).trans_le (safe B inside).2.2))
  have later (B : Bank) (inside : B∈[owners,count,srcDepth,srcGain]) : B.Fits w outG :=
    ⟨(safe B inside).1,(safe B inside).2.1,(safe B inside).2.2.trans mono⟩
  have pins (i : Fin N) : mid (owners.base+i.val)=((own i).val:Word w) :=
    (same owners (by simp) _ (i.isLt.trans_le (rows owners (by simp)))).trans (ownerPin i)
  have count' : mid count.base=(H:Word w) := by
    have keep := same count (by simp) 0 (safe count (by simp)).1
    exact (show mid count.base=mem count.base by simpa only [Nat.add_zero] using keep).trans card
  obtain ⟨stop,gain,after⟩ := DescentHostCount.issued (H:=P)
    owners count (.lookup srcGain .row) 0 outG N H own mid
    ⟨⟨later owners (by simp),trivial⟩,⟨later count (by simp),trivial⟩,⟨later srcGain (by simp),trivial⟩,trivial⟩
    room (rows owners (by simp)) wide within pins count'
  refine ⟨image outG N (masked owners count srcGain) mid,?_,?_,?_,?_⟩
  · rw [Nat.mul_comm 48 N]
    intro labels regs slots machine
    exact Procedure.Exec.then start stop machine
  · intro t
    have hi := (ord t).isLt
    have keep := after (outD+(ord t).val) (.inl (by omega))
    have readDepth : (Expr.lookup srcDepth .row).eval mem ((ord t).val:Word w)=mem (srcDepth.base+(ord t).val) :=
      DescentPackedZip.bank_read srcDepth mem (hi.trans_le (rows srcDepth (by simp))) (safe srcDepth (by simp))
    by_cases hit : (owner t).val<H <;>
      simpa [masked,own,liveHost,hit,readDepth] using keep.trans (depth (ord t))
  · intro t
    have legal := (ord t).isLt.trans_le (rows srcGain (by simp))
    have readGain : (Expr.lookup srcGain .row).eval mid ((ord t).val:Word w)=mem (srcGain.base+(ord t).val) :=
      (DescentPackedZip.bank_read srcGain mid legal (later srcGain (by simp))).trans (same srcGain (by simp) _ legal)
    by_cases hit : (owner t).val<H <;>
      simpa [masked,own,liveHost,hit,readGain] using gain (ord t)
  · intro a outside
    rcases outside with lo | hi
    · exact (after a (.inl (lo.trans_le mono))).trans (saved a (.inl lo))
    · exact (after a (.inr hi)).trans (saved a (.inr ((Nat.add_le_add_right mono N).trans hi)))

end
end Hierarchy.DescentPackedRectangle.Canvas

end OAI
