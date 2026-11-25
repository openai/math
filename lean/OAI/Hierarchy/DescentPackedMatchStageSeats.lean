import OAI.Hierarchy.DescentPackedMatchFlatWords
import OAI.Hierarchy.DescentPackedMatchSourceSeat

namespace OAI
/-! # Native fields and selector ranks on the same all-key source seat -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentHostDirectory DescentSIMDLookup
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H G M : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {gadget : PoweredGadget F} {price ε : ℝ}
variable (he : 0≤ε) (A : GroupStage W gadget price ε J V k)
variable (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "addr" => nativeAddress he A.stage
local notation "K" => 2^(k+1)
local notation "C" => ScanColonies he A.stage

def keyAt (c : C) : Fin K :=
  ⟨heap (addr c).2,heap_fits ((Finset.mem_product.mp (Finset.mem_product.mp (nativeAddress_legal he A.stage c)).2).1)⟩

def sourceIndex : C ↪ Fin (K*H)×Fin G :=
  (sourceChart he A groups hosts).trans finProdFinEquiv.symm.toEmbedding

theorem sourceIndex_eq (c : C) :
    sourceIndex he A groups hosts c=(finProdFinEquiv (keyAt he A c,hosts (addr c).1.2),groups (addr c).1.1) := by
  exact finProdFinEquiv.symm_apply_apply _

def wordCast : Fin (K*(H*chunks G M)) ≃ Fin ((K*H)*chunks G M) :=
  finCongr (Nat.mul_assoc ..).symm

def slot : C ↪ Fin ((K*H)*chunks G M)×Fin M :=
  (sourceSeat he A groups hosts hm).trans ((wordCast (k:=k) (H:=H) (G:=G) (M:=M)).prodCongr (Equiv.refl (Fin M))).toEmbedding

theorem slot_eq (c : C) :
    slot he A groups hosts hm c =
      (row (K*H) G M (position (sourceIndex he A groups hosts c).1 (sourceIndex he A groups hosts c).2 hm),
        lane (sourceIndex he A groups hosts c).2 hm) := by
  rw [sourceIndex_eq]
  apply Prod.ext
  · apply Fin.ext
    have a:=seatOf_word k (nativeAddress he A.stage) (nativeAddress_legal he A.stage) groups hosts hm c
    change ((sourceSeat he A groups hosts hm c).1).val = _
    apply a.trans
    let q := heap (addr c).2
    let h := (hosts (addr c).1.2).val
    let j := (groups (addr c).1.1).val/M
    change q*(H*chunks G M)+(j+chunks G M*h) = j+chunks G M*(h+H*q)
    ring
  · rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
