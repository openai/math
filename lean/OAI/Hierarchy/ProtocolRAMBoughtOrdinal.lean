import OAI.Hierarchy.ProbeRetainedOrdinals
import OAI.Hierarchy.ProtocolRAMPurchaseKey
import OAI.Hierarchy.ProtocolRAMPurchaseMarks

namespace OAI
/-! # Injective original DFS ordinals of the bought catalogue rows -/

namespace Hierarchy.ProtocolRAM.BoughtLocation
open AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))} {depth : ℕ}
  {marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z))}

def keyOf (p : LiveChains S π depth marked) : Key z d k :=
  key p.1 ((PurchaseMarks.signedDirection k).symm p.2.1)

/-- The same witness supplies the decision flag and every tile, even if the
sampler's branch-word enumeration contains repeated paths. -/
def localIndex (p : LiveChains S π depth marked) : PurchaseDirectory.Index (2^z) S.degree depth :=
  (StripDirectory.retainedRows S π depth marked p).choose

def localRow (p : LiveChains S π depth marked) : Fin (paths z S.degree depth) :=
  ⟨(localIndex p).val,by simpa [PurchaseFrozen.paths] using (localIndex p).isLt⟩

def relative (p : LiveChains S π depth marked) : Fin (count z d k * paths z S.degree depth) :=
  finProdFinEquiv (keyOf p,localRow p)

theorem relative_val (p : LiveChains S π depth marked) :
    (relative p).val = (keyOf p).val*paths z S.degree depth+(localIndex p).val := by
  change (localIndex p).val+paths z S.degree depth*(keyOf p).val=_
  ac_rfl

theorem relative_injective : Function.Injective (relative (S:=S) (π:=π) (depth:=depth) (marked:=marked)) := by
  intro p q eq
  have pair : (keyOf p,localRow p)=(keyOf q,localRow q) := finProdFinEquiv.injective eq
  have keyEq : keyOf p=keyOf q := congrArg Prod.fst pair
  have rowEq : localIndex p=localIndex q := Fin.ext (congrArg (fun t => t.2.val) pair)
  have st : p.1=q.1 := by simpa only [keyOf,stage_key] using congrArg (stage (z:=z) (d:=d) (k:=k)) keyEq
  have dir : p.2.1=q.2.1 := (PurchaseMarks.signedDirection k).symm.injective (by
    simpa only [keyOf,axis_key] using congrArg (axis (z:=z) (d:=d) (k:=k)) keyEq)
  have tile : liveRow S π depth marked p 0=liveRow S π depth marked q 0 := by
    apply Fin.castSucc_injective _
    let first (t : StageAt z d) (i : PurchaseDirectory.Index (2^z) S.degree depth) :=
      let choice:=ProtocolRAMPurchaseOwners.successor (advisedStage z d π t)
        (Fintype.equivFin (stageAt z d t).Group).toEmbedding (D:=S.degree)
        (portDigits (S.rows (stageAt z d t).span))
      PurchaseColumns.rowTile choice i 0
    have rows (r : LiveChains S π depth marked) :
        first r.1 (localIndex r)=(liveRow S π depth marked r 0).castSucc :=
      (StripDirectory.retainedRows S π depth marked r).choose_spec.2 0
    have pHit := rows p
    rw [st,rowEq] at pHit
    exact pHit.symm.trans (rows q)
  have same : (p,(0:Fin (depth+1)))=(q,0) :=
    (liveSlots S π depth marked).injective (congrArg Sum.inr (Prod.ext (Prod.ext tile st) dir))
  exact congrArg Prod.fst same

end
end Hierarchy.ProtocolRAM.BoughtLocation

end OAI
