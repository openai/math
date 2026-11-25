import OAI.Hierarchy.TaggedWireInstalledRows
import OAI.Hierarchy.ProtocolRAMRepairCommodity
import OAI.Hierarchy.ProbeStripOccupancy
import OAI.Hierarchy.TaggedWireGoodsDistinct

namespace OAI
/-! Actual endpoint graphs behind the retained and paid portions of the installed row order. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard AdaptiveProbe Strip WireTelescope ChosenPackets
open scoped Classical Fin.CommRing
variable {h d k K n : ℕ} {A I Ball : Type}
local notation "G" => Commodity (Fin (2^h)) (Stages h d) k
local notation "num" => Fintype.card G

def stockOrder (h d k : ℕ) : Commodity (Fin (2^h)) (Stages h d) k≃Fin (Fintype.card (Commodity (Fin (2^h)) (Stages h d) k)) :=
  (PurchaseInventory.slotEquiv h (Stages h d) k).trans (finCongr (PurchaseInventory.card_commodity h (Stages h d) k).symm)

def earnedInventory (π : Equiv.Perm (Fin (2^h))) (name : Site h d k↪Fin K) :
    PortGraph (Fin K) (Fin num) :=
  ⟨fun i=>name (commodityEnds π ((stockOrder h d k).symm i)).1,
    fun i=>name (commodityEnds π ((stockOrder h d k).symm i)).2⟩

def earnedCatalogue (entry : Fin n→Site h d k×Site h d k) (name : Site h d k↪Fin K) :
    PortGraph (Fin K) (Fin n) := ⟨fun e=>name (entry e).1,fun e=>name (entry e).2⟩

def installedRows (π : Equiv.Perm (Fin (2^h))) (entry : Fin n→Site h d k×Site h d k)
    (name : Site h d k↪Fin K) (pad : Chord K) : Fin (num+n)→Chord K :=
  unionRows (earnedInventory π name) (earnedCatalogue entry name) pad

theorem installed_paid (π : Equiv.Perm (Fin (2^h))) (entry : Fin n→Site h d k×Site h d k)
    (name : Site h d k↪Fin K) (pad : Chord K) (e : Fin n) (distinct : (entry e).1≠(entry e).2) :
    installedRows π entry name pad (Fin.natAdd num e)=Probe.orderedEnds
      (name (entry e).1) (name (entry e).2) (name.injective.ne distinct) := by
  change unionRows _ _ pad (paidRow (g:=num) e)=_
  simp only [unionRows,paidRow,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
  exact dite_eq_right (name.injective.ne distinct)

theorem installed_stock (π : Equiv.Perm (Fin (2^h))) (entry : Fin n→Site h d k×Site h d k)
    (name : Site h d k↪Fin K) (pad : Chord K) (place : Ball×I↪Fin K)
    (u : Ball) (extra : A→DistinctPair I) (a : A) (item : G)
    (source : place (u,(extra a).left)=name (commodityEnds π item).1)
    (target : place (u,(extra a).right)=name (commodityEnds π item).2) :
    installedRows π entry name pad (stockRow (p:=n) (stockOrder h d k item))=
      reportedRole place extra u a := by
  unfold installedRows unionRows stockRow
  rw [Function.comp_apply,Equiv.symm_apply_apply]
  change filledChord (earnedInventory π name) pad (stockOrder h d k item)=_
  simp only [earnedInventory,filledChord,Equiv.symm_apply_apply,dite_eq_right (name.injective.ne (goods_different π item))]
  apply Subtype.ext
  by_cases lt : name (commodityEnds π item).1<name (commodityEnds π item).2
  all_goals simp [reportedRole,Probe.orderedEnds,orderedChord,source,target,lt]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
