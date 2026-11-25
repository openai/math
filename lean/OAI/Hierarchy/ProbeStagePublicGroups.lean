import OAI.Hierarchy.ProbeAdvisedPurchase
import OAI.Hierarchy.ProbeStageReadback

namespace OAI
/-! # Fixed group addresses on the actual native stage columns -/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM ProbeStage ProbeStage.Native
open scoped Fin.CommRing Classical
noncomputable section

variable {z d w : ℕ}

def stageNumber (t : StageAt z d) : Fin (2*rounds d+1) :=
  t.cast (template_length ..)

theorem matching_card (π : Equiv.Perm (Fin (2^z))) (s : Fin (2*rounds d+1)) :
    Fintype.card (stageMatching π s).shape.Group=(stageMatching π s).count := by
  have outer (j : Fin (rounds d)) (forward : Bool) :
      Fintype.card (numberedOuter π j forward).shape.Group=(numberedOuter π j forward).count := by
    change Fintype.card ((history z d π j.val).shape.Group × Fin _) = _
    rw [Fintype.card_prod,Fintype.card_fin,history_card]
    rfl
  unfold stageMatching
  split
  · exact outer ..
  · split
    · exact history_card ..
    · exact outer ..

private def retile {R : Type} (l : RoutedLayer R) (s : Shape) (e : l.shape=s) : Tiles R s.Group s.span :=
  e ▸ l.tiles

private theorem retile_layer {R : Type} (l : RoutedLayer R) (s : Shape) (e : l.shape=s) :
    layer (retile l s e)=l := by subst s; cases l; rfl

theorem route_get (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d) :
    (advisedRoute z d π).layers[t.val]? = some (layer (advisedStage z d π t)) := by
  let path := advisedRoute z d π
  have shapes := path.layer_shapes
  have len : path.layers.length=(permutationFabric z d).shapes.length := by
    simpa only [List.length_map] using congrArg List.length shapes
  have bound : t.val<path.layers.length := by simpa only [len] using t.isLt
  let l := path.layers[t.val]
  have shape : l.shape=stageAt z d t := by
    have found := congrArg (fun ls => ls[t.val]?) shapes
    simpa [l,stageAt,List.getElem?_eq_getElem,bound,t.isLt] using found
  change path.layers[t.val]? = some (layer (retile l (stageAt z d t) shape))
  rw [List.getElem?_eq_getElem bound,retile_layer]

private theorem sameLayer (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d) :
    layer (stageMatching π (stageNumber t)).tiles=layer (advisedStage z d π t) :=
  Option.some.inj ((stageMatching_route π (stageNumber t)).symm.trans (route_get π t))

private theorem sameShape (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d) :
    (stageMatching π (stageNumber t)).shape=stageAt z d t :=
  congrArg RoutedLayer.shape (sameLayer π t)

private theorem sameCount (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d) :
    (stageMatching π (stageNumber t)).count=Fintype.card (stageAt z d t).Group :=
  (matching_card π (stageNumber t)).symm.trans
    (congrArg (fun s : Shape => Fintype.card s.Group) (sameShape π t))

/-- The format uses the native mixed-radix order. Its group inverse is a fixed public owner lookup. -/
def groupNumber (t : StageAt z d) : (stageAt z d t).Group ≃ Fin (Fintype.card (stageAt z d t).Group) :=
  (groupFormat (stageMatching (Equiv.refl _) (stageNumber t))).onShape (stageAt z d t)
    (sameShape (Equiv.refl _) t) (sameCount (Equiv.refl _) t)

private def Numbered {n : ℕ} (fmt : GroupNumbering) (group input output : Bank) (mem : Memory w) (l : RoutedLayer (Fin n)) : Prop :=
  ∃ (shape : fmt.shape=l.shape) (count : fmt.count=Fintype.card l.shape.Group),
    Resident group mem (fun r => ((fmt.onShape l.shape shape count) (l.tiles.group r)).val) ∧
    Resident input mem (fun r => (l.tiles.input r).val) ∧
    Resident output mem (fun r => (l.tiles.output r).val)

/-- All three native columns are read according to the public mixed-radix numbering. -/
theorem stage_numbered (π : Equiv.Perm (Fin (2^z))) (t : StageAt z d)
    (input : Memory (wordBits z d copies)) (done : After (d:=d) π input (rounds d)) :
    let s := stageNumber t
    let mem := images z d input (rounds d)
    let p := advisedStage z d π t
    Resident (stageBank z d s 0) mem (fun r => (groupNumber t (p.group r)).val) ∧
      Resident (stageBank z d s 1) mem (fun r => (p.input r).val) ∧
      Resident (stageBank z d s 2) mem (fun r => (p.output r).val) := by
  let s := stageNumber t
  let p := stageMatching π s
  let fmt := groupFormat p
  let mem := images z d input (rounds d)
  have stored : Numbered fmt (stageBank z d s 0) (stageBank z d s 1) (stageBank z d s 2) mem (layer p.tiles) :=
    ⟨rfl,(matching_card π s).symm,stageBank_reads π input done s 0,
      stageBank_reads π input done s 1,stageBank_reads π input done s 2⟩
  change Numbered fmt (stageBank z d s 0) (stageBank z d s 1) (stageBank z d s 2) mem (layer (stageMatching π (stageNumber t)).tiles) at stored
  rw [sameLayer π t] at stored
  obtain ⟨hs,hc,groups,ports,targets⟩ := stored
  have equal := GroupNumbering.onShape_congr (stage_numbering π (Equiv.refl _) s)
    (stageAt z d t) hs (sameShape (Equiv.refl _) t) hc (sameCount (Equiv.refl _) t)
  change fmt.onShape (stageAt z d t) hs hc=groupNumber t at equal
  change Resident (stageBank z d s 0) mem (fun r =>
    ((fmt.onShape (stageAt z d t) hs hc) ((advisedStage z d π t).group r)).val) at groups
  rw [equal] at groups
  exact ⟨groups,ports,targets⟩

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
