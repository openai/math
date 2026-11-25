import OAI.Hierarchy.DescentDatedPhysicalMatcherIndex
import OAI.Hierarchy.DescentDatedMaterialPhase
import OAI.Hierarchy.DescentDatedOperandHeadShape
import OAI.Hierarchy.DescentDatedSourcePathPages
import OAI.Hierarchy.DescentDatedDenseRankColumns
import OAI.Hierarchy.DescentOrdinaryMaterialSocket
import OAI.Hierarchy.DescentDatedOperandPages

namespace OAI
/-! # Material values for the retained cable and the original newborn at their dated receiver -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedZip
open DescentRawCablePanel DescentHaloWalkRAM DescentSharedCableNames
open scoped Classical Fin.CommRing
open DescentPackedColony DescentHaloPackedRebase DescentDatedOperandPages DescentDatedSourcePathDirectory
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
set_option hygiene false
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "O" => DepotRAM.Material.roles fmt₀
local notation "G" => (e₀).groups
local notation "B" => (e₀).blocks
local notation "b" => (e₀).fieldBits
local notation "val₀" => Fin K → Fin G → Cell b
set_option hygiene true

def rawMaterialValue (R : Fin H → Fin (fmt₀).degree → Option (Fin H))
    (state : Fin H → Fin (e₀).oldGroups → DepotRAM.Parts fmt₀) (bands : (e₀).oldGroups=G*B)
    (x : Fin B) (f : Fin 6) (i : Fin (P₀*O)) : Fin (e₀).hosts → Fin (e₀).groups → Cell (e₀).fieldBits :=
  let (p,z):=finProdFinEquiv.symm i
  let seat:=(DepotRAM.Material.seatIndex fmt₀).symm z
  let cal:=DepotRAM.Material.reverseEntries fmt₀ R
  let sheetFields:=DepotRAM.Material.Sheets.fields fmt₀ v.materialFormat state (fun h (_ : Fin (e₀).oldGroups)=>digest (cal h))
  DepotRAM.Material.Route.value R v.materialPitch p 0 x (fun h g=>
    sheetFields (DepotRAM.Material.Sheets.rawId fmt₀ f seat) h (g.cast bands.symm))

def matchedFieldValue (R : Fin H → Fin D → Option (Fin H))
    (state : Fin H → Fin (e₀).oldGroups → DepotRAM.Parts fmt₀) (bands : (e₀).oldGroups=G*B)
    (j : Fin (count fmt₀)) (p : Fin P₀) (x : Fin B) : Fin (e₀).hosts → Fin (e₀).groups → Cell (e₀).fieldBits :=
  DepotRAM.Material.Route.value R v.materialPitch p 0 x (fun h g=>
    law fmt₀ v.profile b j.val (DepotRAM.combine fmt₀ (state h (g.cast bands.symm))))

def matchOldIndex (i : Fin (P₀*((fmt₀).blocks*(D*(fmt₀).cap)))) (f : Fin 4) :=
  let (p,t):=finProdFinEquiv.symm i
  let (x,slot):=finProdFinEquiv.symm t
  let (peer,first):=finProdFinEquiv.symm slot
  (p,header fmt₀ x peer first f)

def narrowValue (R : Fin H → Fin D → Option (Fin H)) (key : v.NarrowHead) (h : Fin K) (_ : Fin G) : Cell (Packed.bits P₀) :=
  let receiver:=DepotRAM.Material.Route.receiver H v.materialPitch h
  match key with
  | .inl i=>let (p,d):=finProdFinEquiv.symm i
            receiver.elim 0 (fun z=>DescentDatedSourcePathDirectory.token R z p d)
  | .inr p=>receiver.elim 0 (fun z=>Local.token R z p)

variable (R : Fin H → Fin D → Option (Fin H)) (state : Fin H → Fin (e₀).oldGroups → DepotRAM.Parts fmt₀)
variable (bands : (e₀).oldGroups=G*B) (serial peer : Fin B → Fin (P₀*O) → val₀)

def wideMaterialValues (key : v.WideHead) : val₀ :=
  match key with
  | .inl (x,f,i)=>
    let slot:=v.matchOldIndex i f
    v.matchedFieldValue R state bands slot.2 slot.1 x
  | .inr (.inl (x,f,i))=>
    let slot:=v.matchAnchorIndex i f
    v.matchedFieldValue R state bands slot.2 slot.1 x
  | .inr (.inr (x,f,i))=>
    if raw : f.val<6 then v.rawMaterialValue R state bands x ⟨f.val,raw⟩ i
    else if f.val=6 then serial x i else peer x i

theorem raw_value_at_donor (p : Fin P₀) (x : Fin B) (z : DepotRAM.Material.Seat fmt₀) (f : Fin 6)
    (h : Fin K) (g : Fin G) (recv donor : Fin H) (atHost : DepotRAM.Material.Route.receiver H v.materialPitch h=some recv)
    (selected : Gather.select (Gather.reaching R) recv p=some donor) :
    v.rawMaterialValue R state bands x f (finProdFinEquiv (p,DepotRAM.Material.seatIndex fmt₀ z)) h g=
      DepotRAM.Material.rawObserved fmt₀ v.materialFormat (state donor ((finProdFinEquiv (g,x)).cast bands.symm))
        (digest (DepotRAM.Material.reverseEntries fmt₀ R donor)) z f :=by
  have gate : ¬(9+f.val<9):=by omega
  simp [rawMaterialValue,DepotRAM.Material.Route.value,DepotRAM.Material.Route.selected,atHost,selected,
    DepotRAM.Material.Route.gated,DepotRAM.Material.Sheets.fields,DepotRAM.Material.Sheets.fieldId,DepotRAM.Material.Sheets.rawId,
    DepotRAM.Material.Sheets.rawIndex,DepotRAM.Material.Sheets.allFields,gate,Option.elim]
  rfl

theorem matched_field_at_donor (j : Fin (DescentDatedOperandPages.count fmt₀)) (p : Fin P₀) (x : Fin B)
    (h : Fin K) (g : Fin G) (recv donor : Fin H) (atHost : DepotRAM.Material.Route.receiver H v.materialPitch h=some recv)
    (selected : Gather.select (Gather.reaching R) recv p=some donor) :
    v.matchedFieldValue R state bands j p x h g=DescentDatedOperandPages.law fmt₀ v.profile b j.val
      (DepotRAM.combine fmt₀ (state donor ((finProdFinEquiv (g,x)).cast bands.symm))) :=by
  simp [matchedFieldValue,DepotRAM.Material.Route.value,DepotRAM.Material.Route.selected,atHost,selected,DepotRAM.Material.Route.gated]



end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
