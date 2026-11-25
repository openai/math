import OAI.Hierarchy.DescentMaterialSocketProgram
import OAI.Hierarchy.DescentDatedMaterialIssued
import OAI.Hierarchy.DescentMaterialSocketRoom

namespace OAI
/-! Actual earlier expressions for the nine fields of an ordinary signed receiving socket. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloPackedRebase DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
local notation "e" => v.material
local notation "s" => v.ticket.depotShape v.short
local notation "H" => v.material.oldHosts
local notation "P₀" => breadth (DepotRAM.Shape.degree (v.ticket.depotShape v.short))
local notation "b" => v.material.fieldBits
local notation "M" => v.material.lanes
local notation "G₁" => v.material.groups
local notation "B" => v.material.blocks
local notation "RouteField" => DepotRAM.Material.Route.Port
variable (base : ℕ) (ranks : DescentOrdinaryDonorRankDirectory.Banks) (previous : Ports (breadth (v.ticket.depotShape v.short).degree))
def bankSocket (j : Fin (DepotRAM.Material.Sheets.count s)) (path : Fin P₀) (x : Fin B) (f : RouteField) : Expr :=
  v.materialProgram.bankSocket base ranks previous j path x f

def materialSocket (path : Fin P₀) (seat : DepotRAM.Material.Seat s) (x : Fin B) (f : RouteField) : Expr :=
  v.materialProgram.materialSocket base ranks previous path seat x f

private theorem castRead {hosts groups slots lanes width memWidth : ℕ} (eqn : groups=slots)
    (values : Fin hosts→Fin groups→Cell width) (src : Bank) (mem : Memory memWidth)
    (old : DescentPackedColony.Reads src values lanes mem) :
    DescentPackedColony.Reads src (fun h (j : Fin slots)=>values h (Fin.cast eqn.symm j)) lanes mem :=by
  subst slots
  exact old

variable {w : ℕ} {parts : Bank} (m : Memory w) (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts))
variable (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short))
local notation "run" => v.materialAt base parts ranks.reverseRank w
local notation "image" => NativePhase.image run m
local notation "cal" => DepotRAM.Material.reverseEntries s R
local notation "rev" => fun h (_:Fin v.material.oldGroups)=>digest (cal h)
local notation "words" => DepotRAM.Material.Sheets.fields s v.materialFormat state rev
def socketValue (bands : (e).oldGroups=G₁*B) (path : Fin P₀) (seat : DepotRAM.Material.Seat s) (x : Fin B) (f : RouteField) :=
  value (K:=v.material.hosts) R v.materialPitch path f x (fun h g=>words (DepotRAM.Material.Sheets.id s (donorField f) seat) h (Fin.cast bands.symm g))

theorem bank_socket_issued (ok : v.MaterialRoom base parts ranks.reverseRank w)
    (priorWidth : 0<(e).oldLanes) (lanes : 0<M) (blocks : 0<B) (bands : (e).oldGroups=G₁*B)
    (oldRank : ∀h p,m (ranks.reverseRank.base+(finProdFinEquiv (h,p)).val)=((cal h p).val:Word w))
    (old : Reads parts (fun h g=>DepotRAM.combine s (state h g)) (e).oldLanes m)
    (path : Fin P₀) (j : Fin (DepotRAM.Material.Sheets.count s)) (x : Fin B) (f : RouteField) (out : ℕ)
    (order : (e).endAddress base≤out) (room : out<2^w) (rows : H*chunks G₁ M<2^w)
    (earlier : Accessible (keepPorts ranks previous) (v.receivedBank base j) H G₁ M w out)
    (mounted : Mounted previous (Gather.reaching R) image G₁ M)
    (issued : DescentOrdinaryDonorRankDirectory.Reads R ranks image) :
    Source (v.bankSocket base ranks previous j path x f) (value (K:=v.material.hosts) R v.materialPitch path f x (fun h g=>words j h (Fin.cast bands.symm g))) M image :=by
  have retained:=castRead bands (words j) (v.receivedBank base j) image
    (v.material_issued ok m R state priorWidth oldRank old j)
  let first:=(((v.materialCharts base w).seq (v.materialJoin base parts ranks.reverseRank w)).seq (v.materialSheets base w)).seq
    ((v.materialJob base).phase ((e).overlapStart base) w)
  let prev:=first.image m
  let stage:=Projection.stage H (e).hosts G₁ M P₀ b B v.materialPitch ((e).projectionStart base) w
  have agree : image=stage.image prev :=by
    change (Projection.stage H (e).hosts G₁ M (e).reach b B v.materialPitch ((e).projectionStart base) w).image prev =
      (Projection.stage H (e).hosts G₁ M P₀ b B v.materialPitch ((e).projectionStart base) w).image prev
    rw [ok.sameReach]
  have buy:Projection.roof b B M (e).hosts G₁ P₀ ((e).projectionStart base)≤out:=by rw [←ok.sameReach,v.stampedRoof];exact order
  rw [agree] at retained mounted issued ⊢
  exact Projection.source_at ((e).projectionStart base) out buy room R ranks previous (v.receivedBank base j) f path x _
    v.materialPitch prev lanes blocks retained earlier mounted issued rows

def rawSocket (path : Fin P₀) (seat : DepotRAM.Material.Seat s) (x : Fin B) (f : Fin 6) :=
  v.bankSocket base ranks previous (DepotRAM.Material.Sheets.rawId s f seat) path x 0

theorem material_socket_issued (ok : v.MaterialRoom base parts ranks.reverseRank w)
    (priorWidth : 0<(e).oldLanes) (lanes : 0<M) (blocks : 0<B) (bands : (e).oldGroups=G₁*B)
    (oldRank : ∀h p,m (ranks.reverseRank.base+(finProdFinEquiv (h,p)).val)=((cal h p).val:Word w))
    (old : Reads parts (fun h g=>DepotRAM.combine s (state h g)) (e).oldLanes m)
    (path : Fin P₀) (seat : DepotRAM.Material.Seat s) (x : Fin B) (f : RouteField) (out : ℕ)
    (order : (e).endAddress base≤out) (room : out<2^w) (rows : H*chunks G₁ M<2^w)
    (earlier : Accessible (keepPorts ranks previous) (v.receivedBank base (DepotRAM.Material.Sheets.id s (donorField f) seat)) H G₁ M w out)
    (mounted : Mounted previous (Gather.reaching R) image G₁ M)
    (issued : DescentOrdinaryDonorRankDirectory.Reads R ranks image) :
    Source (v.materialSocket base ranks previous path seat x f) (v.socketValue R state bands path seat x f) M image :=v.bank_socket_issued base ranks previous m R state ok priorWidth lanes blocks bands oldRank old path
  (DepotRAM.Material.Sheets.id s (donorField f) seat) x f out order room rows earlier mounted issued

theorem material_raw_issued (ok : v.MaterialRoom base parts ranks.reverseRank w)
    (priorWidth : 0<(e).oldLanes) (lanes : 0<M) (blocks : 0<B) (bands : (e).oldGroups=G₁*B)
    (oldRank : ∀h p,m (ranks.reverseRank.base+(finProdFinEquiv (h,p)).val)=((cal h p).val:Word w))
    (old : Reads parts (fun h g=>DepotRAM.combine s (state h g)) (e).oldLanes m)
    (path : Fin P₀) (seat : DepotRAM.Material.Seat s) (x : Fin B) (f : Fin 6) (out : ℕ)
    (order : (e).endAddress base≤out) (room : out<2^w) (rows : H*chunks G₁ M<2^w)
    (earlier : Accessible (keepPorts ranks previous) (v.receivedBank base (DepotRAM.Material.Sheets.rawId s f seat)) H G₁ M w out)
    (mounted : Mounted previous (Gather.reaching R) image G₁ M)
    (issued : DescentOrdinaryDonorRankDirectory.Reads R ranks image) :
    Source (v.rawSocket base ranks previous path seat x f) (value (K:=v.material.hosts) R v.materialPitch path (0:RouteField) x (fun h g=>DepotRAM.Material.rawObserved s v.materialFormat (state h (Fin.cast bands.symm g)) (rev h (Fin.cast bands.symm g)) seat f)) M image :=by
  let j:=DepotRAM.Material.Sheets.rawId s f seat
  simpa only [j,rawSocket,DepotRAM.Material.Sheets.fields,DepotRAM.Material.Sheets.rawId,DepotRAM.Material.Sheets.fieldId,
    Equiv.symm_apply_apply,DepotRAM.Material.Sheets.allFields,DepotRAM.Material.Sheets.rawIndex,Fin.val_mk,
    Nat.not_lt_of_ge (Nat.le_add_right 9 _),dite_false,Nat.add_sub_cancel_left] using
    (v.bank_socket_issued base ranks previous m R state ok priorWidth lanes blocks bands oldRank old path j x 0 out order room rows earlier mounted issued)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
