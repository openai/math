import OAI.Hierarchy.DescentDatedSignedParentIssue
import OAI.Hierarchy.DescentOrdinaryMaterialShelf

namespace OAI
/-! Authenticate the signed input record itself from the first two ordinary post-matcher sweeps. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloWalkRAM DescentHaloPackedRebase DescentParallelBase.ParentFilter
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route
open scoped Classical Fin.CommRing
noncomputable section
private theorem castPorts (H G M a : ℕ) {D E : ℕ} (eqn : D=E) :
    cast (congrArg Ports (congrArg breadth eqn)) (PriorHeader.ports H G M D a)=PriorHeader.ports H G M E a :=by
  subst E;rfl

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "s" => v.signed
local notation "D" => DepotRAM.Shape.degree (v.ticket.depotShape v.short)
local notation "G" => v.material.groups
local notation "H" => v.material.oldHosts
local notation "M" => v.material.lanes
local notation "B" => v.material.blocks
variable (floor : ℕ) (c : v.SignedChart)
local notation "base" => v.donorEnd floor
local notation "mat" => PriorHeader.endAddress H G M D base
local notation "geo" => PriorHeader.rankBanks H G M D base
local notation "ports" => PriorHeader.ports H G M D base
local notation "I₀" => v.signedInput floor c
local notation "dRay" z => c.ray (Prod.fst (finProdFinEquiv.symm (Prod.snd z)))
local notation "seat" z => c.donorSeat (Prod.snd (finProdFinEquiv.symm (Prod.snd z)))
local notation "block" z => Fin.cast c.blocks (Prod.fst z)

theorem before_socket (z : (s).Socket) (f : Fin 9) :
    (s).donorSocket I₀ z f=v.materialSocket mat geo ports (dRay z) (seat z) (block z) f :=by
  let old:=PriorHeader.ports H G M (s).degree base
  let hd:=PriorHeader.rankBanks H G M (s).degree base
  have head : hd=geo:=congrArg (fun degree₀=>PriorHeader.rankBanks H G M degree₀ base) c.degree
  have table : v.materialStart floor=mat:=congrArg (fun degree₀=>PriorHeader.endAddress H G M degree₀ base) c.degree
  have ray:=castPorts H G M base c.degree
  have eqn (f : Fin 9):
      v.materialSocket (v.materialStart floor) hd (cast (congrArg Ports (congrArg breadth c.degree)) old)
        (dRay z) (seat z) (block z) f=v.materialSocket mat geo ports (dRay z) (seat z) (block z) f:=by
    rw [head,table,show cast (congrArg Ports (congrArg breadth c.degree)) old=ports from ray]
  fin_cases f <;> apply eqn

def rerouted {a b degree₀ E : ℕ} (hosts : a=b) (degree : degree₀=E) (R : Fin a→Fin degree₀→Option (Fin a)) :
    Fin b→Fin E→Option (Fin b):=by subst b;subst E;exact R
def rebasedRaw {a b degree₀ E Q K L bits : ℕ} (hosts : a=b) (degree : degree₀=E) (R : Fin a→Fin degree₀→Option (Fin a))
    (raw : Option (Fused.Raw R Q K L bits)) : Option (Fused.Raw (rerouted hosts degree R) Q K L bits):=by
  subst b;subst E;exact raw

private theorem reindex_port {a b degree₀ E Q K L bits : ℕ} (hosts : a=b) (degree : degree₀=E)
    (R : Fin a→Fin degree₀→Option (Fin a)) (r : Option (Fused.Raw R Q K L bits)) (f : Fin 9) :
    atPort (rerouted hosts degree R) (rebasedRaw hosts degree R r) f=atPort R r f:=by
  subst b;subst E;rfl

private theorem reindex_location {a b degree₀ E Q K L bits regions : ℕ} (hosts : a=b) (degree : degree₀=E)
    (pitch:ℕ) (h : Fin regions) (R : Fin a→Fin degree₀→Option (Fin a)) (r : Option (Fused.Raw R Q K L bits))
    (original : ∀u,r=some u → receiver a pitch h=some u.receiver.1 ∧
      Gather.select (Gather.reaching R) u.receiver.1 u.path=some u.host) :
    ∀u,rebasedRaw hosts degree R r=some u → receiver b pitch h=some u.receiver.1 ∧
      Gather.select (Gather.reaching (rerouted hosts degree R)) u.receiver.1 u.path=some u.host:=by
  subst b;subst E;exact original

variable (hosts : v.material.oldHosts=v.signed.priorHosts)
    (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts)) (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short))
    (bands : v.material.oldGroups=v.material.groups*v.material.blocks)
    (room : Fused.capacity (v.ticket.depotShape v.short).degree v.signed.lowSites v.signed.tickets v.signed.cap≤2^v.material.fieldBits)
    (pitch : 0<v.materialPitch) (inside : v.materialPitch≤ v.signed.lowSites)
    (bound : ∀h g z,DepotRAM.Material.ParentRoom (v.ticket.depotShape v.short) v.materialFormat (state h g)
        (digest (DepotRAM.Material.reverseEntries (v.ticket.depotShape v.short) R h)) z v.signed.lowSites v.signed.tickets v.signed.cap)
def signedIncoming (z : (s).Socket) (h : Fin (s).hosts) (g : Fin (s).groups) :=
  rebasedRaw hosts c.degree.symm R
    (v.incoming R state bands room pitch inside bound (dRay z) (seat z) (block z) h g)
local notation "reached" => v.signedIncoming c hosts R state bands room pitch inside bound

theorem signed_parent_run {w : ℕ} (parts adj : Bank) (pre : PriorHeader.Room adj H G M D base w)
    (paid : v.MaterialRoom mat parts (geo).reverseRank w) (previous : parts.base+parts.size≤base)
    (pos : 0<(e).oldLanes) (hm : 0<M) (hb : 0<B) (grows : H≤(e).hosts)
    (m after : Memory w)
    (neighbors : ∀h j,m (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (board : Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (e).oldLanes m)
    (nextBase : ℕ) (order : v.materialEnd floor≤nextBase)
    (keep : ∀a<v.materialEnd floor,after a=(v.beforeSignedMaterial floor parts adj w).image m a) :
    (s).Donors I₀ (rerouted hosts c.degree.symm R) reached nextBase after :=by
  let done:=(v.beforeSignedMaterial floor parts adj w).image m
  have startEq : v.materialStart floor=mat:=congrArg (fun degree₀=>PriorHeader.endAddress H G M degree₀ base) c.degree
  have roof:v.materialEnd floor=(e).endAddress mat:=congrArg (e).endAddress startEq
  refine (s).donors_held I₀ _ reached done after (old:=v.materialEnd floor) ?_ ?_ order keep ?_
  · intro z f
    rw [v.before_socket floor c z f]
    simp only [signedIncoming]
    rw [show done=(v.beforeSignedMaterial floor parts adj w).image m from rfl,v.material_to_issued parts adj floor c.degree]
    have portsEq :
        (fun h g=>atPort (rerouted hosts c.degree.symm R)
          (rebasedRaw hosts c.degree.symm R (v.incoming R state bands room pitch inside bound (dRay z) (seat z) (block z) h g)) f)=
        (fun h g=>atPort R (v.incoming R state bands room pitch inside bound (dRay z) (seat z) (block z) h g) f) :=by
      funext h g
      exact reindex_port hosts c.degree.symm R _ f
    have actual := v.real_parent_sources base parts adj pre paid previous pos hm hb bands grows m R state neighbors board
      room pitch inside bound (dRay z) (seat z) (block z) f
    apply (congrArg (fun cells => Source (v.materialSocket mat geo ports (dRay z) (seat z) (block z) f) cells M _) portsEq).mpr
    exact actual
  · intro z f
    rw [v.before_socket floor c z f,roof]
    let j:=DepotRAM.Material.Sheets.id fmt (donorField f) (seat z)
    have seen:=v.received_fit mat ((e).endAddress mat) w le_rfl paid.range hm hb bands grows j
    have order':mat≤(e).endAddress mat:=by rw [MaterialExtent.translated];exact Nat.le_add_right ..
    apply v.material_socket_fits mat _ w le_rfl paid.range paid.sameReach geo ports _ _ _ f
    exact (PriorHeader.accessible base adj pre (v.receivedBank mat j) _ order' seen.1 seen.2).2
  · intro z h g u eqn
    exact reindex_location hosts c.degree.symm v.materialPitch h R _
      (fun t is=>v.incoming_location R state bands room pitch inside bound _ _ _ h g is) u eqn

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
