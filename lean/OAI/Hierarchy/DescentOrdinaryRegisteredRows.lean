import OAI.Hierarchy.DescentOrdinarySelectedMeasure
import OAI.Hierarchy.DescentOrdinaryVenueClipRun

namespace OAI
/-! # All operand pages of the ordinary gather from the previous physical raster -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentPackedZip DescentSIMDLookup DescentRawCablePanel
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryReferenceInputs DescentSharedCableNames
open DescentHaloWalkRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)

variable (S : A.InputShape v) (floor : ℕ) («matching» : A.Match v floor)
local notation "H₀" => A.clip.venue.hosts
local notation "G₀" => A.clip.venue.groups
local notation "M₀" => A.clip.working
local notation "L₀" => A.population v floor
local notation "P₀" => A.ports v floor
local notation "R₀" => A.directory v floor «matching»
local notation "C₀" => v.refChart floor

local notation "Nv" => v.reference.newNodes
local notation "names₀" => v.reference.nameBits
local notation "count₀" => v.reference.countBits
local notation "actors₀" => v.reference.actors
local notation "donors₀" => v.reference.donors
local notation "Old" => Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous)
local notation "Parts" => Fin H₀→Fin G₀→DepotRAM.Parts A.clip.venue.socket
local notation "Roles" => Fin A.previous.blocks→Fin A.previous.hosts→Fin G₀→Cell ((L₀).roleBits*(L₀).nodes)
local notation "HostRoutes" => Fin H₀→Fin (L₀).walks→Option (Fin H₀)
local notation "HostFields" => Fin H₀→Fin G₀→Cell (names₀*actors₀)

def groupValues {D k K cap H g₁ g₂ a nb mb : ℕ} (groups : g₁=g₂)
    (V : Values D k K cap H g₁ a nb mb) : Values D k K cap H g₂ a nb mb :=
  groups ▸ V

theorem group_measured {D k K cap H g₁ g₂ a nb mb n M base w : ℕ} (groups : g₁=g₂)
    {C : Refs D k K cap} {V : Values D k K cap H g₁ a nb mb} {m : Memory w}
    (read : Measured C V n M base m) : Measured C (groupValues groups V) n M base m :=by
  cases groups
  exact read

def registeredValues (old : Old) (parts : Parts) (roles : Roles) (order : HostRoutes) (field : HostFields)
    (names : (L₀).nameBits=names₀) (ranks : (L₀).donors=donors₀)
    (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity H₀ G₀ v.reference.bits names₀ count₀ where
  walks h j:=order h (Fin.cast «matching».paths.symm j)
  old:=A.oldInput v S floor «matching» old p
  born:=A.bornInput v S floor «matching» parts p
  wanted:=rowsAt rfl rfl names (fun (_ : Fin H₀) (_ : Fin G₀)=>Packed.token (some q))
  venues h g:=(encode names₀ actors₀).symm (field h g)
  counts h g:=(encode count₀ donors₀).symm ((rowsAt rfl rfl (congrArg (count₀*·) ranks)
    ((L₀).dataCount order (A.roleValues v roles))) h g)

private theorem same_walk_family {H D n H' D' : ℕ}
    (hosts : H=H') (degree : D=D') (paths : breadth D=n)
    (prev : Fin H→Fin D→Option (Fin H)) (current : Fin H'→Fin D'→Option (Fin H'))
    (once : HEq prev current) :
    HEq (fun h (p : Fin n)=>Gather.reaching prev h (p.cast paths.symm)) (Gather.reaching current) :=by
  subst H';subst D';subst n
  cases eq_of_heq once
  rfl

theorem registered_walks {H D nextG : ℕ} (old : Old) (parts : Parts) (roles : Roles)
    (peer : Fin H₀→Fin A.clip.venue.socket.degree→Option (Fin H₀))
    (R : Fin H→Fin D→Option (Fin H))
    (hostSize : H₀=H) (degree : A.clip.venue.socket.degree=D) (same : HEq peer R)
    (field : HostFields) (names : (L₀).nameBits=names₀) (ranks : (L₀).donors=donors₀)
    (groups : G₀=nextG) (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    HEq (groupValues groups (A.registeredValues v S floor «matching» old parts roles
      (Gather.reaching peer) field names ranks p q)).walks (Gather.reaching R):=by
  subst nextG
  exact same_walk_family hostSize degree «matching».paths peer R same

/-- A shared charged adjacency word identifies the old per-host neighbor even at the absent sentinel. -/
theorem roster_from_reads {H D H' D' w : ℕ} (hosts : H'=H) (degree : D'=D)
    (adj : Bank) (m : Memory w) (limit : H<2^w)
    (p : Fin H'→Fin D'→Option (Fin H')) (r : Fin H→Fin D→Option (Fin H))
    (old : ∀h j,m (adj.base+h.val*D'+j.val)=(number (p h j):Word w))
    (now : ∀h j,m (adj.base+h.val*D+j.val)=(number (r h j):Word w)) : HEq p r:=by
  subst H';subst D'
  apply heq_of_eq
  funext h j
  have eqn:=(old h j).symm.trans (now h j)
  have small (u : Option (Fin H)) : number u<2^w:=by
    cases u with
    | none=>exact limit
    | some t=>exact t.isLt.trans limit
  have eqval:=congrArg Fin.val eqn
  rw [Fin.val_cast_of_lt (small _),Fin.val_cast_of_lt (small _)] at eqval
  generalize p h j=a at eqval ⊢
  generalize r h j=b at eqval ⊢
  cases a with
  | none =>
    cases b with
    | none=>rfl
    | some t=>exact False.elim (t.isLt.ne eqval.symm)
  | some t =>
    cases b with
    | none=>exact False.elim (t.isLt.ne eqval)
    | some u=>exact congrArg some (Fin.ext eqval)

/-- Every registered W reference page uses the original adjacency that the
earlier signed directory read. Numeric word equality also covers absent hosts. -/
theorem registered_walks_from_reads {H D nextG w : ℕ} (old : Old) (parts : Parts) (roles : Roles)
    (peer : Fin H₀→Fin A.clip.venue.socket.degree→Option (Fin H₀)) (R : Fin H→Fin D→Option (Fin H))
    (size : H₀=H) (degree : A.clip.venue.socket.degree=D) (adj : Bank) (input : Memory w) (room : H<2^w)
    (seen : ∀h j,input (adj.base+h.val*A.clip.venue.socket.degree+j.val)=(number (peer h j):Word w))
    (prior : ∀h j,input (adj.base+h.val*D+j.val)=(number (R h j):Word w))
    (field : HostFields) (names : (L₀).nameBits=names₀) (ranks : (L₀).donors=donors₀)
    (groups : G₀=nextG) (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    HEq (groupValues groups (A.registeredValues v S floor «matching» old parts roles
      (Gather.reaching peer) field names ranks p q)).walks (Gather.reaching R):=
  A.registered_walks v S floor «matching» old parts roles peer R size degree
    (roster_from_reads size degree adj input room peer R seen prior) field names ranks groups p q

theorem all_registered_rows {w} (m : Memory w) (safe : A.Room v floor w) (space : v.vectorStart floor<2^w)
    (old : Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts A.clip.venue.socket)
    (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin G₀→Cell ((L₀).roleBits*(L₀).nodes))
    (oldPitch : 0<A.previous.lanes) (panelPitch : 0<A.clip.panelPitch) (rolePitch : 0<A.rolePitch)
    (lower : ∀x p,(previousBank A.previous A.previousBase x p).Fits w (v.signedEnd floor))
    (oldRows : ∀x p,Reads (previousBank A.previous A.previousBase x p) (old p x) A.previous.lanes m)
    (panel : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g)) A.clip.panelPitch m)
    (roleLo : ∀x,(A.role x).base+(A.role x).size≤v.signedEnd floor) (roleRoom : ∀x,A.previous.hosts*chunks G₀ A.rolePitch≤(A.role x).size)
    (roleRows : ∀x,Reads (A.role x) (roles x) A.rolePitch m)
    (order : HostRoutes) (field : HostFields) (names : (L₀).nameBits=names₀) (ranks : (L₀).donors=donors₀)
    (venue : Reads (A.clip.fieldBank (v.signedEnd floor)) field M₀ (A.clippedTape v floor m))
    (wired : Mounted P₀ (DescentSortedRoster.indexed order) (A.clippedTape v floor m) G₀ M₀)
    (ports : ∀bank : Bank,bank.Fits w (A.priorStart v floor)→H₀*chunks G₀ M₀≤bank.size→
      Accessible P₀ bank H₀ G₀ M₀ w (A.priorStart v floor)) (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    Measured ((R₀).refs p q) (A.registeredValues v S floor «matching» old parts roles order field names ranks p q)
      Nv v.reference.lanes (v.vectorStart floor) (A.mountedTape v floor m) :=by
  let V:=A.registeredValues v S floor «matching» old parts roles order field names ranks p q
  apply A.registered_row v S floor «matching» m safe space old parts roles oldPitch panelPitch rolePitch lower oldRows
    panel roleLo roleRoom roleRows p q V names ranks rfl rfl rfl
  · funext h g
    exact (encode count₀ donors₀).apply_symm_apply _
  · have obs : (fun h g=>encode names₀ actors₀ (V.venues h g))=field:=by
      funext h g
      exact (encode names₀ actors₀).apply_symm_apply _
    rw [obs];exact venue
  · exact wired
  · exact ports

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
