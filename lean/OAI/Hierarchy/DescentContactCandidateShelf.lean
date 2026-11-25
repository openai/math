import OAI.Hierarchy.DescentPrivateCandidateShelf
import OAI.Hierarchy.DescentContactReceiver

namespace OAI
/-! # Compact fields of the public contact at its true receiving socket -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


local notation "old" => W.granular B.count (z*G.b) B.fit

local notation "pool" => DescentDenseHostOrder.roster (Z).graph ((Z).k-(T).commonDepth) height

/-- This is a structural read for every real public socket, including a
socket of width zero. Both relative codes are bounded by the public palette. -/
theorem contact_header_shape (c : (placement).Contact) (side : Bool) :
    let e:=contactParent B c
    let v:=if side then (blocks B).dst e else (blocks B).src e
    ((Z).actualRecord T vertexCode e (if side then 2 else 1))%(pool).card=relativeShape B v := by
  intro e v
  obtain ⟨_,shapeWord,_⟩:=signed_header B e side
  rw [←shapeWord,(Z).rawHostRank_read T vertexCode v.1.2,Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (((Z).hostFields T vertexCode v.1.2).2.isLt)

theorem contact_header_before_width (c : (placement).Contact) :
    let e:=contactParent B c
    let row:=(Z).actualRecord T vertexCode e
    row 0=1 ∧ row 1%(pool).card=relativeShape B ((blocks B).src e) ∧
      row 2%(pool).card=relativeShape B ((blocks B).dst e) := by
  exact ⟨rfl,contact_header_shape B c false,contact_header_shape B c true⟩

/-- Counting the physical contact fiber gives the exact unit count even
when a paid rotor socket has no incoming edges. -/
theorem contact_units (c : (placement).Contact) (positive : 0<(Z).unit) :
    (blocks B).count (contactParent B c)=Fintype.card {i : (old).graph.Edge // (placement).contact i=c} ∧
    contactParent B c∈(coarse).core := by
  let e:=contactParent B c
  have row:=((Z).contact_row T vertexCode birth c).2
  have amt:=congrFun row (5 : Fin 7)
  have core:=congrFun row (6 : Fin 7)
  change (coarse).graph.width e=Fintype.card {i : (old).graph.Edge // (placement).contact i=c}*(Z).unit at amt
  change (if e∈(coarse).core then 1 else 0)=1 at core
  refine ⟨Nat.eq_of_mul_eq_mul_right positive ((weight_width B e).trans amt),?_⟩
  by_contra no
  simp [e,no] at core

/-- Receiver-local shape comparison is sufficient once the numerical issuing
bank has selected its actual old host and common block. -/
theorem contact_short_hit (u : Host) (c : (placement).Contact) (s : Bool)
    (selected : receiverRoot B u=((Z).rootVertex T ((placement).owner s c),
      (Z).rootBlock T ((placement).owner s c))) :
    let e:=contactParent B c
    let endpoint:=if s then (blocks B).dst e else (blocks B).src e
    relativeShape B endpoint=relativeShape B u ↔ endpoint=u := by
  intro e endpoint
  have reach : receiverRoot B endpoint=receiverRoot B u :=
    (contact_endpoint_root B c s).trans selected.symm
  exact ⟨root_shape_injective B reach,congrArg (relativeShape B)⟩

local notation "contactId" => DescentContactReceiver.localContactId ((Z).k-(T).commonDepth) (2^(Z).n) height

/-- Either half can encounter the public socket. A loop is owned by its
source ticket, and a zero-width or remote socket contributes no local parent. -/
theorem contact_selected_origin (u : Host) (c : (placement).Contact) (side : Bool)
    (selected : receiverRoot B u=((Z).rootVertex T ((placement).owner side c),
      (Z).rootBlock T ((placement).owner side c))) :
    let slot:=contactId (side,(Z).rootTicket T ((placement).owner side c),contactSocket B side c)
    localOrigin B u (contactShelfIndex B slot)=
      if owns : DescentResetLocalRoster.active (blocks B) u (contactParent B c) ∧
        decide ((blocks B).src (contactParent B c)≠u)=side then some ⟨contactParent B c,owns.1⟩ else none := by
  intro slot
  split
  next yes=>
    apply (contact_shelf_iff B u slot _).2
    refine ⟨c,yes.1,rfl,?_⟩
    let t:=decide ((blocks B).src (contactParent B c)≠u)
    change contactId (t,(Z).rootTicket T ((placement).owner t c),contactSocket B t c)=_
    exact congrArg (fun t=>contactId (t,(Z).rootTicket T ((placement).owner t c),contactSocket B t c)) yes.2
  next no=>
    cases found : localOrigin B u (contactShelfIndex B slot) with
    | none=>rfl
    | some x=>
      obtain ⟨q,live,_,key⟩:=(contact_shelf_iff B u slot x).1 found
      let t:=decide ((blocks B).src (contactParent B q)≠u)
      change contactId (t,(Z).rootTicket T ((placement).owner t q),contactSocket B t q)=
        contactId (side,(Z).rootTicket T ((placement).owner side c),contactSocket B side c) at key
      have coords:=(contactId).injective key
      have sides : t=side:=congrArg Prod.fst coords
      subst side
      have oldRoot : receiverRoot B u=((Z).rootVertex T ((placement).owner t q),(Z).rootBlock T ((placement).owner t q)):=
        contact_at_root B ⟨q,live.2⟩
      have roots:=oldRoot.symm.trans selected
      have owners : (placement).owner t q=(placement).owner t c:=((Z).rootLocation T vertexCode).injective
        (Prod.ext (congrArg vertexCode (congrArg Prod.fst roots))
          (Prod.ext (congrArg Prod.snd roots) (congrArg (fun k=>k.2.1) coords)))
      have same : q=c:=contact_unique B t owners (congrArg (fun k=>k.2.2) coords)
      subst c
      exact (no ⟨live,rfl⟩).elim

theorem contact_at_slot {b : ℕ} (u : Host) (c : (placement).Contact)
    (live : DescentResetLocalRoster.active (blocks B) u (contactParent B c))
    (x : Fin 9→DescentSIMDLookup.Cell b) (positive : 0<(Z).unit)
    (issued : (x 0).val≠0)
    (sourceHit : (x 1).val=(x 3).val ↔ (blocks B).src (contactParent B c)=u)
    (targetHit : (x 2).val=(x 3).val ↔ (blocks B).dst (contactParent B c)=u)
    (src : (x 4).val=localClass B u ((blocks B).src (contactParent B c)))
    (dst : (x 5).val=localClass B u ((blocks B).dst (contactParent B c)))
    (self : (x 6).val=localClass B u u)
    (missing : ((x 7).val≠0) ↔ u∉Stage.near B.next.placement u)
    (mass : (x 8).val=Fintype.card {i : (old).graph.Edge // (placement).contact i=c}) :
    let j:=localRoster B u ⟨contactParent B c,live⟩
    DescentCandidateMaskRAM.render x=DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u j)) := by
  intro j
  have picked:=((local_read B u j ⟨contactParent B c,live⟩).2 rfl)
  obtain ⟨count,marked⟩:=contact_units B c positive
  have total:=mass.trans count.symm
  have showIt : DescentCandidateMaskRAM.visible x :=
    ⟨issued,total.symm ▸ live.1,live.2.imp sourceHit.mpr targetHit.mpr⟩
  simp only [DescentCandidateMaskRAM.render,ite_eq_left showIt,picked,«meta»,src,dst,self,total,
    propext missing,decide_eq_true marked]

/-- Blank reservations, exhausted empty donor sockets, and cables with
neither endpoint here all return the same all-zero metadata word. -/
theorem contact_masked {b : ℕ} (x : Fin 9→DescentSIMDLookup.Cell b)
    (absent : (x 0).val=0 ∨ (x 8).val=0 ∨ ((x 1).val≠(x 3).val ∧ (x 2).val≠(x 3).val)) :
    DescentCandidateMaskRAM.render x=DescentResetFieldAssembler.raw b DescentResetFieldAssembler.Meta.blank := by
  apply DescentCandidateMaskRAM.masked
  rintro ⟨flag,pos,loc⟩
  rcases absent with missing|zero|reject
  · exact flag missing
  · omega
  · exact loc.elim reject.1 reject.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
