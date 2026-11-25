import OAI.Hierarchy.DescentResetOriginalNumberRoom
import OAI.Hierarchy.DescentResetOriginalDonorTariff
import OAI.Hierarchy.DescentResetOriginalPageTariff
import OAI.Hierarchy.DescentResetNumberStemTariff

namespace OAI
/-! Exact composition of the native source, public, stem and private original-number bills. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs
open DescentSIMDLookup DescentPackedZip DescentStaticWordColumn ProtocolRAM
noncomputable section
set_option quotPrecheck false

variable {s : CandidateSheets} (u : s.OriginalInputs) (base : ℕ)
local notation "P" => u.publicSide base
local notation "T" => u.stemSide base
local notation "A" => u.privateSide base
local notation "J" => s.privates
local notation "X" => s.blocks
local notation "D" => s.originalDonors
local notation "raw" => s.inputDonorsBase base
local notation "z" => DescentResetOriginalZeroHalo.count s.hosts s.groups s.lanes s.metaBits
local notation "q" => DescentResetHaloBroadcast.count s.hosts s.groups s.lanes s.argBits
local notation "coord" => s.stemSources.coord.layout.size

def staticCost (count : ℕ) := 4+10*count+7*(15*(count+1))

def publicCost (U : ℕ) :=
  let c:=2*U+2*max U (1+u.signedSlots*(2*U+22))+33
  let page:=12*2^((P).date.width)
  let jobs:=X*(s.contacts+1)
  staticCost (P).count+staticCost page+(4+jobs*(4+s.rows*(2*c+4)))+7*(15+jobs*(11+4*c))

def invoice (U V W : ℕ) :=
  staticCost coord + staticCost s.stemSources.pages + staticCost z + (D).price V +
  u.publicCost base U + 266240*(X*u.stems+1)*(1+s.rows+2^(7*s.stemBits*s.lanes)) +
  staticCost J + staticCost q + (A).pagePrice W

structure Inputs (U V W : ℕ) : Prop where
  «meta» : ∀x j,(u.sources.meta x j).work≤U
  zero : ∀x,(u.sources.zero x).work≤U
  own : ∀x,(u.sources.self x).work≤U
  shape : ∀x,(u.sources.shape x).work≤U
  labels : ∀x f j,(u.sources.label x f j).work≤U
  payload : ∀x f t j,(u.sources.cargo x f t j).work≤U
  selected : ∀f j,(u.sensor.label f j).work≤V
  returned : ∀f j,(u.sensor.ticket f j).work≤V
  old : ∀j,(u.sensor.halo j).work≤V
  signed : ∀x j t,(u.stem x j t).work≤64
  privateMeta : ∀i,((A).fields.meta i).work≤W
  privateZero : ∀i,((A).fields.zero i).work≤W
  halo : ∀i,((A).fields.halo i).work≤W
  argument : ∀i,((A).fields.arg i).work≤W

private theorem coordinate_bill (base w : ℕ) (L : DescentStemNumberOperands.Plan) :
    L.ticks+7*names (L.program base w)=staticCost L.coord.layout.size+staticCost L.pages :=by
  unfold DescentStemNumberOperands.Plan.program
  rw [names_seq,Book.names]
  change (4+10*L.coord.layout.size+(4+10*L.pages))+
    7*(names (DescentStaticWordColumn.program w base _ L.coord.layout.size)+15*(L.pages+1))=_
  rw [names_mount]
  unfold staticCost;omega

theorem literal_invoice (w U V W : ℕ) (room : u.Room base w) (reads : u.Inputs base U V W) :
    u.time base+7*names (u.code base w)≤u.invoice base U V W :=by
  have first:=coordinate_bill (s.metaEnd base) w s.stemSources
  have scalar : (4+10*z)+7*names (u.scalarPhase base w).program=staticCost z :=by
    change _+7*names (DescentStaticWordColumn.program w _ _ z)=_
    simp only [names_mount,staticCost]
  have donors := (D).priced raw w V u.sensor room.donor reads.selected reads.returned reads.old
  have pub:=(P).price room.public_ U reads.meta reads.zero reads.own reads.shape reads.labels reads.payload
  have public_: (P).clock+7*names ((P).cpu w)≤u.publicCost base U :=by
    obtain ⟨a,b⟩:=pub
    dsimp only [publicCost, staticCost]
    change (P).clock ≤ 4+10*(P).count+(4+10*(12*2^(P).date.width)+
      (4+X*(s.contacts+1)*(4+s.rows*(2*_+4)))) at a
    omega
  have stem:=(T).tariff64 w reads.signed
  have private_:=(A).priced W room.private_ reads.privateMeta reads.privateZero reads.halo reads.argument
  have words :
      (4+10*J+(4+10*q))+7*names (DescentUniformSlotOperands.program (s.stemFormatEnd base) J
        s.hosts s.groups s.lanes s.argBits w)=staticCost J+staticCost q :=by
    unfold DescentUniformSlotOperands.program
    rw [names_seq,names_mount,names_mount];unfold staticCost;omega
  unfold time code prefixTime «prefix» invoice
  simp only [names_seq] at *
  change (T).ticks+7*names ((T).code w) ≤
    266240*(X*u.stems+1)*(1+s.rows+2^(7*s.stemBits*s.lanes)) at stem
  omega

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs

end OAI
