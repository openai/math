import OAI.Hierarchy.DescentStageVenueSources
import OAI.Hierarchy.DescentStageVenueBookLayout
import OAI.Hierarchy.DescentDatedStageVenue
import OAI.Hierarchy.DescentVenueActorMask
import OAI.Hierarchy.DescentScalarHaloPortROM

namespace OAI
/-! # Compiling the successor stage input on the same memory as its measured banks -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentCompiler DescentPackedColony DescentSIMDLookup DescentPackedZip
open DescentPacking.PackedMatch.Local.Stage DescentActorRaster DescentColonies
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def args (B:Sources) (base k H G M D:ℕ) : Dated.Operands :=
  let ports:=DescentScalarHaloPortROM.chart H G M D (area base k H G M) B.roster
  {roster:=B.roster,ids:=fun j=>⟨area base k H G M+j*(H*chunks G M),Nat.clog 2 (H*chunks G M)⟩,
   offsets:=ports.offsets,chunks:=ports.chunks,actors:=Venue.output base k H G M,
   wire:=B.signed,hubs:=B.hub,atoms:=fun x=>.lookup (B.paid x) .row}

def input (B:Sources) (k:ℕ) (x:Fin (2^k)):Expr:=.lookup (B.alive x.val) .row
def program (B:Sources) (base k H G M D w:ℕ) :=
  (Venue.program w base k H G M (input B k)).seq
    (DescentScalarHaloPortROM.program H G M D w (area base k H G M))
def ticks (B:Sources) (base k H G M D:ℕ) :=
  Venue.ticks base k H G M (input B k)+(4+10*DescentScalarHaloPortROM.length H G M D)
def image {w : ℕ} (B:Sources) (base k H G M D:ℕ) (m:Memory w) :=
  DescentScalarHaloPortROM.image H G M D (area base k H G M)
    (Venue.after base k H G M (input B k) m)

theorem translates (base k H G M D:ℕ) :
    endAddress base k H G M D=base+endAddress 0 k H G M D:=by
  simp only [endAddress,area,Venue.outBase,DescentPackedColumnSum.finish,
    DescentScalarHaloPortROM.stop,Nat.zero_add,Nat.add_assoc]

structure Room (B:Sources) (base k H G M D cap w:ℕ) : Prop where
  rank : B.roster.Fits w base
  rankSize : H*D≤B.roster.size
  hub : B.hub.Fits w base
  hubSize : H≤B.hub.size
  alive : ∀x:DescentColonies.Block k,(B.alive x.val).Fits w base
  aliveSize : ∀x:DescentColonies.Block k,H*chunks G M≤(B.alive x.val).size
  paid : ∀x:ℕ,(B.paid x).Fits w base
  paidSize : ∀x:DescentColonies.Block k,H*chunks G M≤(B.paid x.val).size
  signed : ∀(x:DescentColonies.Block k) (j:Fin (2*cap)),(B.signed x.val j.val).Fits w base
  signedSize : ∀(x:DescentColonies.Block k) (j:Fin (2*cap)),H*chunks G M≤(B.signed x.val j.val).size
  room : endAddress base k H G M D<2^w

variable {F P : Type} [Field F] {u : ℕ} {bits : P→ℕ} {W : MarkedWorld F u P bits}
    {gadget : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z D wire s H M w b : ℕ}
    (r : Reached W gadget q ε S k age z D wire s) (wide : Fintype.card r.V≤H)
    (B:Sources) (base:ℕ)
local notation "G" => S.groupCount age
local notation "host" => r.vertex.trans (Fin.castLEEmb wide)
local notation "gid" => Function.Embedding.refl (Fin G)
local notation "A" => r.placement
local notation "n" => H*chunks G M
local notation "high" => area base k H G M
local notation "roof" => endAddress base k H G M D
local notation "actualWire" => Prepare.signed (A) (r.order.trans Fin.valEmbedding) S r.valid gid host

theorem issued (previous:Memory w) (rs:Fin H→Fin D→Option (Fin H))
    (bounds:Room B base k H G M D (A).cap w)
    (roster:∀(h:Fin H) (j:Fin D), previous (B.roster.base+(h.val*D+j.val))=(DescentPackedColony.target (rs h j):Word w))
    (hub:∀h:Fin H,previous (B.hub.base+h.val)=((Census.hub (A) host h).val:Word w))
    (actors:∀x:DescentColonies.Block k,Reads (B.alive x.val) (Venue.actual (A) gid host x) M previous)
    (funded:∀x:DescentColonies.Block k,Reads (B.paid x.val) (fun h g=>Census.count (A) (Equiv.refl _) host b h g x) M previous)
    (cables:∀(x:DescentColonies.Block k) (j:Fin (2*(A).cap)),Reads (B.signed x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (actualWire x j h g)) M previous) :
    let next:=image B base k H G M D previous
    (program B base k H G M D w).Exec previous next (ticks B base k H G M D) ∧
    stageVenue r wide (args B base k H G M D) M b roof rs next ∧
    (∀a,a<base ∨ roof≤a→next a=previous a) ∧ CheapCode (program B base k H G M D w) := by
  let mid:=Venue.after base k H G M (input B k) previous
  let done:=image B base k H G M D previous
  have base0 : base≤Venue.outBase base k M:=by unfold Venue.outBase DescentPackedColumnSum.finish;omega
  have nspan : n ≤ span n:=Nat.le_pow_clog (by decide) _
  have upto : Venue.outBase base k M+n≤high:=Nat.add_le_add_left nspan _
  have areaEnd : high+DescentScalarHaloPortROM.length H G M D≤roof:=Nat.le_add_right ..
  have hiRoom : high<2^w:=(Nat.le_add_right ..).trans_lt (areaEnd.trans_lt bounds.room)
  have ah:=Venue.run (A) gid host base (input B k) previous
    (fun x=>show (B.alive x.val).Fits w base ∧ True from ⟨bounds.alive x,True.intro⟩)
    (fun x=>source_column _ base (bounds.alive x) _ _ (bounds.aliveSize x) (actors x)) (upto.trans_lt hiRoom)
  obtain ⟨run₀,mask,keep₀,cheap₀⟩:=ah
  obtain ⟨run₁,statics,keep₁,cheap₁⟩:=DescentScalarHaloPortROM.mount H G M D high B.roster mid
    (areaEnd.trans_lt bounds.room)
  have low : base≤high:=base0.trans ((Nat.le_add_right ..).trans upto)
  have old (a:ℕ) (lt:a<base) : done a=previous a:=
    (keep₁ a (.inl (lt.trans_le low))).trans (keep₀ a (.inl lt))
  have up (T:Bank) (fits:T.Fits w base) : T.Fits w roof:=
    ⟨fits.1,fits.2.1,fits.2.2.trans (low.trans ((Nat.le_add_right ..).trans areaEnd))⟩
  have saved {T:Bank} {a:ℕ} {f:Fin H→Fin G→Cell a} (fits:T.Fits w base) (size:n≤T.size)
      (read:Reads T f M previous): Reads T f M done :=by
    intro p
    exact (old _ ((Nat.add_lt_add_left ((row H G M p).isLt.trans_le size) _).trans_le fits.2.2)).trans (read p)
  have fitActor:(Venue.output base k H G M).Fits w roof :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt hiRoom,(Nat.le_add_right ..).trans areaEnd⟩
  have geometry:=DescentScalarHaloPortROM.geometry H G M D high roof B.roster (Venue.output base k H G M)
     le_rfl bounds.room (up _ bounds.rank) bounds.rankSize fitActor nspan
  refine ⟨by
    intro P R K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then run₀ run₁ machine pc regs pubs exit rom advice cfg memory enter same,⟨geometry.1,⟨fun p j=>statics.ids j p,?_,statics.offsets,statics.chunks⟩,?_,?_,
        up _ bounds.hub,bounds.hubSize,?_,?_,?_⟩,?_,cheap_seq cheap₀ cheap₁⟩
  · intro h j
    have small : h.val*D+j.val<H*D :=by simpa [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm] using (finProdFinEquiv (h,j)).isLt
    exact (old _ ((Nat.add_lt_add_left (small.trans_le bounds.rankSize) _).trans_le bounds.rank.2.2)).trans (roster h j)
  · intro p
    exact (keep₁ _ (.inl ((Nat.add_lt_add_left (row H G M p).isLt _).trans_le upto))).trans (mask p)
  · intro x j
    exact saved (bounds.signed x j) (bounds.signedSize x j) (cables x j)
  · intro h
    exact (old _ ((Nat.add_lt_add_left (h.isLt.trans_le bounds.hubSize) _).trans_le bounds.hub.2.2)).trans (hub h)
  · intro x;exact ⟨up _ (bounds.paid x),True.intro⟩
  · intro x
    exact source_column _ roof (up _ (bounds.paid x.val)) done _ (bounds.paidSize x)
      (saved (bounds.paid x.val) (bounds.paidSize x) (funded x))
  · rintro a (lt|late)
    · exact old a lt
    · have end₀:=upto.trans ((Nat.le_add_right ..).trans areaEnd)
      exact (keep₁ a (.inr (areaEnd.trans late))).trans (keep₀ a (.inr (end₀.trans late)))

end
end Hierarchy.DescentSixParty.StageVenueTail

end OAI
