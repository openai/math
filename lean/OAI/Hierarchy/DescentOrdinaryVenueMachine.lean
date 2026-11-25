import OAI.Hierarchy.DescentOrdinaryShapeSlots
import OAI.Hierarchy.DescentOrdinaryVenueExtent
import OAI.Hierarchy.DescentOrdinaryHubColumn
import OAI.Hierarchy.DescentOrdinaryPeerCoordinates
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # The new geometric header used by the ordinary date's signed cable writer -/
open ThreeFlat.RAM.PhysicalProcedure
namespace Hierarchy.DescentOrdinaryVenueReturn
open DescentSixParty DescentSixParty.Chronology DescentSixParty.Chronology.OrdinaryLink DescentHostDegree DescentHostDirectory DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section

def gain (D:ℕ):=gainExponent 20 D
def «public» (k D:ℕ):=shapeSet (gap D+gain D) k (shapeSlots D)
def word (k D R i:ℕ):=if i<span R then (ordinaryHubRow k (shapeSlots D) (gain D) i).1
  else (ordinaryHubRow k (shapeSlots D) (gain D) (i-span R)).2.toNat

structure Sources where
  count : Bank
  roster : Bank
  hub : Bank

def phase (B:Sources)(base k H D R E w:ℕ):NativePhase w:=
  let peers:=DescentOrdinaryPeerCount.program w base H D R E B.count B.roster («public» k D)
  let tags:NativePhase w:=⟨DescentStaticWordColumn.program w (bookStart base H D R E) (word k D R) (2*span R),
    4+10*(2*span R),fun m=>DescentStaticWordColumn.image (bookStart base H D R E) (word k D R) m (2*span R),
    @DescentStaticWordColumn.cheap _ _ _ _⟩
  let e:=paddedHubExpr H (owners base H D R E) B.hub (masks base H D R E)
  let o:=(hubs base H D R E).base
  (peers.seq tags).seq ⟨scan w o R e,4+R*(2*e.work+4),ProtocolRAM.image o R e,@scan_cheap _ _ _ _⟩

structure Room (B:Sources)(base H D R E w:ℕ):Prop where
  count : B.count.Fits w base
  roster : B.roster.Fits w base
  hub : B.hub.Fits w base
  safe : roof base H D R E<2^w

variable (B:Sources)(base k H D R E w:ℕ)
local notation "p" => bookStart base H D R E
local notation "src" => owners base H D R E
local notation "mask" => masks base H D R E
local notation "out" => Bank.base (hubs base H D R E)

theorem parts (room:Room B base H D R E w):
    H<2^w ∧ base≤p ∧ p<2^w ∧ p+2*span R=out ∧
    (src).Fits w out ∧ (mask).Fits w out ∧ B.hub.Fits w out ∧ out+R<2^w:=by
  have begin_:base≤p:=by
    simp only [bookStart,DescentOrdinaryPeerCount.roof,DescentOrdinaryPeerRows.endAddress,
      DescentOrdinaryPeerChart.top,DescentOrdinaryPeerChart.out,DescentOrdinaryPeerChart.length,
      DescentOrdinaryPeerRows.fixed];omega
  have hh:H<2^w:=by
    have full:=room.safe
    rw [expanded] at full
    have has:=span_ge H;omega
  have tail_:out+R<2^w:=(Nat.add_le_add_left (span_ge R) _).trans_lt room.safe
  have so:p+2*span R=out:=rfl
  have older:p≤out:=(Nat.le_add_right ..).trans_eq so
  have pad:span R<2^w:=by omega
  refine ⟨hh,begin_,older.trans_lt ((Nat.le_add_right ..).trans_lt tail_),rfl,
    ⟨span_pos _,pad,?_⟩,⟨span_pos _,pad,?_⟩,⟨room.hub.1,room.hub.2.1,room.hub.2.2.trans (begin_.trans older)⟩,tail_⟩
  · change p+span R≤p+2*span R;omega
  · change p+span R+span R≤p+2*span R;omega

theorem any (m:Memory w)(room:Room B base H D R E w):
    (phase B base k H D R E w).Runs m ∧ ∀a,a<base ∨ roof base H D R E≤a→(phase B base k H D R E w).image m a=m a:=by
  obtain ⟨hh,offset,peersRoom,defs,ofit,mfit,hfit,rawRoom⟩:=parts B base H D R E w room
  let orig:=DescentOrdinaryPeerCount.program w base H D R E B.count B.roster («public» k D)
  let mid:=DescentStaticWordColumn.image p (word k D R) (orig.image m) (2*span R)
  obtain ⟨one,earlier⟩:=DescentOrdinaryPeerCount.any base H D R E B.count B.roster («public» k D) m room.count room.roster hh peersRoom
  have printer:(DescentStaticWordColumn.program w p (word k D R) (2*span R)).Exec (orig.image m) mid (4+10*(2*span R)):=DescentStaticWordColumn.mount p (2*span R) (word k D R) (orig.image m) (defs.le.trans_lt ((Nat.le_add_right ..).trans_lt rawRoom))
  let query:=paddedHubExpr H src B.hub mask
  have go:(scan w out R query).Exec mid (ProtocolRAM.image out R query mid) (4+R*(2*query.work+4)):=scan_exec out R (paddedHubExpr H src B.hub mask) mid
    ⟨⟨ofit,trivial⟩,trivial,⟨⟨mfit,trivial⟩,trivial,trivial,hfit,ofit,trivial⟩,trivial⟩ rawRoom
  refine ⟨by
    intro P Rw K machine pc regs pubs exit rom advice cfg memory enter same
    exact Procedure.Exec.then (Procedure.Exec.then one printer) go machine pc regs pubs exit rom advice cfg memory enter same,?_⟩
  intro a side
  have top:out+R≤roof base H D R E:=Nat.add_le_add_left (span_ge _) _
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a (side.imp (by omega) (by omega))).trans
    ((DescentStaticWordColumn.frame _ _ _ _ a (side.imp (by omega) (by omega))).trans (earlier a (side.imp_right (by change roof base H D R E ≤ a → p ≤ a; omega))))

end
end Hierarchy.DescentOrdinaryVenueReturn

end OAI
