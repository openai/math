import OAI.Hierarchy.DescentContactOutputShape
import OAI.Hierarchy.DescentContactMaskPeriod
import OAI.Hierarchy.DescentResetDonorBook
import OAI.Hierarchy.DescentContactWidthPage
import OAI.Hierarchy.DescentContactMarkerShape

namespace OAI
/-! # Shared source, target, count and selector tables for the positive contact fields -/
namespace Hierarchy.DescentContactOutputShape.Shape
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (first : ℕ) {w : ℕ}
local notation "M" => A.donor.batch
local notation "f" => A.donor.fieldBits
local notation "t" => A.metaBits
local notation "v" => A.donor.cargoBits
local notation "P" => A.marker first
local notation "B" => A.flagPage first
local notation "J" => A.countPage first
local notation "K" => A.haloPage first
local notation "U" => A.choicePage first
local notation "E" => A.projected first

def request (q : Fin A.sockets) := (DescentContactSenderMass.query (r:=A.donor.residual) (n:=A.donor.n) (Ht:=A.donor.height) q).2
def labels:=DescentResetDonorBook.page A.request f t M
def choices (m : Memory w):=ROM.after A.labels A.choiceBits U m

def marked (m : Memory w):=DescentContactMarkerShape.memory A.shapes A.markerBits t M P m
def flagPages:=ROM.binary (DescentContactMarkerShape.flag A.markerBits f) M
def flagged (m : Memory w):=ROM.after A.flagPages (A.markerBits*M) B (A.marked first m)
def counts (m : Memory w):=DescentContactWidthPage.image J f t M (A.flagged first m)
def halos (m : Memory w):=DescentContactWidthPage.image K v t M (A.counts first m)
def catalogImage (m : Memory w):=A.choices first (A.halos first m)
def catalog (w : ℕ):=((((DescentContactMarkerShape.program A.shapes A.markerBits t M P w).seq
    (ROM.mount A.flagPages (A.markerBits*M) w B)).seq (DescentContactWidthPage.program J f t M w)).seq (DescentContactWidthPage.program K v t M w)).seq
      (ROM.mount A.labels A.choiceBits w U)
def catalogClock:=
  (DescentContactMarkerShape.ticks A.markerBits M+DescentContactMarkerShape.ticks A.markerBits M+DescentContactWidthPage.clock f M+DescentContactWidthPage.clock v M)+
    (4+10*DescentResetDonorBook.words A.sockets f t M)
def catalogNames :=
  15*(2*2^(A.markerBits*M)+1)+15*(2*2^(A.markerBits*M)+1)+DescentContactWidthPage.size f M+DescentContactWidthPage.size v M+
    15*(DescentResetDonorBook.words A.sockets f t M+1)

theorem catalog_any (m : Memory w) (room : E<2^w) :
    (A.catalog first w).Exec m (A.catalogImage first m) A.catalogClock ∧ CheapCode (A.catalog first w) ∧
    ∀addr,addr<P ∨ E≤addr→A.catalogImage first m addr=m addr:=by
  obtain ⟨_,a,b,c,d,_⟩:=A.cuts first
  have markLow:P≤B:=Nat.le_add_right ..
  have flagLow:B≤J:=Nat.le_add_right ..
  have one:=DescentContactMarkerShape.any A.shapes A.markerBits t M P m ((flagLow.trans (b.trans (c.trans d))).trans_lt room)
  have flags:=ROM.run A.flagPages (A.markerBits*M) B (A.marked first m) ((b.trans (c.trans d)).trans_lt room)
  have saved:=ROM.frame A.flagPages (A.markerBits*M) B (A.marked first m)
  have two:=DescentContactWidthPage.any J f t M (A.flagged first m) ((c.trans d).trans_lt room)
  have three:=DescentContactWidthPage.any K v t M (A.counts first m) (d.trans_lt room)
  have four:=DescentResetDonorBook.installed A.request f t M U (A.halos first m) room
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then one.1 flags.1) two.1) three.1) four.1,cheap_seq (cheap_seq (cheap_seq (cheap_seq one.2.1 (ROM.cheap _ _ _ _)) two.2.1) three.2.1) (ROM.cheap _ _ _ _),?_⟩
  intro addr away
  exact (four.2.2.2.1 addr (away.imp (fun h=>h.trans_le (a.trans (b.trans c))) id)).trans
    ((three.2.2 addr (away.imp (fun h=>h.trans_le (a.trans b)) (fun h=>d.trans h))).trans
      ((two.2.2 addr (away.imp (fun h=>h.trans_le a) (fun h=>(c.trans d).trans h))).trans
        ((saved addr (away.imp (fun h=>h.trans_le markLow) (fun h=>(b.trans (c.trans d)).trans h))).trans
        (one.2.2 addr (away.imp id (fun h=>(flagLow.trans (b.trans (c.trans d))).trans h))))))

theorem catalog_names (w : ℕ) : DescentStaticWordColumn.names (A.catalog first w)=A.catalogNames:=by
  unfold catalog catalogNames DescentContactMarkerShape.program DescentContactWidthPage.program DescentContactWidthPage.size
  simp only [DescentStaticWordColumn.names_seq,ROM.mount,DescentStaticWordColumn.names_mount]
  rfl

end
end Hierarchy.DescentContactOutputShape.Shape

end OAI
