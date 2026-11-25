import OAI.Hierarchy.DescentResetOriginalDonors
import OAI.Hierarchy.DescentResetStemProjectExprTariff

namespace OAI
/-! # Literal ticks and controller text of the three original donor columns -/
namespace Hierarchy.DescentResetOriginalDonors
open DescentSIMDLookup DescentPackedZip DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
namespace Panel
variable (P : Panel)
def price (T : ℕ) :=
  (DescentContactWidthPage.clock P.oldBits P.lanes+7*DescentContactWidthPage.size P.oldBits P.lanes)+
  4096*DescentResetStemProject.volume P.fields P.sparseHosts P.groups P.blocks P.bits P.lanes P.lanes+
  (4+P.fields*(4+P.sparseHosts*chunks (P.groups*P.blocks) P.lanes*(2*(T+12)+4)))+
  7*(15+P.fields*(11+4*(T+12)))

theorem priced (base w T : ℕ) (f : Fin P.fields→Expr) (prior : ∀j,(f j).work≤T)
    (lanes : 0<P.lanes) (blocks : 0<P.blocks) (roof : P.endAddress base<2^w) :
    P.ticks base f+7*names (P.program base f w)≤P.price T :=by
  have low:=(P.bounds base).2.trans_lt roof
  have text:=DescentContactWidthPage.tariff base P.oldBits P.bits P.lanes (fun _=>0 : Memory w) low
  have inner (j : Fin P.fields) : (P.expanded base f j).work≤T+12:=by
    unfold expanded DescentContactWidthPage.expr DescentStaticUnary.query
    rw [DescentPackedZip.work]
    change (f j).work+1+11≤T+12
    have h:=prior j
    omega
  have finish:=DescentResetStemProjectExpr.tariff (P.cut base) P.sparseHosts P.groups P.blocks P.bits
    P.lanes P.lanes w (P.expanded base f) (T+12) inner lanes blocks lanes
  rw [program,names_seq,text,ticks,price]
  omega
end Panel
namespace Layout
variable (L : Layout)
def price (T : ℕ) := L.labels.price T+L.tickets.price T+L.halos.price T
theorem priced (base w T : ℕ) (f : Sensors L.slots) (ready : L.Ready base f w)
    (labels : ∀s j,(f.label s j).work≤T) (tickets : ∀s j,(f.ticket s j).work≤T)
    (halos : ∀j,(f.halo j).work≤T) :
    L.ticks base f+7*names (L.program base f w)≤L.price T :=by
  obtain ⟨_,t,h⟩:=L.cuts base
  have a:=L.labels.priced base w T (L.lift f.label) (fun _=>labels _ _) ready.lanes ready.blocks ((t.trans h).trans_lt ready.room)
  have b:=L.tickets.priced (L.ticketBase base) w T (L.lift f.ticket) (fun _=>tickets _ _) ready.lanes ready.blocks (h.trans_lt ready.room)
  have c:=L.halos.priced (L.haloBase base) w T f.halo halos ready.lanes ready.blocks ready.room
  rw [ticks,program,names_seq,names_seq,price]
  omega
end Layout
end
end Hierarchy.DescentResetOriginalDonors

end OAI
