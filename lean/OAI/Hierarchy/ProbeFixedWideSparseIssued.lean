import OAI.Hierarchy.ProbeFixedWideSparseReady
import OAI.Hierarchy.ProbeFixedWideSparseBallot
import OAI.Hierarchy.ProbeFixedWideForestAperture
import OAI.Hierarchy.TaggedWidePageSweep

namespace OAI
/-! # Issuing the first physical ballot on every genuine attempted calendar date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage Native CoreBoard CoreRoute StripChart
open CatalystArchive PurchaseStage StockBound ReportSockets Tagged WideCPU
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_dated_ballot_issued :
    ∀ᶠ h : ℕ in Filter.atTop, ∀width, width≤2^h→v.keepLimit*width+1≤2^h→
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let top:=A.endAddress v.mesh
      let W:=wordBits h (2^v.W) copies
      let stock:=v.fixedTerminalStock P h width
      ∀size,top≤ size→∀M (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)), M=v.radius→
      let m:=v.wideSignedMidAt h width size stock M π (wideRouteOrder h (2^v.W) k) raw
      let co:=checkedOut (v.wideSignedChart h width stock) top m
      ∀ell fee rom work,
      let g:=v.wideDated h width ell fee
      ∀(transport : Fin g.rawEdges→Bool) (original : Memory W),
        (∀a,a<top→ original a=co a)→top≤rom→3*g.romEnd rom+2≤work → g.workEnd work<2^W→
        ∀(j : Fin (events v.mesh).length) (a : Attempt), (events v.mesh).get j=.attempt a→
        (PageResult.skip (g.ballotPage rom work j)).Issued work
          (g.words rom (SiteDirectory.table h (2^v.W) k) transport original) := by
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  filter_upwards [v.wide_row_room,v.wide_face_room,Filter.eventually_ge_atTop v.wideStockHeight,
    Filter.eventually_ge_atTop ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊] with h rowRoom face tall cut
  intro width small budget P A top W stock size extent M π raw nativeRadius m co ell fee rom work g transport original base late gap
    span j a atDate processing low
  subst M
  let dates:=events v.mesh
  let C:=v.wideSignedChart h width stock
  let r:=Fintype.card (Slots h (2^v.W) k)
  let page:=v.wideSignedPage h width stock
  let cnt:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A))
  let owners:=sinkBank (v.catalystStaticStart P h width) cnt r P.catalogue.rows
  let banks:=TerminalLayout.settlement page stock
  let src:=TerminalLayout.source page
  let tab:=TerminalLayout.table page
  let dst:=TerminalLayout.destination page
  let table:=SiteDirectory.table h (2^v.W) k
  let image:=g.words rom table transport original
  have scheduled : Event.attempt a∈dates:=atDate ▸ dates.get_mem j
  have zz:=v.wide_stock_sizes h width tall budget small
  have single:=v.wide_stock_at h width size extent v.radius π raw tall budget small
  have whole:=single.mounted_all
  obtain ⟨_,_,boot,pub,_,_,_,_,_⟩:=v.wide_signed_boot_at h width size extent stock v.radius π
    (wideRouteOrder h (2^v.W) k) raw zz.words.addresses
  have all (ev) (hit : Event.attempt ev∈dates):=(v.wide_stock_layout h width size extent v.radius π raw zz.words budget
    zz.width zz.alphabet zz.rowsMass zz.roles ev hit).1
  have arch:=v.mode_archive P h width r banks src tab dst owners m single all
  have layout:=all a scheduled
  obtain ⟨past,tail,split⟩:=List.append_of_mem scheduled
  let entry:=run C past m
  have slot:=slot_of_split C m _ past tail entry split rfl whole
  have room:=zz.words.addresses
  have endROM : g.siteROM rom+g.siteDirectorySize≤g.romEnd rom:=by
    simp only [Dated.romEnd,Dated.maskROM,Dated.controlROMStart,Dated.firstROM,endOf];omega
  have prior : top≤work:=by dsimp only [Dated.siteROM] at endROM;omega
  have fix (i) (_ : g.ballotROM rom j≤ i) (inside : i<g.ballotROM rom j+(g.ballot j).advice g.sites) :
      processing i=image i := by
    have a₁ : g.ballotROM rom j+(g.ballot j).advice g.sites≤g.controlROMStart rom:=WideCPU.extent _ _ j
    have a₂ : g.controlROMStart rom≤g.romEnd rom:=by simp only [Dated.romEnd,Dated.maskROM,endOf];omega
    exact low _ (by omega)
  let siteROM:=g.siteROM rom
  let ballotROM:=g.ballotROM rom j
  let begin:=g.ballotStart work j
  let pre:=g.roleStart work j.castSucc
  let post:=g.roleStart work j.succ
  let strides:=g.siteStride rom
  let bits:=ProtocolRAMPurchaseSampler.bits (v.widePacketShelf h)
  have sheet:=v.wide_dated_ballot_ready h width ell fee rom work banks src tab dst owners table transport original processing
    j a atDate fix room ((show v.menu.copiesAt v.copyScale width≤width from Nat.div_le_self ..).trans_lt zz.width)
    prior gap span
  change PublicSheet (v.widePacketShape h width (dates.get j)) g.sites ballotROM begin W
    (v.widePacketFields h width bits (dates.get j) siteROM strides pre post) processing at sheet
  rw [atDate] at sheet
  have keep (i) (inside : i<top) : processing i=co i:=(low _ (inside.trans_le prior)).trans
    ((g.words_before rom table transport original i (inside.trans_le late)).trans (base i inside))
  have siteMounted : HistoryRoles.RoleROM.Mounted siteROM table processing:=by
    intro i
    have inside : i.val<g.siteDirectorySize:=i.isLt
    exact (low _ (by dsimp only [siteROM];omega)).trans (g.site_mounted rom table transport original i)
  have sizeFit : SiteDirectory.size h (2^v.W) k≤2^W:=by
    change g.siteDirectorySize≤2^W
    have topWork : work≤g.workEnd work:=by
      simp only [Dated.workEnd,Dated.slotStart,Dated.maskStart,Dated.controlStart,Dated.rolesEnd,endOf];omega
    omega
  obtain ⟨_,_,out,runBallot,_,frame⟩:=v.wide_ballot_scattered h width r banks src tab dst owners π m a past tail entry
    processing bits siteROM ballotROM begin pre post strides slot boot pub whole room arch zz.strip small cut
    (rowRoom width).1 face.1 face.2.1 face.2.2 layout layout.board keep siteMounted sizeFit sheet
  let assembled:=fun ev=>(v.widePacketShape h width ev).sheet g.sites ballotROM begin
    (v.widePacketFields h width bits ev siteROM strides pre post)
  have pageEq : g.ballotPage rom work j=assembled (.attempt a):=congrArg assembled atDate
  rw [pageEq]
  exact ⟨out,runBallot,trivial,fun addr below=>frame addr (Or.inl (by
    change addr<begin+1-1 at below;omega)) (Or.inl (by
    change addr<begin+1-1 at below;omega)) (by change addr<begin+1-1 at below;omega)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
