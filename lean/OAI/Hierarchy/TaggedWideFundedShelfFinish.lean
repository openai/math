import OAI.Hierarchy.TaggedWideCalendarFinish
import OAI.Hierarchy.TaggedWireShelfContents

namespace OAI
/-! # Evaluating the paid fixed-calendar shelf with the five words returned by its native run -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe ReportSockets HistoryRoles RoleProgram Tagged WideStack ProtocolStackContraction
open WireTelescope CalendarTape ProtocolRAM.Calendar ProtocolRAM.Calendar.CatalogueRows
open TaggedShorterBudget ProtocolRAMReportedPorts WideCalendarSites WideControlJoin
open Tagged.WideStack.Leaf ProtocolRAM.Calendar.CatalogueRows.Alignment
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
set_option quotPrecheck false
variable {F : Type*} [Field F] {stageHeight : ℕ} {X : Type}
    {h W k w R attempts M den H lanes m view p e : ℕ}
    (π : Equiv.Perm (Tagged.Row h)) (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
local notation "N" => siteLast h (2^W) k+1
variable (slot : Event→Slot X) (wire : X→Widths (siteLast h (2^W) k+1)) (es : List Event) (x : X) (path : Path slot es x)
    (Z : Report π (2^W) k w R M den (wire (terminal slot es x path)))
local notation "S" => Z.sampler
local notation "pad" => publicChord h (2^W) k
local notation "L" => Z.mount.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "counts" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
variable (ident : {i // 0<Z.fixed i} ↪ Catalogue Z.sampler π.symm depth marked)
local notation "role" => Terminal.ports S π.symm depth marked unique Z.fixed Z.stock Z.reserved Z.used ident
variable (histCap : Public Z.sampler h W k attempts→ℕ)
    (room : ∀q : NamedAperture.LiveEnd (SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used),
      SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used q.val.1 ≤
        histCap (Terminal.ports Z.sampler π.symm depth marked unique Z.fixed Z.stock Z.reserved Z.used ident q))
    (cells : ∀y,(Σs,SiteBit (wire y) s) ↪ (Σu,Fin (histCap u)))
    (packing : cells (terminal slot es x path)=(NamedAperture.transport Z.ledger.symm).toEmbedding.trans
      (Terminal.place Z.sampler π.symm depth marked unique Z.mount (publicChord h (2^W) k)
        Z.fixed Z.stock Z.reserved Z.used ident Z.receipt histCap room))
    (z : SiteChoices slot wire es x path)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
    (b : Board) (order : Fin b.coreRows≃Edges Z.sampler h (2^W) k)
    (raw : Fin b.rows→ProtocolRAMEmit.Row) (capacity : b.Private order→ℕ)
local notation "pos" => b.transport order
local notation "stage" => fun _ : Fin b.rows=>stageHeight
local notation "key" => stageKey stageHeight m
local notation "width" => fun t : Fin (m+1)=>⌈dyadic t.val*w⌉₊
variable (ins : ∀t : Fin (m+1),Installed F dir.groups H lanes w m t.val
      (atScale (b.transport order) (fun _ : Fin b.rows => stageHeight) stageHeight raw))
    (a : ∀i,Fin (2^(raw i).width))
local notation "history" => placedBits slot wire es x path (timelineFin slot wire cells es x path) z
local notation "input" => nativePins (view:=view) key raw pos stage ins capacity a history
variable (s : Site h (2^W) k)
local notation "num" => siteNumber h (2^W) k s
variable (fits : ∀r : Fiber (attempts:=attempts) Z.sampler s,
      ∀t, RoleProgram.labelled Z.sampler t r.val < 2^p)
local notation "ap" => Terminal.outputAperture (lanes:=lanes) (view:=view) (e:=e)
  S dir es b order capacity histCap width s fits
variable (acquired : Bought Z.sampler π.symm depth marked→Fin b.boughtRows)
variable (A : Alignment b Z.sampler π.symm depth marked M raw (fun i=>(raw i).width)
      (b.original Z.sampler π.symm depth marked order acquired))
    (orig : Fin Z.edges≃Fin b.rows) (sameWidth : ∀u,Z.widthAt u=(raw (orig u)).width)
local notation "pub" => originalPort S π.symm depth marked unique b order acquired raw A
variable (hw : 0<w)
variable (inject : Function.Injective fun i =>
      (atScale (b.transport order) (fun _ : Fin b.rows => stageHeight) stageHeight raw i).link)
    (port : Bool→Fin b.rows→Fin H) (same : ∀t,(ins t).port=port)
    (owners :
      let scaled := atScale (b.transport order) (fun _ : Fin b.rows => stageHeight) stageHeight raw
      let whereAt := location Z.sampler π.symm depth marked unique b order acquired raw A
        (fun _ : Fin b.rows => stageHeight) stageHeight w hw
      ∀(i : {r : Fin b.rows // 0 < pieces scaled w r}) side,
        (whereAt.trans (ReportSockets.packed dir) (i,side)).1.val = (scaled i.val).group)
    (pins :
      let scaled := atScale (b.transport order) (fun _ : Fin b.rows => stageHeight) stageHeight raw
      let whereAt := location Z.sampler π.symm depth marked unique b order acquired raw A
        (fun _ : Fin b.rows => stageHeight) stageHeight w hw
      ∀(i : {r : Fin b.rows // 0 < pieces scaled w r}) side,
        (whereAt.trans (ReportSockets.packed dir) (i,side)).2 = port side i.val)
    (lanesRoom : ∀i,
      pieces (atScale (b.transport order) (fun _ : Fin b.rows => stageHeight) stageHeight raw) w i ≤ lanes)
    (maxPrivate : ∀i : b.Private order,(raw i.val).width≤capacity i)
local notation "code₀" => fun i side=>if on:0<counts i then RoleProgram.labelled S false (role ⟨(i,side),on⟩) else 0
local notation "code₁" => fun u side=>if on:0<Z.widthAt u then RoleProgram.labelled S true (pub (⟨orig u,(sameWidth u) ▸ on⟩ : Active b raw) side) else 0
local notation "data" => fun i=>Fin.cast (congrArg (fun n : ℕ=>2^n) (sameWidth i).symm) (a (orig i))
variable {E Q : Type} [Fintype E] [Fintype Q] (G : Gate) {slots n : ℕ}
    (base : ℕ) (out : Memory G.W) (ext : E→Bool) (sel : Q→Bool)

include packing hw inject same owners pins lanesRoom maxPrivate in
/-- The frozen terminal gate reads the actual five-word shelf at its allocated address.
All positions and role codes come from the native receipt. -/
theorem funded_shelf_finish
    (contents : Z.ShelfContents slots n base out code₀ code₁)
    (observed : ∀i : {e // 0<Z.fixed e},let ends:=actualEnds S π.symm depth marked (ident i)
      ((Z.rows i.val).endpoint=(name ends.1).val ∧ (Z.rows i.val).opposite=(name ends.2).val) ∨
      ((Z.rows i.val).endpoint=(name ends.2).val ∧ (Z.rows i.val).opposite=(name ends.1).val))
    (paidSite : ∀u (on : 0<Z.widthAt u) side,name (HistoryRoles.site S (pub (⟨orig u,(sameWidth u) ▸ on⟩ : Active b raw) side))=
      (rowGraph (L).edge).vertex u side)
    (allRoles : ∀r : Public S h W k attempts,∀side,RoleProgram.labelled S side r<2^p)
    (oldRoom : ∀i,counts i≤2^e) (newRoom : ∀u,Z.widthAt u≤2^e)
    (outputRoom : ∀u,Z.widthAt u≤view) (pFits : p≤G.W) (capFits : 2^e<2^G.W)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val) (shelfRoom : base+5*(N*slots)≤G.u) :
    TypedWiring.value (G.shelfNet (F:=F) (slots:=slots) base num ap)
      (Sum.elim ext (Sum.elim sel (Sum.elim input (G.terminal out))))=
      Z.finish num (last slot wire num es x path (z num).1 (z num).2) (Z.ports data num) := by
  obtain ⟨sp,posn,col,put,written,widths,site,fields⟩:=contents
  apply Z.shelf_finish π depth marked unique slot wire es x path ident histCap room cells packing z
    dir b order raw capacity ins a s fits acquired A orig sameWidth hw inject port same owners pins
    lanesRoom maxPrivate G base out ext sel sp posn col put observed paidSite allRoles oldRoom newRoom
    outputRoom pFits capFits dense shelfRoom written widths site
  · exact fun u side=>(fields u side).1
  · exact fun u side=>(fields u side).2

end Hierarchy.ProbeStage.CoreBoard.Report
end

end OAI
