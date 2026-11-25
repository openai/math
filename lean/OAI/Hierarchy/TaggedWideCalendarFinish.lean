import OAI.Hierarchy.TaggedWideCalendarShelf
import OAI.Hierarchy.TaggedWideCalendarPreviousBit
import OAI.Hierarchy.TaggedWideCalendarOutputBit
import OAI.Hierarchy.TaggedWideCalendarTurnBounds

namespace OAI
/-! # The complete terminal site factor at the original native route and both shared output planes -/

noncomputable section
namespace Hierarchy.WireTelescope.TurnShelf
open scoped Classical

/-- Extend the finite physical barrel plane by zero to a natural digit address. -/
def readPlane {p e : ℕ} (operand : Aperture p e→Bool) (c j : ℕ) : Bool :=
  if role:c<2^p then if bit:j<2^e then operand (⟨c,role⟩,⟨j,bit⟩) else false else false

theorem readPlane_at {p e : ℕ} (operand : Aperture p e→Bool) (d : Aperture p e) :
    readPlane operand d.1.val d.2.val=operand d := by simp [readPlane,d.1.isLt,d.2.isLt]

end Hierarchy.WireTelescope.TurnShelf

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
local notation "outBits" => Sum.elim input id ∘ ap
variable {E Q : Type} [Fintype E] [Fintype Q] (G : Gate) {slots n : ℕ}
    (base : ℕ) (out : Memory G.W) (ext : E→Bool) (sel : Q→Bool)
    (sp :
      let layout := Z.mount.matrixLayout (siteNumber h (2^W) k).injective (publicChord h (2^W) k)
      ∀i, Spine (rowGraph layout.edge) (layout.family i).1.1 (layout.routes i) (layout.family i).1.2)
    (posn : Fin n ≃ TurnShelf.Positions
      (Z.mount.matrixLayout (siteNumber h (2^W) k).injective (publicChord h (2^W) k)).routes)
    (col : Fin n→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live col ↪ Fin (siteLast h (2^W) k+1) × Fin slots)

include packing hw inject same owners pins lanesRoom maxPrivate in
/-- All five native words are shared among the candidate selectors. The only
endpoint reads are the last dated state, the original private bank or the
physically decoded positive output slot of that same input assignment. -/
theorem shelf_finish
    (observed : ∀i : {e // 0<Z.fixed e},let ends:=actualEnds S π.symm depth marked (ident i)
      ((Z.rows i.val).endpoint=(name ends.1).val ∧ (Z.rows i.val).opposite=(name ends.2).val) ∨
      ((Z.rows i.val).endpoint=(name ends.2).val ∧ (Z.rows i.val).opposite=(name ends.1).val))
    (paidSite : ∀u (on : 0<Z.widthAt u) side,name (HistoryRoles.site S (pub (⟨orig u,(sameWidth u) ▸ on⟩ : Active b raw) side))=
      (rowGraph (L).edge).vertex u side)
    (allRoles : ∀r : Public S h W k attempts,∀side,RoleProgram.labelled S side r<2^p)
    (oldRoom : ∀i,counts i≤2^e) (newRoom : ∀u,Z.widthAt u≤2^e)
    (outputRoom : ∀u,Z.widthAt u≤view) (pFits : p≤G.W) (capFits : 2^e<2^G.W)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val) (shelfRoom : base+5*(N*slots)≤G.u)
    (written : ∀ (f : Fin 5) (z : Fin N×Fin slots),out (TurnShelf.addr base z.1 z.2 f)=ProtocolRAMTurnShelf.entry col put f z)
    (widths : ∀i,col i 4=counts (posn i).1)
    (site : ∀u : ProtocolRAMTurnShelf.Live col,(put u).1=(sp (posn u.val).1).visit (posn u.val).2)
    (roles : ∀u : ProtocolRAMTurnShelf.Live col,∀side : Bool,col u.val (if side then 1 else 0)=
      refRole (L).routes code₀ code₁ (posn u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (posn u.val) side))
    (starts : ∀u : ProtocolRAMTurnShelf.Live col,∀side : Bool,col u.val (if side then 3 else 2)=
      refStart (L).routes counts ((L).nativeOrder Z.enum) (posn u.val).1 (TurnShelf.refAt (L).family (L).edge (L).routes sp (posn u.val) side)) :
    TypedWiring.value (G.shelfNet (F:=F) (slots:=slots) base num ap)
      (Sum.elim ext (Sum.elim sel (Sum.elim input (G.terminal out))))=
      Z.finish num (last slot wire num es x path (z num).1 (z num).2) (Z.ports data num) := by
  let plane:=TurnShelf.readPlane outBits
  have outputs : ∀u side,code₁ u side<2^p := by
    intro u side
    dsimp only
    split
    · exact allRoles _ _
    · exact Nat.two_pow_pos _
  have inputs : ∀i side,code₀ i side<2^p := by
    intro i side
    dsimp only
    split
    · exact allRoles _ _
    · exact Nat.two_pow_pos _
  have endsFit:=Z.turn_extent sp posn col (2^e) oldRoom newRoom widths starts
  have rolesFit:=Z.turn_role_fits sp posn col p code₀ code₁ inputs outputs roles
  refine (G.shelfNet_value (F:=F) base num ap dense shelfRoom out ext sel input).trans ?_
  have finPlane : outBits=fun d=>plane d.1.val d.2.val :=
    funext fun d=>(TurnShelf.readPlane_at outBits d).symm
  let evaluate := fun bits : TurnShelf.Aperture p e → Bool =>
    TypedWiring.value (TurnShelf.network F slots p e) (TurnShelf.nativeView base num out bits)
  refine (congrArg evaluate finPlane).trans ?_
  apply Z.installed_finish base out sp posn col put written widths site
    (turn_words col pFits capFits rolesFit endsFit) rolesFit endsFit code₀ code₁ roles starts
    num (last slot wire num es x path (z num).1 (z num).2) data plane
  · intro i j side here
    have on : 0<counts i:=Nat.zero_lt_of_lt j.isLt
    let q : (bitGraph (rowGraph (L).family) counts).Port num:=⟨(⟨i,j⟩,side),by cases side <;>exact here⟩
    let d : TurnShelf.Aperture p e:=⟨⟨code₀ i side,inputs _ _⟩,⟨j.val,j.isLt.trans_le (oldRoom i)⟩⟩
    refine (TurnShelf.readPlane_at outBits d).trans ?_
    exact Z.previousAperture_digit π depth marked unique slot wire es x path ident histCap room cells packing z
      dir b order raw capacity ins a s fits q observed d (by simp [d,q,on]) rfl
  · intro i hop j side here
    let u:=((L).routes i).get hop
    let off:=NativeSlot.start (L).routes counts ((L).nativeOrder Z.enum) i hop
    have on : 0<counts i:=Nat.zero_lt_of_lt j.isLt
    have full : off+counts i≤Z.widthAt u :=
      (NativeSlot.start_room (L).routes counts ((L).nativeOrder Z.enum) i hop on).trans_eq
        (congrFun (Z.receipt.native_width (siteNumber h (2^W) k).injective pad) u)
    have low : off+j.val<Z.widthAt u := (Nat.add_lt_add_left j.isLt off).trans_le full
    have active : 0<Z.widthAt u :=Nat.zero_lt_of_lt low
    let j' : Fin (raw (orig u)).width:=⟨off+j.val,low.trans_eq (sameWidth u)⟩
    let d : TurnShelf.Aperture p e:=⟨⟨code₁ u side,outputs _ _⟩,⟨off+j.val,low.trans_le (newRoom u)⟩⟩
    have home : HistoryRoles.site S (pub (⟨orig u,(sameWidth u) ▸ active⟩ : Active b raw) side)=s :=
      (siteNumber h (2^W) k).injective ((paidSite u active side).trans here)
    refine (TurnShelf.readPlane_at outBits d).trans ?_
    exact A.originalAperture_digit S π.symm depth marked unique b order acquired raw dir hw ins inject port same
      owners pins lanesRoom capacity maxPrivate es histCap a history s fits (⟨orig u,(sameWidth u) ▸ active⟩ : Active b raw) side j' home
      ((sameWidth u).symm.le.trans (outputRoom u)) d (by simp [d,active]) rfl

end Hierarchy.ProbeStage.CoreBoard.Report
end

end OAI
