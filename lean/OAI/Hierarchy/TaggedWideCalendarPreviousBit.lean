import OAI.Hierarchy.TaggedWideCalendarExit
import OAI.Hierarchy.TaggedWireTerminalReportBit
import OAI.Hierarchy.TaggedWideCalendarLeaf
import OAI.Hierarchy.TaggedWideLeafBits
import OAI.Hierarchy.TaggedWireTerminalAlignment

namespace OAI
/-! # The final physical barrel reads the last state of its chronological path -/

noncomputable section
namespace Hierarchy.Tagged.WideCalendarSites
open LinearAlgebra.SpectralBooks ChordGraph
open WireTelescope WireTelescope.CalendarTape ProtocolRAM.Calendar
variable {X : Type} {N : ℕ} (slot : Event→Slot X) (wire : X→Widths N)

theorem last_eq_lastState (s : Fin N) : ∀ es x (j : Path slot es x)
    (v : State (wire x) s × PartyStates slot wire s es x j),
    last slot wire s es x j v.1 v.2=lastState slot wire s es x j v
  | [],_,_,_=>rfl
  | e::es,x,j,v=>last_eq_lastState s es ((slot e).next x j.1) j.2 v.2

end Hierarchy.Tagged.WideCalendarSites

namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe ReportSockets HistoryRoles RoleProgram Tagged WideStack ProtocolStackContraction
open WireTelescope CalendarTape ProtocolRAM.Calendar ProtocolRAM.Calendar.CatalogueRows
open Tagged.WideStack.Leaf TaggedShorterBudget ProtocolRAMReportedPorts WideCalendarSites
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
variable (ident : {i // 0<Z.fixed i} ↪ Catalogue (Z.sampler) π.symm depth marked)
local notation "role" => Terminal.ports S π.symm depth marked unique Z.fixed Z.stock Z.reserved Z.used ident
variable (histCap : Public (Z.sampler) h W k attempts→ℕ) (room : ∀q,(SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used) q.val.1≤histCap ((Terminal.ports (Z.sampler) π.symm depth marked unique Z.fixed Z.stock Z.reserved Z.used ident) q))
    (cells : ∀y,(Σs,SiteBit (wire y) s) ↪ (Σu,Fin (histCap u)))
    (packing : cells (terminal slot es x path)=(NamedAperture.transport Z.ledger.symm).toEmbedding.trans
      (Terminal.place (Z.sampler) π.symm depth marked unique Z.mount (publicChord h (2^W) k) Z.fixed Z.stock Z.reserved Z.used ident Z.receipt histCap room))
    (z : SiteChoices slot wire es x path)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
    (b : Board) (order : Fin b.coreRows≃Edges (Z.sampler) h (2^W) k)
    (raw : Fin b.rows→ProtocolRAMEmit.Row) (capacity : b.Private order→ℕ)
local notation "pos" => b.transport order
local notation "stage" => fun _ : Fin b.rows=>stageHeight
local notation "rows" => atScale pos stage stageHeight raw
local notation "key" => stageKey stageHeight m
local notation "width" => fun t : Fin (m+1)=>⌈dyadic t.val*w⌉₊
variable (ins : ∀t : Fin (m+1),Installed F dir.groups H lanes w m t.val (atScale (b.transport order) (fun _ : Fin b.rows=>stageHeight) stageHeight raw))
    (a : ∀i,Fin (2^(raw i).width))
local notation "history" => placedBits slot wire es x path (timelineFin slot wire cells es x path) z
local notation "input" => nativePins (view:=view) key raw pos stage ins capacity a history
variable (s : Site h (2^W) k)
local notation "num" => siteNumber h (2^W) k s
local notation "Fib" => Fiber (attempts:=attempts) S s
variable (fits : ∀r:(Fiber (attempts:=attempts) (Z.sampler) s),∀t,RoleProgram.labelled (Z.sampler) t r.val<2^p)
local notation "ap" => Terminal.outputAperture (lanes:=lanes) (view:=view) S dir es b order capacity histCap width s fits
variable (q : (bitGraph (rowGraph ((Z.mount.matrixLayout (siteNumber h (2^W) k).injective (publicChord h (2^W) k))).family) (SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used)).Port (siteNumber h (2^W) k s))
local notation "old" => (⟨(q.1.1.1,q.1.2),Nat.zero_lt_of_lt q.1.1.2.isLt⟩ : NamedAperture.LiveEnd counts)

include packing in
/-- The physical source is a time word at the original reported endpoint.
The two admissible endpoint orders are the original catalogue row receipt. -/
theorem previousAperture_digit
    (observed : ∀i : {e // 0<Z.fixed e},let ends:=actualEnds S π.symm depth marked (ident i)
      ((Z.rows i.val).endpoint=(name ends.1).val ∧ (Z.rows i.val).opposite=(name ends.2).val) ∨
      ((Z.rows i.val).endpoint=(name ends.2).val ∧ (Z.rows i.val).opposite=(name ends.1).val))
    (d : TurnShelf.Aperture p e) (code : d.1.val=RoleProgram.labelled S false (role old)) (digit : d.2.val=q.1.1.2.val) :
    Sum.elim input id (ap d)=rowBits (L).family counts
      (Z.initialState (last slot wire num es x path (z num).1 (z num).2)) q := by
  have chart:=Terminal.positions_of_reported S π.symm depth marked Z.mount pad Z.fixed Z.stock Z.reserved
    Z.used ident Z.receipt observed
  have atSite : HistoryRoles.site S (role old)=s := by
    apply (siteNumber h (2^W) k).injective
    refine (Terminal.native_site S π.symm depth marked unique Z.mount pad Z.fixed Z.stock Z.reserved Z.used ident old chart).trans ?_
    rcases q with ⟨⟨⟨i,j⟩,side⟩,loc⟩
    cases side <;> exact loc
  let live : Fib := ⟨role old,atSite⟩
  have bound : d.2.val<histCap live.val := by
    rw [digit]
    exact q.1.1.2.isLt.trans_le (room old)
  refine (Terminal.lastHistoryPin_value (lanes:=lanes) (view:=view) S dir es b order capacity histCap width s fits input d live code bound).trans ?_
  have read:=Z.previousBit π depth marked unique slot wire es x path ident histCap room cells packing z q
  change history (bodyIndex es (Fin.last es.length) ⟨role old,⟨d.2.val,bound⟩⟩)=_
  refine Eq.trans ?_ (read.trans ?_)
  · apply congrArg history
    apply congrArg (bodyIndex es (Fin.last es.length))
    exact congrArg (fun n : Fin (histCap (role old)) => (⟨role old,n⟩ : Σu,Fin (histCap u))) (Fin.ext digit)
  · exact congrArg (fun state => rowBits (L).family counts (Z.initialState state) q)
      (last_eq_lastState slot wire num es x path (z num)).symm

end Hierarchy.ProbeStage.CoreBoard.Report
end

end OAI
