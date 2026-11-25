import OAI.Hierarchy.TaggedWideSparseTerminal
import OAI.Hierarchy.TaggedWideBranchEndpointPlacement

namespace OAI
/-! # The literal terminal aperture at the last chronological cursor -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM.Calendar
variable {X:Type} (slot:Event→Slot X)

theorem boundary_last : ∀ es x (p : Path slot es x),
    boundaryState slot es x p (Fin.last es.length)=terminal slot es x p
  | [],_,_=>rfl
  | _::es,_,p=>by
      change boundaryState slot es _ p.2 (Fin.last es.length)=_
      exact boundary_last es _ p.2

namespace Prefix
theorem index_terminal {es : List Event} {x : X} (j : Path slot es x) :
    boundaryIndex j (Fin.last es.length)=terminal cursorSlot es (atCursor Prefix.start)
      (histories Prefix.start j) :=
  boundary_last _ _ _ _
end Prefix
end Hierarchy.WireTelescope.CalendarTape

namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph CalendarTape
theorem transport_back {K : ℕ} {A B C : Widths K} {T : Type}
    (ab:A=B) (bc:B=C) (ac:A=C) (f : (Σs,SiteBit B s)↪T) :
    (transport ac.symm).toEmbedding.trans ((transport ab).toEmbedding.trans f)=
    (transport bc).symm.toEmbedding.trans f := by
  subst B
  subst C
  rfl
end Hierarchy.WireTelescope.NamedAperture

namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.BranchRoles
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe ReportSockets WireTelescope CalendarTape
open ProtocolRAM.Calendar ProtocolRAM.Calendar.CatalogueRows ProtocolRAMEmit
open scoped Classical
set_option quotPrecheck false
variable {X:Type} {sl : Event→Slot X} {es:List Event} {t₀:X}
variable {h W k jobs depth : ℕ} {S:PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
variable {cap : Public S h W k jobs → ℕ}
    {wire : Prefix.Cursor sl es t₀ → Widths (siteLast h (2^W) k + 1)}
    (possible : ∀ c : Prefix.Cursor sl es t₀, Nonempty (Path sl c.todo c.mem))
    (R : ∀ j : Path sl es t₀, BranchRoles S π depth cap wire j) (j : Path sl es t₀)
local notation "q" => R j
local notation "stop" => terminal Prefix.cursorSlot es (Prefix.atCursor Prefix.start) (Prefix.histories Prefix.start j)
variable {M den w supply : ℕ} {board : Board} (B : Mount (S:=S) π (name (W:=W) (k:=k)) board.rows)
    (pad : Chord (siteLast h (2^W) k + 1)) {fixed : Fin board.rows→ℕ} {stock : Goods h W k→ℕ}
    {reserved used : Catalysts h W k→ℕ} {actual : Fin board.rows→Row}
    {G : Geometry (boardLayout h (2^W) k w supply) M den actual}
    (receipt : MatrixReceipt B fixed stock reserved used G)
    (order : Fin board.coreRows ≃ Edges S h (2^W) k)
    (sz : jobs*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=board.boughtRows)
local notation "ordinal" => board.ordinal S π depth (q).mark order sz
local notation "origRow" => DatedRows.embed S π depth (q).mark board order sz
local notation "ordRow" => DatedRows.raw S π depth (q).mark board order sz (q).order
local notation "qty" => SettledMatrix.Layout.available fixed stock reserved used ∘ origRow ∘ (q).order
local notation "mass" => SettledMatrix.Layout.bits fixed stock reserved used
local notation "ch" => sorted S π depth (q).mark ∘ (q).order
local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "avail" => B.actual.chordWidths fixed+(commodityGraph π name).chordWidths stock+
  (catalystGraph name).chordWidths (fun i=>reserved i-used i)
variable (ident : {i:Fin board.rows // 0<fixed i} ↪ Catalogue S π depth (R j).mark)
local notation "ports" => Terminal.ports S π depth (q).mark (q).exclusive fixed stock reserved used ident

/-- Equality of the actual final named state and the matrix comparator's dense input aperture. -/
theorem terminal_mapping
    (index : ∀i,ordinal (ident i)=i.val)
    (position : ∀i,filledChord B.actual pad i.val=sorted S π depth (q).mark (.inl (ident i)))
    (data : (q).bits (Fin.last es.length)=qty)
    (prior : ∀i j,ch i=ch j→(i<j ↔ ordRow i<ordRow j)) :
    ∃ (head:avail=wire stop) (room:∀p:NamedAperture.LiveEnd mass,mass p.val.1≤cap (ports p)),
      cells possible R j stop=(NamedAperture.transport head.symm).toEmbedding.trans
        (Terminal.place S π depth (q).mark (q).exclusive B pad fixed stock reserved used ident receipt cap room) := by
  let t:=Fin.last es.length
  have loc : Prefix.boundaryIndex j t=stop := Prefix.index_terminal _ j
  have fitted (i s) : qty i≤cap (named S π depth (q).mark (q).exclusive (q).order (i,s)) := by
    rw [←data]
    exact (q).fits t i s
  obtain ⟨agree,room,placement⟩:=Terminal.sparse_terminal (q).exclusive B pad order sz (q).order ident
    index position cap fitted (fun i l _ _ h=>prior i l h)
  have dense :=receipt.old_width (siteNumber h (2^W) k).injective pad
  have sparse : installedWidths ch qty=avail := agree.trans dense
  have cursor : installedWidths ch qty=wire stop := by
    rw [←data,←loc]
    exact (q).atWidth t
  let head:=sparse.symm.trans cursor
  refine ⟨head,room,?_⟩
  have previous:=endpoint_mapping possible R j t stop loc qty data avail sparse head fitted
  refine previous.trans (congrArg (fun g=>(NamedAperture.transport head.symm).toEmbedding.trans g) ?_)
  rw [placement]
  exact NamedAperture.transport_back agree dense sparse _

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.BranchRoles
end

end OAI
