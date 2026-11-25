import OAI.Hierarchy.TaggedWideSparseLivePlacement
import OAI.Hierarchy.TaggedWideDatedRows
import OAI.Hierarchy.TaggedWireTerminalPorts
import OAI.Hierarchy.TaggedWireCalendarPorts

namespace OAI
/-! # Actual chronological role bits in the original terminal matrix packing -/

set_option quotPrecheck false

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe ReportSockets WireTelescope CalendarTape
open ProtocolRAM.Calendar ProtocolRAM.Calendar.CatalogueRows ProtocolRAMEmit
open scoped Classical
variable {h W k attempts n : ℕ} {board : Board} {S : PurchaseSampler}
    {π : Equiv.Perm (Fin (2^h))} {depth : ℕ} {mark : Marks h W k attempts}
    (unique : Exclusive mark) (B : Mount (S:=S) π (name (W:=W) (k:=k)) board.rows)
    (pad : Chord (siteLast h (2^W) k+1))
    {fixed : Fin board.rows→ℕ} {stock : Goods h W k→ℕ} {reserved used : Catalysts h W k→ℕ}
    (order : Fin board.coreRows ≃ Edges S h (2^W) k)
    (sz : attempts*(ProtocolRAM.PurchaseFrozen.count h (2^W) k*ProtocolRAM.PurchaseFrozen.paths h S.degree depth)=board.boughtRows)
    (ids : Fin n ≃ Source S π depth mark)
local notation "ordinal" => board.ordinal S π depth mark order sz
local notation "origRow" => DatedRows.embed S π depth mark board order sz
local notation "ordinalRow" => DatedRows.raw S π depth mark board order sz ids
local notation "qty" => SettledMatrix.Layout.available fixed stock reserved used ∘ origRow ∘ ids
local notation "amount" => SettledMatrix.Layout.bits fixed stock reserved used
local notation "oldChord" => sorted S π depth mark ∘ ids
local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "ends" => (L).family
variable (ident : {i:Fin board.rows // 0<fixed i} ↪ Catalogue S π depth mark)
    (index : ∀ i : {r : Fin board.rows // 0 < fixed r},
      board.ordinal S π depth mark order sz (ident i) = i.val)
    (position : ∀i,filledChord B.actual pad i.val=sorted S π depth mark (.inl (ident i)))
local notation "namedAt" => named S π depth mark unique ids
local notation "terminalAt" => ports S π depth mark unique fixed stock reserved used ident

include index

private theorem sparse_lift (s : Source S π depth mark)
    (on : 0<SettledMatrix.Layout.available fixed stock reserved used (origRow s)) :
    NamedAperture.liftRow fixed (Sum.elim stock fun a=>reserved a-used a) ident
      ⟨origRow s,on⟩=s := by
  cases s with
  | inl e =>
    change Sum.inl (ident ⟨ordinal e,on⟩)=Sum.inl e
    let row : {r : Fin board.rows // 0 < fixed r} := ⟨ordinal e, on⟩
    exact congrArg Sum.inl ((ordinal).injective (index row))
  | inr g => rfl

/-- Physical sparse names and terminal labels agree on every actual original half-edge. -/
theorem sparse_names (i : Fin n) (hi : 0<qty i) (s : Bool) :
    let h : 0<amount (ordinalRow i) := by
      change 0<SettledMatrix.Layout.available fixed stock reserved used (SettledMatrix.Layout.numbered _)
      rw [DatedRows.numbered_raw]
      exact hi
    namedAt (i,s)=terminalAt ⟨(ordinalRow i,s),h⟩ := by
  intro live
  apply congrArg (fun q=>physical S π depth mark unique (orient S π depth mark q))
  change (ids i,s)=
    (NamedAperture.liftRow fixed (Sum.elim stock fun a=>reserved a-used a) ident
      ⟨SettledMatrix.Layout.numbered (ordinalRow i),live⟩,s)
  let lift:=NamedAperture.liftRow fixed (Sum.elim stock fun a=>reserved a-used a) ident
  have same : (⟨SettledMatrix.Layout.numbered (ordinalRow i),live⟩ : {x // 0<
      Sum.elim fixed (Sum.elim stock fun a=>reserved a-used a) x}) = ⟨origRow (ids i),hi⟩ :=
    Subtype.ext (DatedRows.numbered_raw S π depth mark board order sz ids i)
  exact Prod.ext ((congrArg lift same).trans (sparse_lift order sz ident index (ids i) hi)).symm rfl

include position in
/-- The equality of state placements depends only on the order of live rows sharing a chord. -/
theorem sparse_terminal (cap : Public S h W k attempts→ℕ)
    (bound : ∀i s,qty i≤cap (namedAt (i,s)))
    (orderAt : ∀i j,0<qty i→0<qty j → oldChord i=oldChord j→(i<j ↔ ordinalRow i<ordinalRow j)) :
    ∃ (widths : installedWidths oldChord qty=installedWidths ends amount)
      (room : ∀s:NamedAperture.LiveEnd amount,amount s.val.1≤cap (terminalAt s)),
      statePlace S π depth mark unique ids qty cap bound=
      (NamedAperture.transport widths).toEmbedding.trans
        (NamedAperture.livePlace ends amount terminalAt cap room) := by
  have counts (i:Fin n) : amount (ordinalRow i)=qty i := by
    change SettledMatrix.Layout.available fixed stock reserved used (SettledMatrix.Layout.numbered _)=_
    rw [DatedRows.numbered_raw]; rfl
  have vacant (i) (idle:i∉Set.range ordinalRow) : amount i=0 := by
    obtain ⟨e,hit,empty⟩:=DatedRows.blank S π depth mark board order sz ids idle
    change SettledMatrix.Layout.available fixed stock reserved used (SettledMatrix.Layout.numbered _)=_
    rw [hit]
    change fixed e=0
    by_contra nonzero
    have pos : 0 < fixed e := Nat.pos_of_ne_zero nonzero
    exact empty ⟨ident ⟨e,pos⟩, index ⟨e,pos⟩⟩
  have names := sparse_names (stock:=stock) (reserved:=reserved) (used:=used) unique order sz ids ident index
  have active (i : Fin n) (hi : 0<qty i) : ends (ordinalRow i)=oldChord i := by
    have loc (s : Bool) : (portGraph _).vertex (ends (ordinalRow i)) s=
        (portGraph _).vertex (oldChord i) s := by
      let q : NamedAperture.LiveEnd amount := ⟨(ordinalRow i,s),by simpa [counts] using hi⟩
      have atDense:=native_site S π depth mark unique B pad fixed stock reserved used ident q position
      exact atDense.symm.trans ((congrArg (fun u=>name (site S u)) (names i hi s).symm).trans
        (named_site S π depth mark unique ids i s))
    exact Subtype.ext (Prod.ext (loc false) (loc true))
  have widths : installedWidths oldChord qty=installedWidths ends amount := by
    apply Fintype.sum_of_injective ordinalRow (ordinalRow).injective
    · intro x hx
      simp [vacant x hx]
    · intro i
      by_cases hi : 0<qty i
      · rw [counts,active i hi]
      · rw [counts]
        simp only [Nat.eq_zero_of_not_pos hi, zero_smul]
  have room (s : NamedAperture.LiveEnd amount) : amount s.val.1≤cap (terminalAt s) := by
    rcases s with ⟨⟨r,k⟩,live⟩
    have present : r∈Set.range ordinalRow := by
      by_contra bad
      exact (Nat.ne_of_gt live) (vacant r bad)
    obtain ⟨i,rfl⟩:=present
    have hi : 0<qty i := (counts i) ▸ live
    calc amount (ordinalRow i) = qty i := counts i
         _ ≤ cap (namedAt (i,k)) := bound i k
         _ = cap (terminalAt ⟨(ordinalRow i,k),live⟩) := congrArg cap (names i hi k)
  refine ⟨widths,room,?_⟩
  exact NamedAperture.sparse_place oldChord ends qty amount ordinalRow counts vacant active orderAt namedAt
    terminalAt cap bound room names widths

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
end

end OAI
