import OAI.Hierarchy.ProbeFixedWideSpillCases
import OAI.Hierarchy.ProbeFixedWideDirectInvoice
import OAI.Hierarchy.ProbeFixedWideBroadcastBits

namespace OAI
/-! # The original direct, mate, tree and overflow invoice at a dated attempt -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT ReportSockets
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_attempt_invoice :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.keepLimit*width+1 ≤ 2^h →
      let P:=v.widePlacement h width
      let A:=v.privateArena P h width
      let stock:=v.fixedTerminalStock P h width
      let r:=Fintype.card (Slots h (2^v.W) k)
      let page:=v.wideSignedPage h width stock
      let count:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A))
      let owners:=sinkBank (v.catalystStaticStart P h width) count r P.catalogue.rows
      let banks:=TerminalLayout.settlement page stock
      let src:=TerminalLayout.source page
      let tab:=TerminalLayout.table page
      let dst:=TerminalLayout.destination page
      ∀size,A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)),
        let m:=v.wideSignedMidAt h width size stock v.radius π (wideRouteOrder h (2^v.W) k) raw
        let out:=run (v.wideSignedChart h width stock) (events v.mesh) m
        let days:=v.birthMarks P h width r banks src tab dst owners m
        let ord:=P.catalogue.ordinal v.sampler π v.depth days (v.wideOrder h width) rfl
        let len:=extendedLength ord (lenCode v.sampler π v.depth days v.radius)
        ∀a, Event.attempt a∈events v.mesh →
          let f := v.nativeFormats P h width a
          let forest := v.nativeTrees P h width a
          (∃tree : Fin f.pricedArea.rows→List (Fin P.catalogue.rows), forest.Reads out tree ∧
            ∀i,(out (f.pricedArea.broadcast+i.val)).val≠0 → ((tree i).map len).sum≤v.cost.atAttempt a) →
          ((v.wideEventSlices h width v.maxBits (.attempt a)).map (fun t=>t.toll out len width)).sum≤
            (v.receipts P h width r banks src tab dst owners out (.attempt a)).install := by
  let : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  filter_upwards [v.spill_word_room,v.wide_row_room,Filter.eventually_ge_atTop v.wideStockHeight,Filter.eventually_ge_atTop v.maxBits]
    with h words rows age enc
  intro width small budget P A stock r page count owners banks src tab dst size extent π raw m out days ord len
    a live f forest located
  obtain ⟨occurrences,bound,copies,stored,product⟩ :=
    (v.wide_broadcast_bits h width size extent v.radius π raw age budget small enc a live).1
  let chart := v.wideSignedChart h width stock
  let sizes := v.wide_stock_sizes h width age budget small
  have run := v.wide_stock_at h width size extent v.radius π raw age budget small
  have low := (v.wide_spill_source h width size extent π raw sizes.words.addresses run.mounted_all).1
  obtain ⟨prior,tail,split⟩ := List.append_of_mem live
  let entry := Calendar.run chart prior m
  have cut := slot_of_split chart m (.attempt a) prior tail entry split rfl run.mounted_all
  obtain ⟨mask,mate,pair,charge⟩ := v.wide_direct_invoice h width size extent π raw a entry prior tail
    sizes.words.addresses sizes.roles (rows width).1 (rows width).2 days rfl run.mounted_all cut
  obtain ⟨tree,reads,tariff⟩ := located
  exact v.true_repair_invoice P h width r banks src tab dst owners π days (v.wideOrder h width) rfl out _ _
    low.1 _ low.2 words.1 words.2.1 (rows width).1.le (fun _ => v.catalystPairOwners P h width)
    (fun _ => v.catalystPairParity P h width) a v.maxBits mask mate tree occurrences pair reads bound copies
    stored product (fun i _ => charge i) tariff

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
