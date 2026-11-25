import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout
import OAI.Hierarchy.ProtocolRAMNativeReserveSink

namespace OAI
/-! # Preserving original paid archive words through reserve and route settlement -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe Calendar
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

theorem sink_prefix {w r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    {core : I→List (Fin edges)} {center : J→List (Fin edges)}
    (s : Sink r edges) (m : Memory w) (enum : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (x : ℕ)
    (width : x<s.banks.width.base ∨ s.banks.width.base+edges≤x)
    (tape : x<s.source) (packed : x<s.table) (emit : x<s.destination) :
    s.output m enum ci cj x=m x := by
  let settled:=RouteSettlement.output s.banks s.source m enum ci cj
  let fields:=RouteSettlement.fields s.banks s.geometry
  change ProtocolRAMEmit.emitted s.destination (reportedRows (n:=edges) [] fields settled)
    ((report s.table edges s.owners fields).apply settled) x=m x
  have second : x<s.destination+3*edges := by omega
  have third : x<s.destination+6*edges := by omega
  simp only [ProtocolRAMEmit.emitted,fillSegment,not_le.mpr emit,not_le.mpr second,
    not_le.mpr third,false_and,ite_false]
  refine (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ x (.inl packed)).trans ?_
  unfold settled RouteSettlement.output
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (by
    intro i
    have bound:=((enum i).edge).isLt
    unfold RouteSettlement.address
    omega)]
  exact ProtocolRAMGeneratedWrite.frame_image s.source (2*r) (RouteSettlement.words s.banks) m x (.inl tape)

namespace CatalystArchive.TerminalLayout
open Calendar.CoreRoute

/-- The reserve and the full sink preserve the live stock, role, and history
addresses outside the short interval that receives the settled edge widths. -/
theorem archive_prefix_at {w entries r count : ℕ} (bits start n reserveAmount : ℕ)
    (cat : CatalogueRows.Board) (stock : Bank) (site : Fin entries→Fin count) (debit : Fin entries→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (archive : Memory w) (x : ℕ)
    (before : x<6*2^bits) (offWidth : x<2^bits ∨ 2^bits+cat.rows≤x) :
    let b:=settlement bits stock
    let a:=reserve start n bits
    let sink:=cat.sink r b (source bits) (table bits) (destination bits) (sinkBank start n r cat.rows)
    sink.output (ReserveUse.output a b reserveAmount site debit archive) enum ci cj x=archive x := by
  intro b a sink
  let B:=2^bits
  have prior : x<6*B:=before
  have stock : x<sink.banks.width.base ∨ sink.banks.width.base+cat.rows≤x := by
    change x<1*B ∨ 1*B+cat.rows≤x
    simpa only [Nat.one_mul] using offWidth
  rw [sink_prefix sink _ enum ci cj x stock (by change x<9*B; omega)
    (by change x<10*B; omega) (by change x<18*B; omega)]
  exact ReserveUse.frame a b reserveAmount site debit archive x
    (.inl (by change x<6*B;exact before)) (.inl (by change x<7*B;omega))
    (.inl (by change x<8*B;omega))

theorem archive_prefix {w n r count : ℕ} (bits start reserveAmount : ℕ)
    (cat : CatalogueRows.Board) (stock : Bank) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    {I J : Type*} [Fintype I] [Fintype J] {core : I→List (Fin cat.rows)} {center : J→List (Fin cat.rows)}
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (archive : Memory w) (x : ℕ)
    (before : x<6*2^bits) (offWidth : x<2^bits ∨ 2^bits+cat.rows≤x) :
    let b:=settlement bits stock
    let a:=reserve start n bits
    let sink:=cat.sink r b (source bits) (table bits) (destination bits) (sinkBank start n r cat.rows)
    sink.output (ReserveUse.output a b reserveAmount site debit archive) enum ci cj x=archive x :=
  archive_prefix_at bits start n reserveAmount cat stock site debit enum ci cj archive x before offWidth

end CatalystArchive.TerminalLayout
end Hierarchy.ProtocolRAM
end

end OAI
