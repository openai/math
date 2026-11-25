import OAI.Hierarchy.ProtocolRAMTerminalSinkSpace
import OAI.Hierarchy.ProtocolRAMCatalogueRowFields
import OAI.Hierarchy.ProtocolRAMCalendarWhole

namespace OAI
/-! # Reading core and acquired geometry from the terminal reporter -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM
open scoped Fin.CommRing

variable {W r : ℕ} {I J : Type*} [Fintype I] [Fintype J]

/-- Six geometric words. Settlement determines the seventh word, the edge width,
from the installed links and the two routed stocks. -/
structure Reads (row : ProtocolRAMEmit.Row) (v : View) (id : ℕ) : Prop where
  group : row.group=v.group
  leftField : row.endpoint=min v.left v.right
  rightField : row.opposite=max v.left v.right
  link : row.link=id
  lengthField : row.lengthCode=v.lengthCode
  menu : row.menu=v.menu

theorem Reads.of_fields {row : ProtocolRAMEmit.Row} {v : View} {id : ℕ}
    (h : ∀ f : Fin 7, f≠4 → row.field f=v.fields id f) : Reads row v id :=
  ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 5 (by decide),h 6 (by decide)⟩

omit [Fintype I] [Fintype J] in
theorem Board.core_reads (b : Board) (banks : RouteSettlement.Banks) (source table destination : ℕ)
    (owners : Bank) (m : Memory W) {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (i : Fin b.coreRows) (room : b.idBase+b.rows<2^W)
    (fits : ∀ f : Fin 7, f≠4 → (b.geometry f).Fits W banks.width.base)
    (space : banks.width.base+b.rows≤ source) :
    Reads ((b.sink r banks source table destination owners).terminalRows m enum ci cj (b.coreIndex i))
      (b.core.view m (i.val:Word W)) (b.idBase+i.val) := by
  apply Reads.of_fields
  intro f keep
  exact ((b.sink r banks source table destination owners).terminal_field m enum ci cj (b.coreIndex i) f keep
    (fits f keep) space).trans (b.core_read m i room f)

omit [Fintype I] [Fintype J] in
theorem Board.bought_reads (b : Board) (banks : RouteSettlement.Banks) (source table destination : ℕ)
    (owners : Bank) (m : Memory W) {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (i : Fin b.boughtRows) (room : b.idBase+b.rows<2^W) (wide : 1<2^W)
    (fits : ∀ f : Fin 7, f≠4 → (b.geometry f).Fits W banks.width.base)
    (space : banks.width.base+b.rows≤ source) :
    Reads ((b.sink r banks source table destination owners).terminalRows m enum ci cj (b.boughtIndex i))
      (b.bought.view m (i.val:Word W)) (b.idBase+(b.coreRows+i.val)) := by
  apply Reads.of_fields
  intro f keep
  exact ((b.sink r banks source table destination owners).terminal_field m enum ci cj (b.boughtIndex i) f keep
    (fits f keep) space).trans (b.bought_read m i room wide f)

/-- The two receipts cover the whole physical output array, including dormant
acquisition placeholders. -/
theorem Board.split_index (b : Board) (i : Fin b.rows) :
    (∃ j, b.coreIndex j=i) ∨ (∃ j, b.boughtIndex j=i) := by
  by_cases head : i.val<b.coreRows
  · exact .inl ⟨⟨i.val,head⟩,Fin.ext rfl⟩
  · have stop := i.isLt
    change i.val<b.coreRows+b.boughtRows at stop
    refine .inr ⟨⟨i.val-b.coreRows,by omega⟩,Fin.ext ?_⟩
    change b.coreRows+(i.val-b.coreRows)=i.val
    omega

omit [Fintype I] [Fintype J] in
/-- The role directory is format-only. Its eight lanes per edge survive the
complete weighted scatter and are available to the seven-word native printer. -/
theorem Board.owners_after (b : Board) (banks : RouteSettlement.Banks) (source : ℕ)
    (owners : Bank) (m : Memory W) {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (enum : Fin r ≃ RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (mounted : Owners owners b.rows m) (before : owners.base+owners.size≤banks.width.base)
    (space : banks.width.base+b.rows≤ source) :
    Owners owners b.rows (RouteSettlement.output banks source m enum ci cj) := by
  intro i j
  apply Eq.trans _ (mounted i j)
  exact RouteSettlement.output_below banks source m enum ci cj _
    ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos owners.bits)) owners.base).trans_le before) space


end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
