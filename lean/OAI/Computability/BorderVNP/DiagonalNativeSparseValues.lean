import OAI.Computability.BorderVNP.CellSparseExteriorNativeOwned
import OAI.Computability.BorderVNP.FragmentRowsPublishedStream
import OAI.Computability.BorderVNP.DiagonalExternalFragmentValues

/-! # The actual signed sparse cell driver reads the original geometric end assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open VPVNP.BurstRAM Crossing Packing Packing.Directory Packing.CellAddresses Packing.Inherited
open RoutingISA RoutingISA.SparseExterior RoutingISA.CompactMachine Cube.Physical CellSparse
open scoped Classical

variable {D R r literalWidth link V g m n entries desc w : ℕ}
variable (arena : SignedTaskArena.Layout) (N : Network D (FreeBlock R V) (fun _ => g))
variable (cell : N.Site → Fin arena.fragments.cells) (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
variable (head base : ℕ) (old : Memory w) (mem : ℕ → ℕ)
local notation "f" => FragmentRows.Layout.fromFrame head mem
variable (fits : (FragmentRows.Layout.fromFrame head mem).Fits w mem)
variable (cells : arena.fragments.cells=(FragmentRows.Layout.fromFrame head mem).cells)
variable (rows : CableRows N cell edgeID portID (FragmentRows.Layout.fromFrame head mem).host mem)
variable (hg : 0<g) (room : r*(2*literalWidth+R*link) ≤ V*g) (pp lp : ℕ → ℕ × ℕ)
variable (place : LivePlacement N cell edgeID portID lp)
local notation "supplied" => (fun c : ℕ => mem (FragmentRows.Layout.supplied f+c))
variable (counts : ∀ c, mem ((FragmentRows.Layout.fromFrame head mem).supplied+c.val)=suppliedSize N cell c)
variable (privateAfter : ∀ j : Fin entries, mem ((FragmentRows.Layout.fromFrame head mem).supplied+(pp j.val).1) ≤ (pp j.val).2)
variable (input : FreePort R r literalWidth → Bool) (ends : Bool → LiveBit N cell → Bool)
local notation "bank" => fillFree hg room input (fun _ => false)
local notation "data" => endData N cell edgeID portID bank ends
local notation "dir" => freeDirectory R r literalWidth link V g entries desc
local notation "published" => readings (Directory.ISA.publish old head base (Packing.Directory.Layout.directory dir pp lp))

include rows place counts privateAfter in
/-- The return of the physical serializer for a true global cell restores its precise
typed supply and report tail. This uses the compact seven-word directory that the
original-site and live data passes published, even when a supplied lane is unused. -/
theorem emitted_owned_values (c : Fin arena.fragments.cells) (dense : ℕ) (tail : List Bool)
    (original : readings old (head+8)=base) (apart : head+9 < base)
    (rowRoom : ((dir).directory pp lp).length < 2^w)
    (words : ∀ i : Fin ((dir).directory pp lp).length, ∀ x ∈ ((dir).directory pp lp)[i.val].words, x<2^w)
    (ptr : mem (head+8)=published (head+8)) (num : mem (head+9)=published (head+9))
    (kept : ∀ addr, base ≤ addr → addr < base+7*((dir).directory pp lp).length → mem addr=published addr)
    (order : Ordered (supplied c.val) 0 (spans ((f).stream mem) data c.val)) :
    (emittedOwned arena f mem fits cells c data dense (supplied c.val) tail).field.values =
      List.ofFn (Placement.endSupply N cell c edgeID portID bank ends) ++ tail := by
  have actual := FragmentRows.stream_from_published old head base dir pp lp mem original apart rowRoom words ptr num kept
  change expand (supplied c.val) tail 0 (spans ((f).stream mem) data c.val) = _
  rw [actual] at order ⊢
  exact expand_endSupply (desc:=desc) N cell edgeID portID rows hg room pp lp supplied place counts privateAfter input ends c tail order

include rows place counts privateAfter in
/-- The private machine on the true physically compressed burst has the signed
sum of the original cell's sparse terms on its complete end vector and report tail. -/
theorem emitted_owned_value (c : Fin arena.fragments.cells) (dense : ℕ) (tail : List Bool)
    (directory : CellSparse.Directory) (privateWires length : ℕ) (hw : 0 < w)
    (original : readings old (head+8)=base) (apart : head+9 < base)
    (rowRoom : ((dir).directory pp lp).length < 2^w)
    (words : ∀ i : Fin ((dir).directory pp lp).length, ∀ x ∈ ((dir).directory pp lp)[i.val].words, x<2^w)
    (ptr : mem (head+8)=published (head+8)) (num : mem (head+9)=published (head+9))
    (kept : ∀ addr, base ≤ addr → addr < base+7*((dir).directory pp lp).length → mem addr=published addr)
    (order : Ordered (supplied c.val) 0 (spans ((f).stream mem) data c.val)) (profile : directory.ProfileWidths) :
    let field := (emittedOwned arena f mem fits cells c data dense (supplied c.val) tail).field
    SparseExterior.clock w directory privateWires field ≤ length^25 →
      (∑ o ∈ choices SparseExterior.driver length (CompactFrame.pack w (Packet.input directory privateWires field.bytes)), o.2.value) =
        (⟨directory,privateWires,List.ofFn (Placement.endSupply N cell c edgeID portID bank ends) ++ tail⟩ : CellInput).weight := by
  intro field paid
  have trueData := emitted_owned_values (desc := desc) arena N cell edgeID portID head base old mem fits cells rows
    hg room pp lp place counts privateAfter input ends c dense tail original apart rowRoom words ptr num kept order
  have value := SparseExterior.cell_value directory privateWires field hw profile paid
  change field.values = _ at trueData
  rw [trueData] at value
  exact value

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
