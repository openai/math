import OAI.Computability.BorderVNP.DiagonalExternalFragmentSourceWords
import OAI.Computability.BorderVNP.FragmentRowsPublishedStream

/-! # All sparse source reads of the actual native fragment emitter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open VPVNP.BurstRAM Crossing Packing Packing.Directory Packing.CellAddresses
open RoutingISA RoutingISA.SparseExterior Cube.Physical

variable {D R r w link V g m n C entries desc W : ℕ}
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C)
    (edgeID : N.Edge ↪ Fin m) (portID : FreeBlock R V ↪ Fin n)
    (head base : ℕ) (old : Memory W) (geo : ℕ → ℕ) (actual : Fin C → Memory W)
    (hg : 0<g) (room : r*(2*w+R*link) ≤ V*g) (pp lp : ℕ → ℕ × ℕ)
    (origin stride : ℕ) (place : LivePlacement N cell edgeID portID lp)
    (input : FreePort R r w → Bool) (ends : Bool → LiveBit N cell → Bool)

local notation "f" => FragmentRows.Layout.fromFrame head geo
local notation "bank" => fillFree hg room input (fun _ => false)
local notation "data" => endData N cell edgeID portID bank ends
local notation "dir" => freeDirectory R r w link V g entries desc
local notation "published" => readings (Directory.ISA.publish old head base (Layout.directory dir pp lp))

include place in
/-- The canonical per-cell source operand proof for the exact stream read
by the actual native emitter from the published seven-word delivery directory. -/
theorem published_span_reads (c : Fin C)
    (rows : CableRows N cell edgeID portID (f).host geo)
    (counts : ∀ v : Fin C, geo ((f).supplied+v.val) = suppliedSize N cell v)
    (privateAfter : ∀ j : Fin entries, geo ((f).supplied+(pp j.val).1) ≤ (pp j.val).2)
    (bases : ∀ v : Fin C, geo ((f).host.cells+2*v.val+1) = origin+v.val*stride)
    (read : SourceWords N cell edgeID portID hg room lp origin stride input ends (fun v => readings (actual v)))
    (original : readings old (head+8)=base) (apart : head+9 < base)
    (rowRoom : ((dir).directory pp lp).length < 2^W)
    (words : ∀ i : Fin ((dir).directory pp lp).length, ∀ x ∈ ((dir).directory pp lp)[i.val].words, x<2^W)
    (ptr : geo (head+8)=published (head+8)) (num : geo (head+9)=published (head+9))
    (kept : ∀ addr, base ≤ addr → addr < base+7*((dir).directory pp lp).length → geo addr=published addr) :
    ∀ s ∈ spans ((f).stream geo) data c.val, s.Reads (actual c) := by
  rw [FragmentRows.stream_from_published old head base dir pp lp geo original apart rowRoom words ptr num kept]
  exact spans_source_reads N cell edgeID portID hg room lp origin stride input ends pp
    (fun v => geo ((f).supplied+v)) place counts privateAfter rows bases read c

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
