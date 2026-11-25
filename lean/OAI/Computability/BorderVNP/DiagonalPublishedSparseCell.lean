import OAI.Computability.BorderVNP.DiagonalReturnedSparseCell
import OAI.Computability.BorderVNP.DiagonalExternalFragmentPublishedReads
import OAI.Computability.BorderVNP.DiagonalExternalFragmentOrder

/-! # Source intervals of the sparse call on a published signed report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open VPVNP.BurstRAM Crossing Packing Packing.Directory Packing.CellAddresses Packing.Inherited
open RoutingISA RoutingISA.SparseExterior RoutingISA.CompactMachine Cube.Physical
open scoped Classical

variable {D R r literalWidth link V g m C entries desc w : ℕ}
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin m)
    (head base : ℕ) (old returned : Memory w) (actual : Fin C → Memory w)
    (hg : 0<g) (room : r*(2*literalWidth+R*link) ≤ V*g)
    (pp lp : ℕ → ℕ × ℕ) (origin stride : ℕ)
    (place : LivePlacement N cell edgeID finProdFinEquiv.toEmbedding lp)
    (input : FreePort R r literalWidth → Bool) (ends : Bool → LiveBit N cell → Bool)
local notation3 (prettyPrint := false) "mem" => readings returned
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame head (readings returned)
local notation3 (prettyPrint := false) "supplied" => fun c : ℕ => (readings returned) ((f).supplied+c)
local notation3 (prettyPrint := false) "bank" => fillFree hg room input (fun _ => false)
local notation3 (prettyPrint := false) "data" => endData N cell edgeID finProdFinEquiv.toEmbedding bank ends
local notation3 (prettyPrint := false) "dir" => freeDirectory R r literalWidth link V g entries desc
local notation3 (prettyPrint := false) "published" =>
  readings (Directory.ISA.publish old head base (Packing.Directory.Layout.directory dir pp lp))

include place in
/-- The actual sparse emitter reads pairwise ordered logical intervals and their
true physical payloads at the selected recipient. The encoded-word bound uses
their actual span count, occupied bit count, and the report's literal tail. -/
theorem published_report_spans (c : Fin C) (tail : List Bool)
    (rows : CableRows N cell edgeID finProdFinEquiv.toEmbedding (f).host mem)
    (counts : ∀ v : Fin C, supplied v.val=suppliedSize N cell v)
    (privateAfter : ∀ j : Fin entries, supplied (pp j.val).1 ≤ (pp j.val).2)
    (bases : ∀ v : Fin C, mem ((f).host.cells+2*v.val+1)=origin+v.val*stride)
    (read : SourceWords N cell edgeID finProdFinEquiv.toEmbedding hg room lp origin stride input ends
      (fun v => readings (actual v)))
    (original : readings old (head+8)=base) (apart : head+9<base)
    (length : ((dir).directory pp lp).length<2^w)
    (words : ∀ i : Fin ((dir).directory pp lp).length, ∀ x∈((dir).directory pp lp)[i.val].words, x<2^w)
    (ptr : mem (head+8)=published (head+8)) (num : mem (head+9)=published (head+9))
    (kept : ∀ addr, base≤addr → addr<base+7*((dir).directory pp lp).length → mem addr=published addr) :
    let ss := spans ((f).stream mem) data c.val
    Ordered (supplied c.val) 0 ss ∧ (∀ span ∈ ss, span.Reads (actual c)) ∧
      (encode (supplied c.val) tail 0 ss).length ≤ (2*w+4)*(ss.length+1)+2*(ss.map (fun u => u.bits.length)).sum+
        tail.length := by
  intro ss
  have written := FragmentRows.stream_from_published old head base dir pp lp mem original apart length words ptr num kept
  have order : Ordered (supplied c.val) 0 ss := by
    dsimp only [ss]
    have width : readings returned ((f).supplied+c.val)=suppliedSize N cell c := counts c
    rw [written,width]
    exact physical_spans_ordered (entries:=entries) (desc:=desc) N cell edgeID pp lp place supplied counts
      privateAfter hg room rows data c
  refine ⟨order,?_,encode_length tail ss order (returned ((f).supplied+c.val)).isLt⟩
  exact published_span_reads (entries:=entries) (desc:=desc) N cell edgeID finProdFinEquiv.toEmbedding head base old mem
    actual hg room pp lp origin stride place input ends c rows counts privateAfter bases read original apart length words
    ptr num kept

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
