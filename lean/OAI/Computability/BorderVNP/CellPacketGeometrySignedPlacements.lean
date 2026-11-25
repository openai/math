import OAI.Computability.BorderVNP.CellPacketGeometryNativePlaces
import OAI.Computability.BorderVNP.CellPacketGeometryTerminalFeeds
import OAI.Computability.BorderVNP.CellPacketGeometrySignedReports

/-! # The actual ordered signed descriptor operand at every packet placement -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.SignedFields

open Crossing Shortening.PublicCapacity Packing Packing.Inherited FrozenTape CellSparse CellSparse.Packet
open CellSparse.Packet.Source FinalReports SiteWords VPVNP.BurstRAM RoutingISA CellPacket
open Packing.CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork

variable {s : Shape} {n C d k w t J : ℕ} {Z H R B : Type} [Fintype Z] [Fintype H] [Fintype R] [Fintype B]
    (F : Fields s.sites s.edges n C d k w Z) (occupied : Fin s.edges → Z) (portUsed : Fin n → Bool)
    (boxes : Fin s.sites → List (Source.Box (Fin J)))
    (old : Frame (Z ⊕ H) (FrozenTape.Pins R B t))
    (entry : Fin J → Fin s.sites) (arena stride gap desc g digits : ℕ) (valid : Z)
    (z : Z → Bool) (saved : H → Bool)

local notation3 (prettyPrint := false) "src" => liveFrame (H:=H) F boxes entry arena stride gap desc g digits
local notation3 (prettyPrint := false) "feed" => Terminal.feeds (s:=s) F occupied portUsed boxes old src valid
local notation3 (prettyPrint := false) "args" => (feed).arguments (Sum.elim z saved)
local notation3 (prettyPrint := false) "slot" => fun j : Fin J => value (fun b => (frame F boxes entry arena stride gap desc g digits).eval z (.inr j,b))

variable {a : ℕ} {I : Type} (T : LiveWords.Template (Spare.Field C g digits (Fin J)) I (Fin J) a (C+1))
    (read : Fin a → I → ℕ)
local notation3 (prettyPrint := false) "ref" => (fun j : Fin J => Sum.inl (Sum.inr j) : Fin J → T.Fields)

/-- The dynamic input read by each opaque reference is the actual signed
pointer selected by the address circuit. This identity includes zero and
does not require the factor body at this key to pass its later checks. -/
theorem sourcePointer (i : Fin J) : T.arguments args read (ref i) = slot i := by
  apply congrArg value
  funext b
  exact liveFrame_eval F boxes entry arena stride gap desc g digits z saved (.inr i) b

variable {p chunk dest header : ℕ} (mem : ℕ → ℕ) (dir : Directory (Fin a) (Fin J) (C+1))
    (fs : Fin J → List Factor) (ext scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool)

/-- Read the distinct markers, original descriptor pointer columns, and
cell metadata directly from the jointly published signed words. The
external, scratch and burst addresses come from the real task table. -/
theorem sourcePlacements (published : Published dir p chunk dest header ref (T.arguments args read) mem) :
    ∃ fit : C+1+dir.words.length+(C+1) ≤ 2^p,
    ∃ space : C+1+(Schema.coords (dir.referenceRows ref).length).length+(C+1) ≤ 2^chunk,
      let cells := atRanges (dest:=dest) (H:=header) dir ref fit space mem slot fs ext scratch burst external
      TypedBatch.SourceShape cells dir ∧
        ∀ c, CellMemory (cells c) ((cells c).publicBase+((Supplement.prefixParts (cells c)).flatMap Part.publicBuffer).length)
          (descriptorBank dest p+mem (descriptorBank dest p+(2^chunk+(Markers.stop space c).val))) mem := by
  exact published.places dir ref mem slot fs ext scratch burst external
    (sourcePointer F occupied portUsed boxes old entry arena stride gap desc g digits valid z saved T read)

end CellPacketGeometry.History.Native.SignedFields

end BorderVNP
end Computability
end OAI
