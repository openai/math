import OAI.Computability.VPVNP.CompressorCurrentResident
import OAI.Computability.VPVNP.CompressorSelectedPayloadHistory

/-!
# Selected payloads at a compressor boundary

The current incidence graph and placement directories share their memory
with the parser data produced by earlier passes. Appending a selected pass
retains its post-memory as the new snapshot. For older snapshots, only the
completed levels and the current graph's pointer and incidence bank need
to agree with the previous boundary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DetailedResident

open BurstRAM Compression DescriptorSpace PairSimulation.LocalHistory PairSimulation.TraversalRows
open PairSimulation.TraversalRoles
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) {w : ℕ}

/-- Readable current graph, placement directories and selected parser snapshots. -/
def resident (initial : TaggedLayer) (L : Layout) (base n : ℕ) (initialFrame : Fin 8 → Word w)
    (data : SelectedPayloadHistory.Data (w := w) B f hf) : ScheduledTrace.Resident B f hf w :=
  fun past {_ _} X m =>
    CurrentResident.resident B f hf initial L base n initialFrame past X m ∧
    SelectedPayloadHistory.Past B f hf L data past m

variable {B f hf} {initial : TaggedLayer} {L : Layout} {base n a g : ℕ}
variable {initialFrame : Fin 8 → Word w} {data : SelectedPayloadHistory.Data (w := w) B f hf}
variable {past : List (SelectedLevel B f hf)} {X : State a g} {m out : Memory w}

theorem current (h : resident B f hf initial L base n initialFrame data past X m) :
    CurrentResident.resident B f hf initial L base n initialFrame past X m := h.1

theorem payloads (h : resident B f hf initial L base n initialFrame data past X m) :
    SelectedPayloadHistory.Past B f hf L data past m := h.2

/-- The first cursor publisher creates the current graph with an empty
list of completed parser passes. -/
theorem initial_live {b width : ℕ} {workspace : Word w}
    (cursor : BlockStartupPrefix.Resident L a b g width n workspace m X)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) (BlockInitialPackets.post L a b g width m) out)
    (positive : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) :
    resident B f hf ⟨leafLayer (siteOrder X),.cursor⟩ L (endAddress L) n
      (CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1)
        b g a width (incidenceStart L 0)) data [] X out :=
  ⟨CurrentResident.initial_live cursor agree positive fields fit, SelectedPayloadHistory.Past.empty⟩

theorem transfer (h : resident B f hf initial L base n initialFrame data past X m)
    (index : past.length < L.levels) (fit : endAddress L < 2^w) (fields : 14 ≤ L.shape.scalarFields)
    (slots : IncidenceDirectory.slotCount X ≤ slotCapacity L)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) m out) :
    resident B f hf initial L base n initialFrame data past X out := by
  refine ⟨CurrentResident.transfer h.1 index fit fields slots agree, h.2.transfer ?_⟩
  intro x lo _
  exact (agree x (by simpa only [levelStart,Nat.zero_mul,Nat.add_zero] using lo)).symm

/-- Both the newly published graph and its parser data are read from the
same post-memory. The predecessor frame keeps the last pass's output graph
as well as the full data of strictly earlier levels. -/
theorem append {v : SelectedLevel B f hf}
    (h : resident B f hf initial L base n initialFrame data past v.input m)
    (next : CurrentResident.resident B f hf initial L base n initialFrame
      (past ++ [v]) (v.pass.next v.term) out)
    (emitted : data past.length v out)
    (previous : ∀ x, levelsBase L ≤ x → x < levelStart L past.length → out x = m x)
    (input : SourceTransport.Agree (SelectedPayloadHistory.GraphCells L past.length) m out) :
    resident B f hf initial L base n initialFrame data (past ++ [v]) (v.pass.next v.term) out :=
  ⟨next, h.2.append emitted previous input⟩

variable {pub : Fin 11 → Word w} {pitch : Word w} {total ordinal : ℕ}

/-- Project a detailed boundary to the current graph expected by the
terminal bootstrap, preserving the concrete scheduler words. -/
theorem currentBoundary (h : ScheduledTrace.Boundary (resident B f hf initial L base n initialFrame data)
    pub pitch total ordinal past X m) :
    ScheduledTrace.Boundary (CurrentResident.resident B f hf initial L base n initialFrame)
      pub pitch total ordinal past X m :=
  ⟨h.bank,h.tag,h.ordinalValue,h.totalValue,h.stride,h.stored.1⟩

/-- The existing cursor interval supplies the detailed initial boundary
for any selected parser predicate. -/
theorem initialBoundary (h : ScheduledTrace.Boundary (CurrentResident.resident B f hf initial L base n initialFrame)
    pub pitch total ordinal [] X m) :
    ScheduledTrace.Boundary (resident B f hf initial L base n initialFrame data)
      pub pitch total ordinal [] X m :=
  ⟨h.bank,h.tag,h.ordinalValue,h.totalValue,h.stride,h.stored,SelectedPayloadHistory.Past.empty⟩

end CompressorRecords.DetailedResident

end VPVNP
end Computability
end OAI
