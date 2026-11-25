import OAI.Hierarchy.ProtocolRAMTurnText
import OAI.Hierarchy.ProtocolRAMTurnCost

namespace OAI
/-! # Physical text and instruction alphabet of the chronological terminal shelf -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnText
open ProtocolRAM ProtocolRAM.Calendar ProbeStage.Native

theorem shelfTexts_eq : shelfTexts=11098 := by
  unfold shelfTexts
  exact chrono_text ..

theorem installed_text (W N sites slots header bits src base scratch sink : ℕ)
    (d : ProtocolRAMTurnChart.Data) (b : ProtocolRAMTurnItinerary.Banks) (t : ProtocolRAMTurnShelf.Tables) :
    text (ProtocolRAMTurnInstalled.program W N sites slots src base scratch sink
      (ProtocolRAMTurnChart.chart header bits d) b t)=10653 := by
  rw [ProtocolRAMTurnInstalled.program,text_seq,itinerary_text,publish_text]

end Hierarchy.ProtocolRAMTurnText

namespace Hierarchy.ProtocolRAMTurnInstalled
open ProtocolRAM

theorem cheap (W N sites slots src base scratch sink : ℕ)
    (p : ProtocolRAMTurnItinerary.Chart) (b : ProtocolRAMTurnItinerary.Banks)
    (t : ProtocolRAMTurnShelf.Tables) :
    CheapCode (program W N sites slots src base scratch sink p b t) := by
  unfold program
  refine @cheap_seq W (ProtocolRAMTurnItinerary.program W src N p b)
    (ProtocolRAMTurnShelf.program W N sites slots base scratch sink t) ?_ ?_
  · exact @ProtocolRAMTurnItinerary.cheap W src N p b
  · exact @ProtocolRAMTurnShelf.cheap W N sites slots base scratch sink t

end Hierarchy.ProtocolRAMTurnInstalled

namespace Hierarchy.ProtocolRAMChronologicalShelf
open ProtocolRAM ProbeStage.Native

theorem cheap (W N sites slots header bits initial src sb rom rb base scratch sink : ℕ)
    (d : ProtocolRAMTurnChart.Data) (heads : Bank) (b : ProtocolRAMTurnItinerary.Banks) :
    CheapCode (program W N sites slots header bits initial src sb rom rb base scratch sink d heads b) := by
  unfold program
  refine @cheap_seq W (ProtocolRAMVisitColumns.program W N initial
    (ProtocolRAMTurnChart.walk header bits d b.edge b.tailSite heads))
    (ProtocolRAMTurnInstalled.program W N sites slots src base scratch sink
      (ProtocolRAMTurnChart.chart header bits d) b (ProtocolRAMTurnShelf.tables rom rb src sb N)) ?_ ?_
  · exact @ProtocolRAMTurnCost.site_cheap W header bits initial N d b.edge b.tailSite heads
  · exact @ProtocolRAMTurnInstalled.cheap W N sites slots src base scratch sink
      (ProtocolRAMTurnChart.chart header bits d) b (ProtocolRAMTurnShelf.tables rom rb src sb N)

end Hierarchy.ProtocolRAMChronologicalShelf

end

end OAI
