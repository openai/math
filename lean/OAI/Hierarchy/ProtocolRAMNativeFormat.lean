import OAI.Hierarchy.ProtocolRAMCalendarMarketTypes
import OAI.Hierarchy.ProtocolRAMCalendarPostLayout
import OAI.Hierarchy.ProtocolRAMStockCommitDebit
import OAI.Hierarchy.ProtocolRAMCalendar
import OAI.Hierarchy.ProtocolRAMCalendarTime

namespace OAI
/-! # The physical frozen market, post board, priced stock area and its input banks -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseStage
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k : ℕ}

def Market.layout (v : Market z d k) := PurchaseStage.postLayout v.flags v.rows

def testedBoard {q d : ℕ} (s : FailureWords) (B : PurchaseStage.Repair q d) : PurchaseStage.Repair q d :=
  {B with failedMIS:=s.bank, tests:={B.tests with discrepancy:=
    {B.tests.discrepancy with rows:=s.rows,bound:=s.globalBound,term:=s.effective}}}

/-- Inputs determined by the public protocol menu: fixed sampler and strip test, immutable
histogram field banks, the geometric incidence directory, and the bounded stock cap. -/
structure Format (z d k q goods : ℕ) where
  market : Market z d k
  batch : Repair q goods
  histMass : ℕ
  indexBits : ℕ
  sources : StockCommit.Sources
  occurrences : ℕ
  coordinates : ℕ
  limit : ℕ

variable {q goods : ℕ}

def Format.atTime (p : Format z d k q goods) (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (a : Attempt) : Market z d k := {p.market with phase:=deadline c finish prices a}

def Format.testsStart (p : Format z d k q goods) := p.market.flags+p.market.rows

def Format.checkedBoard (p : Format z d k q goods) : Repair q goods :=
  let b := testedBoard p.market.failures p.batch
  { b with
    batch := {b.batch with copies := p.histMass}
    tests := PostLayout.placeTests b.tests p.testsStart }

def Format.maskStart (p : Format z d k q goods) :=
  PostLayout.afterTests (testedBoard p.market.failures p.batch).tests p.testsStart

def Format.board (p : Format z d k q goods) :=
  PostLayout.place p.market.layout p.checkedBoard p.maskStart p.indexBits

def Format.area (p : Format z d k q goods) : StockCommit.Area :=
  ⟨p.board.verdict+1,p.market.rows,p.occurrences,p.coordinates,p.limit⟩

/-- The seed copies the same authoritative commodity bank as the signed price scan.
It reserves a distinct sentinel for ordinary costs even when the previous reserve
immediately follows the source stock. -/
def Format.stockSource (p : Format z d k q goods) : StockCommit.Sources :=
  { p.sources with
    old := {p.sources.old with base := p.market.shelf.stockBase}
    mode := word p.board.modeOut }

def Format.labelStart (p : Format z d k q goods) := p.board.verdict+1

def Format.pricedArea (p : Format z d k q goods) : StockCommit.Area :=
  {p.area with start:=p.labelStart+p.occurrences}

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
