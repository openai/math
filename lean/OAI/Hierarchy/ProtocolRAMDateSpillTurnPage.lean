import OAI.Hierarchy.ProtocolRAMDateSpillTurns
import OAI.Hierarchy.ProtocolRAMDateSpillOffsets
import OAI.Hierarchy.ProtocolRAMDateSpillPage
import OAI.Hierarchy.TaggedWidePrograms

namespace OAI
/-! # The placed native five-word turn board for a single calendar date -/
noncomputable section
namespace Hierarchy.ProtocolRAM.DateSpill

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnChart ProtocolRAMTurnReplayed Calendar

structure TurnPage (roles : ℕ) where
  first : ℕ
  terminal : WideCPU.Terminal
  ranks : Page
  left : DatedSpillOffsets.Side roles
  right : DatedSpillOffsets.Side roles

namespace TurnPage
variable {roles : ℕ} (P : TurnPage roles)

def offsets : DatedSpillOffsets.Layout := ⟨P.first,P.ranks.old,P.ranks.edges⟩
def directory := P.offsets.endAt
def window : ProtocolRAMTurnWindow.Layout :=
  ⟨P.directory+4*2^P.terminal.romBits,P.terminal.turns,P.terminal.sites,P.terminal.seats⟩
def base := P.window.base
def stop := P.window.stop

def data : Data := {P.terminal.columns with oldWidth:=P.ranks.amount,site:=P.window.site}
def banks := P.terminal.board.itinerary (key P.ranks.rankStart (P.ranks.edges+P.ranks.core))
  (rank P.ranks.rankStart (P.ranks.edges+P.ranks.core) P.ranks.edges)
def chart := ProtocolRAMTurnChart.chart P.terminal.header P.terminal.headerBits P.data
def walk := ProtocolRAMTurnChart.walk P.terminal.header P.terminal.headerBits P.data P.banks.edge P.banks.tailSite P.terminal.heads
def added : Turns.Offsets := ⟨P.offsets.oldOffset,P.offsets.newOffset⟩
def words := Columns.passes P.window.src P.terminal.turns (Turns.fields P.chart P.banks P.added)
def romPasses := Relocate.passes P.terminal.rom P.directory P.terminal.romBits P.terminal.turns P.terminal.base P.base
def tables := ProtocolRAMTurnShelf.tables P.directory P.terminal.romBits P.window.src P.window.srcBits P.terminal.turns

def visit (W : ℕ) := ProtocolRAMVisitColumns.program W P.terminal.turns P.window.zero P.walk
def write (W : ℕ) := ProtocolRAMTurnShelf.program W P.terminal.turns P.terminal.sites P.terminal.seats
  P.base P.window.scratch P.window.sink P.tables
def output (W : ℕ) : Procedure W :=
  (P.visit W).seq ((ProtocolRAM.program W P.words).seq (P.write W))
def program (W : ℕ) : Procedure W :=
  ((P.offsets.program W P.left P.right).seq (ProtocolRAM.program W P.romPasses)).seq (P.output W)

def ticks := (P.offsets.time P.left P.right+clock P.romPasses)+
  ((25+206*P.terminal.turns)+(clock P.words+(15+30*(P.terminal.sites*P.terminal.seats)+740*P.terminal.turns)))

theorem cheap (W : ℕ) : CheapCode (P.program W) := by
  let off := P.offsets.program W P.left P.right
  let rom := ProtocolRAM.program W P.romPasses
  let cols := ProtocolRAM.program W P.words
  have prepare : CheapCode (off.seq rom) :=
    @cheap_seq W off rom (@DatedSpillOffsets.Layout.cheap roles P.offsets W P.left P.right)
      (@program_cheap W P.romPasses)
  have writeCols : CheapCode (cols.seq (P.write W)) :=
    @cheap_seq W cols (P.write W) (@program_cheap W P.words)
      (@ProtocolRAMTurnShelf.cheap W P.terminal.turns P.terminal.sites P.terminal.seats
        P.base P.window.scratch P.window.sink P.tables)
  have out : CheapCode (P.output W) :=
    @cheap_seq W (P.visit W) (cols.seq (P.write W))
      (@ProtocolRAMTurnCost.site_cheap W P.terminal.header P.terminal.headerBits P.window.zero
        P.terminal.turns P.data P.banks.edge P.banks.tailSite P.terminal.heads) @writeCols
  exact @cheap_seq W (off.seq rom) (P.output W) @prepare @out

end TurnPage
end Hierarchy.ProtocolRAM.DateSpill

end
end OAI
