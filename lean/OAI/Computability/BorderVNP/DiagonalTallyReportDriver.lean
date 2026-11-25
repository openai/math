import OAI.Computability.BorderVNP.DiagonalTallyOperandRead
import OAI.Computability.BorderVNP.DiagonalTallyReportGuess
import OAI.Computability.BorderVNP.PackedReportWriterDecoded

/-! # Traversing the actual compact owned cells and their retained bottom bundles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM DiagonalTallyOperandArray

/-- Read one word of the public control structure reached through frame slot 92. -/
def readControl (dst : Reg) (n : Fin 256) : Code := .block [.constant 60 n,
  .binary .add 60 2 60,.load dst 60]

/-- Physical layout and initial output cursors, before visiting the first owned cell. -/
def prepareSetup : Code := .block [readFrame 2 60 61 92,readControl 0 17,
  readFrame 1 60 61 90,.constant 60 6,.binary .mul 1 1 60,.binary .add 1 0 1,
  readControl 3 19,readFrame 9 60 61 95,readControl 10 27,readControl 11 22,readFrame 12 60 61 81,
  readControl 17 23,readControl 23 24,.binary .add 23 17 23,
  readControl 20 25,readFrame 30 60 61 44,readControl 31 26,.constant 32 0]

/-- Load a scalar from the current row and advance its public cursor by one word. -/
def consume (cursor dst : Reg) : Code := .block [.load dst cursor,.binary .add cursor cursor 63]

/-- Read the independently prepared six-word owned-cell header. The canonical count
region precedes all weighted use flags, and the private and external cursors differ
by the private assignment prefix. -/
def enterCell : Code := .block [.constant 63 1,.constant 60 6,consume 0 7,
  consume 0 22,consume 0 4,consume 0 15,consume 0 5,consume 0 6,
  .binary .add 24 15 4,.binary .mul 61 10 11,.binary .add 24 24 61,
  .binary .add 22 22 4,.copy 4 22,.binary .mul 5 5 60,.binary .add 5 3 5,
  .binary .mul 6 6 60,.binary .add 6 3 6,readControl 28 12,readControl 61 13,
  .binary .mul 61 7 61,.binary .add 28 28 61,.copy 8 28,.constant 29 0,.constant 21 0]

/-- The six public fields contain an actual delivered source address, clone count,
bottom lane base/stride/capacity, and beginning of the staged lanes. -/
def enterBundle : Code := .block [.constant 63 1,consume 5 16,consume 5 21,consume 5 25,
  consume 5 26,consume 5 27,consume 5 19,.binary .add 16 16 23]

/-- Preserve the packed metadata of every processed bundle until the tally materializer
has performed all its indirect reads. -/
def advancePacked : Code := .block [.load 60 20,.constant 61 3,.binary .mul 60 60 61,
  .constant 61 1,.binary .add 60 60 61,.binary .add 20 20 60]

/-- Decode the delivered positions, write the private checker bindings and the actual
use operands, then reserve the packed fields for their later indirect reads. -/
def bundleKernel : Code := .block [.seq TallySidecar.decode Packing.BottomReports.Writer.program,
  writer .unary,advancePacked]

/-- Read one retained bottom bundle and compile its supplemental records. -/
def bundleReports : Code := .seq enterBundle bundleKernel

/-- Install the true supplement row/word counts and compact tail width for this cell.
Restore the bit cursor to the start of the count-and-use region for the one guess pass. -/
def publishCell : Code := .block [.constant 63 1,readControl 60 14,.constant 61 2,
  .binary .mul 61 61 7,.binary .add 60 60 61,.store 60 29,.binary .add 60 60 63,
  .binary .sub 61 28 8,.store 60 61,.binary .sub 18 22 4,readControl 60 7,
  .binary .add 60 60 7,.store 60 18,.copy 22 4]

/-- Emit the count descriptors and all original-bundle bindings, before sampling the report tail. -/
def cellPrefix : Code := .block [enterCell,writer .count,.whileLt 5 6 bundleReports]

/-- Zero-bundle cells still contain all their genuine gadget count fields. -/
def cellReports : Code := .seq cellPrefix (.seq publishCell guessReports)

/-- The entire native preparation runs before typed task construction and all private calls. -/
def prepareCellReports : Code := .block [prepareSetup,.whileLt 0 1 cellReports,writeFrame 32 60 61 35]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
