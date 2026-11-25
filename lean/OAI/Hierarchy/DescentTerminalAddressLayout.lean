import OAI.Hierarchy.DescentTerminalAddressBanks
import OAI.Hierarchy.DescentTerminalSuffixData

namespace OAI
/-! # Literal layout of the terminal suffix at its shared RAM addresses -/

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalRowArena DescentTerminalVertexFields
noncomputable section

variable (S:Shape) (I:Input) (base:ℕ)

def rowArena : Arena := .make base S.sites S.terminal.rows S.packets I.parts I.totals I.boundaries I.modulo I.homes
local notation "A" => rowArena S I base
def pageEnd := endEvents A S.terminal.pool
def takeOff := DescentTerminalEmitter.Compact.shelfEnd (pageEnd S I base) I.sources
local notation "planeS" => S.terminal.plane
local notation "origin" => takeOff S I base
local notation "flightEnd" => DescentTerminalDataPlane.Arena.finish planeS origin
local notation "src0" => DescentTerminalEmitter.Compact.view (pageEnd S I base) I.sources

def bodyPlane := DescentTerminalDataPlane.Arena.plane planeS origin I.publicTapes I.cable I.candidate
def publicHeader := DescentTerminalDataPlane.Arena.header planeS (DescentTerminalDataPlane.Arena.second planeS origin) I.exterior
/-- Each scatter reader points directly into the corresponding measured
width pass, whether it needs first-row ordinals or clipped formats. -/
def inputs (j:Fin 43) : Bank :=
  if j=1 ∨ j=13 ∨ j=38 then DescentTerminalEmitter.Allocation.parity (A).start
  else if j=10 then (bodyPlane S I base).header.index
  else if j=11 then (publicHeader S I base).index
  else if j=22 then (bodyPlane S I base).header.control
  else if j=23 then (publicHeader S I base).control
  else if j=40 then events A S.terminal.pool else src0 j

def emitter := DescentTerminalEmitter.Allocation.layout S.terminal I.indexEvents I.formatEvents flightEnd (inputs S I base)
  (bodyPlane S I base) (publicHeader S I base) I.blank

def layout (O:DescentPrivateExponentRAM.Banks) : Layout :=
  ⟨I.legacy,O,I.homes,(A).order,(A).row,(A).offset,directory A I.directory,emitter S I base⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
