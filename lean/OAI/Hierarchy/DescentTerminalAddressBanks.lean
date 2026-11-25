import OAI.Hierarchy.DescentTerminalEmitter
import OAI.Hierarchy.DescentTerminalPositionGather
import OAI.Hierarchy.DescentTerminalEmitterSpace
import OAI.Hierarchy.DescentTerminalEmitterSources
import OAI.Hierarchy.DescentTerminalRowArenaSort

namespace OAI
/-! # Physical banks of the terminal emitter, data flights, and site directory -/

namespace Hierarchy.DescentTerminalEmitter.Allocation
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalHeaderScatter
noncomputable section

/-- Addresses 0–11 and 12–23 are the earlier geometry/width banks of the two sparse
publication scans. 24–31 are the real local-book inputs, 32–36 are the route inputs,
and 37–42 are half/lane/home/event/weight/table for the scalar fold. Some views may
refer to the same attained source column. -/
abbrev Sources := Fin 43→Bank

def region (s:Shape) (i f base t:ℕ) : Bank := ⟨base+t*slab s i f,power s i f⟩

def legs (s:Sources) (publicFmt:Bool) : DescentTerminalScatterChip.Layout := if publicFmt then
  ⟨s 12,s 13,s 14,s 15,s 16,s 17,s 18,s 19,s 20,s 21,s 22,s 23⟩ else
  ⟨s 0,s 1,s 2,s 3,s 4,s 5,s 6,s 7,s 8,s 9,s 10,s 11⟩

variable (s:Shape) (i f base:ℕ) (src:Sources)
local notation "b" => region s i f base

def header (fmt:Bool) (shift blank:ℕ) : Header :=
  let t:=if fmt then 2 else 0
  ⟨legs src fmt,b t,(b (t+1)).base,if fmt then f else i,s.rows,(b t).base+s.rows,shift,blank⟩

def book : DescentTerminalLocalPortBook.Gather :=
  ⟨src 24,src 25,src 26,src 27,src 28,src 29,src 30,src 31,b 4⟩
def route : DescentTerminalRouteIssue.Layout :=
  ⟨b 4,src 32,src 33,src 34,src 35,src 36,b 5,b 6⟩
def leaf : DescentTerminalLeafFold.Layout :=
  ⟨src 37,src 38,src 39,src 40,src 41,b 7,b 7,src 42⟩

/-- The format column has no extra origin; the index column adds the number of paid
candidate words and the two original sentinels to genuine public-section positions. -/
def layout (plane:DescentTerminalDataPlane.Layout) (ext:DescentTerminalDenseHeaderRAM.Layout) (blankFmt:ℕ) : Layout where
  plane:=plane
  exteriorWidths:=ext
  indices:=header s i f base src false (s.plane.rawRows+2) 0
  formats:=header s i f base src true 0 blankFmt
  book:=book s i f base src
  route:=route s i f base src
  leaf:=leaf s i f base src
  scratch:=(b 8).base
  scalar:=(b 9).base

def parity (start:ℕ) : Bank := ⟨start,1⟩

end
end Hierarchy.DescentTerminalEmitter.Allocation

namespace Hierarchy.DescentTerminalEmitter.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitterSources
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

/-- Each immutable bank uses the ordinal of its first purchased word. All attained
banks contribute zero to this prefix and keep their original bases and sizes. -/
def view (base : ℕ) (c : Columns) (j : Fin 43) : Bank :=
  match c j with
  | .attained b=>b
  | .literal n=>⟨base+offsetAt (fun i=>size (c i)) j,Nat.clog 2 n⟩

end
end Hierarchy.DescentTerminalEmitter.Compact

namespace Hierarchy.DescentTerminalDataPlane.Arena
open DescentTerminalDataPlane DescentTerminalDenseHeaderRAM DescentExteriorShelf Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section

variable (s : Shape) (origin : ℕ)
local notation "N" => s.exteriors*2^(s.headBits+s.restBits)
local notation "H" => span s.headBits s.restBits s.bitLanes s.exteriors

def size (n : ℕ) := 2^Nat.clog 2 (n+1)
def buy (base n : ℕ) : Bank := ⟨base,Nat.clog 2 (n+1)⟩

/-- Six genuine prior address/stride columns read the home-major public gather.
The seventh bank directly names the actual third-flight value. -/
def publicTapes (src : Fin 6→Bank) : DescentTerminalPublicWordRAM.Tapes :=
  ⟨src 0,src 1,src 2,src 3,src 4,src 5,⟨start s.headBits s.restBits s.bitLanes s.exteriors origin+2*N,
      exponent s.headBits s.restBits s.bitLanes s.exteriors⟩⟩

def post := origin+24*H
def «public» := buy (post s origin) (s.publicRows+2)
def raw := buy ((«public» s origin).base+(«public» s origin).size) (s.rawRows+2+(s.publicRows+2))
def headerBase := (raw s origin).base+(raw s origin).size
def column (base n i : ℕ) := buy (base+i*size n) n
def header (base : ℕ) (src : Fin 5→Bank) : DescentTerminalDenseHeaderRAM.Layout :=
  ⟨src 0,src 1,src 2,src 3,src 4,column base s.headerRows 0,column base s.headerRows 1,
    column base s.headerRows 2,column base s.headerRows 3⟩
def second := headerBase s origin+4*size s.headerRows
def finish := second s origin+4*size s.headerRows

def plane (pub : Fin 6→Bank) (cable : Fin 5→Bank) (candidate : Bank) : DescentTerminalDataPlane.Layout :=
  ⟨origin,«public» s origin,publicTapes s origin pub,candidate,raw s origin,header s (headerBase s origin) cable⟩

end
end Hierarchy.DescentTerminalDataPlane.Arena

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalRowArena DescentTerminalVertexFields
open DescentTerminalSiteShelves
open DescentTerminalDataPlane.Arena (buy size)
noncomputable section

def page (A:Arena) := buy A.finish (A.sites+1)
def events (A:Arena) (pool:ℕ) := buy ((page A).base+(page A).size) pool
def endEvents (A:Arena) (pool:ℕ) := (events A pool).base+(events A pool).size

/-- The eight earlier controls are the port-row count, live population, aligned
page ordinal, preceding shift, and the four immutable radix tables. -/
def directory (A:Arena) (early:Fin 8→Bank) : Directory :=
  ⟨A.row.locate,early 0,early 1,early 2,early 3,page A,early 4,early 5,early 6,early 7⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
