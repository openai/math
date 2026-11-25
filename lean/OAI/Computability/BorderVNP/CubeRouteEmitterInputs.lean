import OAI.Computability.BorderVNP.CubeRoutePinnedEntry
import OAI.Computability.BorderVNP.CubeScatterSharedArenaEmission
import OAI.Computability.BorderVNP.CubeTeamOwnedScannerWords
import OAI.Computability.BorderVNP.CubeRoutePreparedSchedule

/-! # Physical writer operands obtained from the nine-stage group computation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical TeamContraction Transmission Packing.Directory
open private public_image_word from OAI.Computability.BorderVNP.CubeScatterWriterSources

variable {w R : ℕ}

/-- The true slotted input directory and geometric allocation for the native data writer. -/
structure SlottedWriter (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pins : Pins.Layout) (pub : Arg → Word w) (slotted : Memory w) (base : ℕ) {I : Type*} [Fintype I]
    (cell : I → Fin ar.cells) (id : I ↪ ℕ) (width : I → ℕ) where
  pinFrame : Pins.Frame pins (readings pub) (readings slotted)
  pointers : readings slotted ((pub 0).val+8)=base ∧ readings slotted ((pub 0).val+12)=ar.records ∧
    readings slotted ((pub 0).val+72)=ar.hostDirectory
  rawStart : (pub 0).val+112 ≤ base
  rawEnd : base+(D.directory pp lp).length*7 ≤ ar.header.header
  teams : D.teams = pins.teams
  fields : 0 < D.fields
  tailRoom : D.entries*D.description ≤ D.teams*D.processors*(D.literal/2)
  active : 0 < pins.teams
  processors : D.processors = pins.processors
  literal : D.literal = pins.literal
  tapeRoom : pins.processors*pins.stride ≤ ar.pairBase
  substituteRoom : pins.ibase+pins.count ≤ ar.pairBase
  /-- The typed slot of every compact delivery in its actual receiving-cell bank. -/
  placement : BankPlacement D pp lp I cell id width
  destinations : D.DestinationBounds
  slabs : ∀ c, DataSlabs.size cell width c ≤ ar.cellStride

variable {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pub : Arg → Word w} {slotted data : Memory w} {base controls team : ℕ}
variable {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
variable {owner : ℕ → Fin (R+1)} {pins : Pins.Layout} {input : ℕ → ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {width : I → ℕ}

local notation "rawList" => D.directory pp lp
local notation "rawLen" => List.length (D.directory pp lp)
local notation "initialRAM" => Packing.Directory.ISA.publish slotted (Fin.val (pub 0)) base (D.directory pp lp)
local notation "shared" => ar.sharedRows (Fin.val (pub 0)) (Fin.val (Prod.fst decl)) (List.length (D.directory pp lp))

/-- Complete data and shared writer inputs at an actual prefix return. -/
structure PreparedEmission (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (owner : ℕ → Fin (R+1)) (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (pins : Pins.Layout) (pub : Arg → Word w) (m : Memory w) : Prop where
  demand : DemandInput ar D pp lp owner pub m
  pinLayout : (DataWriter.layout (readings pub) (readings m)).pins = pins
  sharedFields : let emit := DataWriter.layout (readings pub) (readings m)
                 (ar.sharedRows (pub 0).val decl.1.val (D.directory pp lp).length).Fields
                   (readings (DataWriter.publish emit pub m))
  sharedFit : let emit := DataWriter.layout (readings pub) (readings m)
              (ar.sharedRows (pub 0).val decl.1.val (D.directory pp lp).length).Fits w
                (readings (DataWriter.publish emit pub m))
  symbols : let emit := DataWriter.layout (readings pub) (readings m)
            SymbolFrame (ar.sharedRows (pub 0).val decl.1.val (D.directory pp lp).length)
              (readings (DataWriter.publish emit pub m)) ar.header.blocks ar.K ar.h decl group

/-- The actual prefix image supplies every operand of both subsequent writers. Equality of
receiving owners is only required on the genuinely populated cells. -/
theorem SlottedWriter.emission (P : SlottedWriter ar D pp lp pins pub slotted base cell id width)
    (mac : TeamOpcode.Macros w 8) (reg : Bank w)
    (native : NativeEntry ar (pub 0).val controls decl.1 R input (readings initialRAM) (readings data))
    (sources : DirectorySources ar (pub 0).val controls decl.1 (fun m => ar.ScannerWords (pub 0).val team decl.1.val
      (fun x => (group x).val) (readings pub) m decl.2) w (readings data))
    (cells : ∀ c < ar.cells, ar.receivingOwner (pub 0).val decl.1 R input c = owner c)
    (low : (pub 0).val+112 ≤ ar.header.header) (axes : ar.header.a = ar.n+1)
    (cap : ∀ p j, decl.2 p j ≤ ar.header.cap)
    (rows : rawLen+ar.header.d.choose 2 ≤ ar.maxRows) (fit : ar.stop < 2^w) :
    PreparedEmission ar D pp lp owner decl group pins pub data := by
  obtain ⟨dem,pk⟩ := native.demand ar controls decl.1 input D pp lp pins slotted data base P.pinFrame P.pointers
    P.rawStart P.rawEnd P.teams P.fields P.tailRoom ((Nat.le_add_right ..).trans rows) fit P.active P.processors
    P.literal P.tapeRoom P.substituteRoom P.placement P.destinations P.slabs
  have finalDem : DemandInput ar D pp lp owner pub data := by
    refine ⟨dem.ready,dem.records,dem.count,dem.raw,?_⟩
    intro i
    have bound := BankPlacement.populated_cell_lt P.placement P.destinations i
    simpa only [cells _ bound] using dem.cells i
  obtain ⟨ms,mc,scanner,bank,pair⟩ := sources
  let banks := ar.cellWriter (pub 0).val controls decl.1
  let pairs := ar.pairWriter (pub 0).val
  let emit := DataWriter.layout (readings pub) (readings data)
  have out : emit.output = ar.records := dem.records
  have count : emit.count = rawLen := dem.count.symm
  obtain ⟨ok,fields,_⟩ := ar.shared_emission pub mac reg team decl.1 (fun x => (group x).val) decl.2 ms mc data banks pairs
    scanner bank pair low axes rfl rfl cap fit out (count.symm ▸ rows)
  have continued := scanner.transfer axes low (out := readings (DataWriter.publish emit pub data))
    (fun x hx ne => public_image_word ar (readings ms) pub banks pairs emit mc data bank pair rfl rfl out x hx ne)
  have sy : SymbolFrame shared (readings (DataWriter.publish emit pub data)) ar.header.blocks ar.K ar.h decl group :=
    ⟨⟨rfl,rfl,rfl,continued.table,ar.rowSelectorBits_eq⟩,continued.owners⟩
  exact ⟨finalDem,pk,by simpa only [← count] using fields,by simpa only [← count] using ok,sy⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
