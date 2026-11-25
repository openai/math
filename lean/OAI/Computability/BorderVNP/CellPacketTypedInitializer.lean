import OAI.Computability.BorderVNP.CellPacketInitializer
import OAI.Computability.BorderVNP.CellPacketSources

/-! # The placed cell's physical packet and original site tables -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM CellSparse CellSparse.Packet.Source

/-- Numerical source addresses and typed placed records of one private macro call. -/
structure Placed (Site : Type) where
  /-- Number of local private wires. -/
  privateWires : ℕ
  /-- Original and public box descriptions in ordinal order. -/
  boxes : List (Box Site)
  /-- Compact repetition and wiring records. -/
  rows : List Record
  /-- Address vectors for reported multiplicities. -/
  reports : List (List ℕ)
  /-- Physical address of the received one-copy description for each original site. -/
  slot : Site → ℕ
  /-- Public width of the private length header. -/
  headerWidth : ℕ
  /-- Original private factors and relative wire positions at a site. -/
  factors : Site → List Factor
  /-- First public geometry word consumed by this cell. -/
  publicBase : ℕ
  /-- First three-word source descriptor for this cell. -/
  descriptorBase : ℕ
  /-- First external input word. -/
  externalBase : ℕ
  /-- First unpacked scratch word. -/
  scratchBase : ℕ
  /-- First output burst word. -/
  burstBase : ℕ
  /-- External input bits in private stack order. -/
  external : List Bool

/-- The typed private directory determined by the one-copy descriptions and public schedule. -/
def Placed.directory {Site : Type} (p : Placed Site) : CellSparse.Directory :=
  ⟨p.boxes.map (CellSparse.Packet.Source.factors p.factors),p.rows,p.reports⟩

/-- Compact parts of the placed cell in generator order. -/
def Placed.parts {Site : Type} (p : Placed Site) : List (CellSparse.Packet.Source.Part Site) :=
  plan p.privateWires p.boxes p.rows p.reports

/-- The physical initializer reads public words contiguously and original boxes at
their delivery slot, independently of the copy counts in the private directory. -/
def Placed.task {Site : Type} (p : Placed Site) : Task where
  descriptorBase := p.descriptorBase
  externalBase := p.externalBase
  scratchBase := p.scratchBase
  burstBase := p.burstBase
  chunks := chunks p.slot p.headerWidth p.factors p.publicBase p.parts
  external := p.external

/-- The payload emitted for this placed cell is its actual sparse private generator input. -/
theorem Placed.payload {Site : Type} (p : Placed Site) :
    p.task.payload = CellSparse.Packet.input p.directory p.privateWires p.external := by
  have eq := packet_bits p.slot p.headerWidth p.factors p.privateWires p.boxes p.rows p.reports p.publicBase
  change RationalHitting.StackLanguage.codeWord _ ++ p.external = RationalHitting.StackLanguage.codeWord _ ++ _
  exact congrArg (fun xs => RationalHitting.StackLanguage.codeWord xs ++ p.external) eq

/-- Instantiate the actual initializer from its public memory image, private source
deliveries and local external assignment. The private generator data is produced by
the RAM program and is not part of the input memory conditions. -/
theorem Placed.initialize {Site : Type} {w : ℕ} (p : Placed Site)
    (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (regs : p.task.Registers s) (room : p.task.Room w) (description : ℕ)
    (rows : WordsAt (readings m) p.descriptorBase (descriptors p.task.chunks))
    (words : WordsAt (readings m) p.publicBase (p.parts.flatMap Part.publicBuffer))
    (sent : ∀ j, Part.original j ∈ p.parts → Delivered (description := description) (readings m)
      (p.slot j) p.headerWidth (p.factors j))
    (bodyRoom : ∀ j, p.headerWidth+(boxBody (p.factors j)).length ≤ description)
    (bodyFits : ∀ j, (boxBody (p.factors j)).length < 2^p.headerWidth)
    (external : CompactWrite.Source m p.externalBase p.external) :
    BoundedRun pub macros initializer s m (p.task.cost w) (fun z =>
      z.reg 5 = p.burstBase ∧
      z.reg 15 = (CompactFrame.pack w (CellSparse.Packet.input p.directory p.privateWires p.external)).length ∧
      z.mem = readings (p.task.image m)) := by
  have input : p.task.Stored m :=
    ⟨rows,chunks_stored (readings m) p.slot p.headerWidth p.factors p.parts p.publicBase sent bodyRoom bodyFits words,
      external⟩
  apply (initializer_run pub macros p.task s m regs input room).mono le_rfl
  rintro z ⟨base,count,mem⟩
  exact ⟨base,by simpa only [Task.burst,p.payload] using count,mem⟩

/-- At the returned address and count, the original opaque tables occur in the exact
private-program packet read by the finite-width native call instruction. -/
theorem Placed.previous {Site : Type} {w : ℕ} (p : Placed Site) {s : Bank w} {m m' : Memory w}
    (base : readings s 5 = p.burstBase)
    (count : readings s 15 = (CompactFrame.pack w (CellSparse.Packet.input p.directory p.privateWires p.external)).length)
    (mem : readings m' = readings (p.task.image m)) :
    TeamRAM.previous m' (.burst (s 5).val (s 15).val) =
      CompactFrame.pack w (CellSparse.Packet.input p.directory p.privateWires p.external) := by
  have eq : p.task.burst w = _ := congrArg (CompactFrame.pack w) p.payload
  rw [←eq]
  exact initializer_burst p.task base (count.trans (congrArg List.length eq.symm)) mem

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
