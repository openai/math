import OAI.Computability.BorderVNP.DiagonalBootedGeometryProfile
import OAI.Computability.BorderVNP.CellPacketGeometryNativePlaces
import OAI.Computability.BorderVNP.FiniteEvaluatorReturnedTerminalOperands
import OAI.Computability.BorderVNP.PackedFinalCellFields
import OAI.Computability.BorderVNP.PackedCellAddressRead

/-! # Native private widths at the published marker ranges of the genuine geometry return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Pins
open RoutingISA.CompactMachine PackedHistoryCircuit DiagonalResidueRAM CellMacro.Generator BorderVNP.Cube.Tally

variable {R r t d link inner n w : ℕ} {Edge : Type} {gen : Fragment IO}
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {regs : Fin (R+1) → RoutingISA.Bank w} {args : Fin (R+1) → UnitAddresses}
    {live : Fin d → Bool} {wire : Exterior R r link → Bool} {u : Fin (R+1)}
    (B : BootedPinStart gen G pub regs args live wire u)
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
local notation3 (prettyPrint := false) "installed" => install gen n mac
local notation3 (prettyPrint := false) "L" => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "f" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "F" => G.processorFields u live wire (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "initial" => processorMemory F w

open Crossing Packing Packing.Inherited Packing.CellAddresses CellPacketGeometry CellPacketGeometry.History.Native
open CellSparse CellSparse.Packet CellSparse.Packet.Source RoutingISA.CellPacket

variable {D C a p chunk at₀ hdr : ℕ} {O E P : Type} {bits : P → ℕ}
    (dir : SiteWords.Directory (Fin a) O (C+1)) (ptr : O → E) (arg : E → ℕ)
    (slot : O → ℕ) (fs : O → List Factor)
    (ext scratch burst : Fin (C+1) → ℕ) (external : Fin (C+1) → List Bool)
    (N : Network D P bits) (cell : N.Site → ℕ) (state : N.Site → Site)

/-- Apply the chosen packet theorem's returned-cell fields to the memory
of this exact reconstruct path. The physical arrays retain their marker
ranges, descriptor contents, and starting wire of each external field. -/
theorem BootedPinStart.publishedPrivateWidths {o time dest : ℕ} {ok : Prop} {words : Fin o → ℕ}
    {resident : (Fin (L).guessWidth → Bool) → Memory w → Prop}
    (paths : ProfilePaths (withStartup pinGeometry) (L).guessWidth (pub u) installed (regs u) initial ok
      time dest words resident)
    (address : ∀ j, arg (ptr j)=slot j)
    (all : ∀ ret : Returns (withStartup pinGeometry) (pub u) installed (regs u) initial,
      Published dir p chunk at₀ hdr ptr arg (readings ret.val.2.2) ∧
        ∀ c : Fin C, dir.privateWires c.castSucc=FinalCell.privateBits N cell state c.val)
    (g : Fin (L).guessWidth → Bool)
    (geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2) :
    let ram := readings geo.val.2.2
    resident g geo.val.2.2 ∧ B.used+traceCost (B.pins g).val.1+traceCost geo.val.1≤time ∧
    Published dir p chunk at₀ hdr ptr arg ram ∧
    ∃ fit : C+1+dir.words.length+(C+1)≤2^p,
    ∃ space : C+1+(Schema.coords (dir.referenceRows ptr).length).length+(C+1)≤2^chunk,
      let cells := atRanges (dest:=at₀) (H:=hdr) dir ptr fit space ram slot fs ext scratch burst external
      TypedBatch.SourceShape cells dir ∧
      (∀ c, CellMemory (cells c) ((cells c).publicBase+((Supplement.prefixParts (cells c)).flatMap Part.publicBuffer).length)
        (descriptorBank at₀ p+ram (descriptorBank at₀ p+(2^chunk+(Markers.stop space c).val))) ram) ∧
      ∀ c : Fin C, (Terminal.placeAt cells c.val).privateWires=externalBase N cell c.val (fun v => (state v).size) := by
  intro ram
  obtain ⟨⟨published,width⟩,kept,clock,_⟩ := B.allReturns_on_pin paths
    (fun _ m => Published dir p chunk at₀ hdr ptr arg (readings m) ∧
      ∀ c : Fin C, dir.privateWires c.castSucc=FinalCell.privateBits N cell state c.val) all g geo
  obtain ⟨fit,space,shape,read⟩ := published.places dir ptr ram slot fs ext scratch burst external address
  refine ⟨kept,clock,published,fit,space,shape,read,?_⟩
  intro c
  let places := atRanges (dest:=at₀) (H:=hdr) dir ptr fit space ram slot fs ext scratch burst external
  have ordinal : Terminal.placeAt places c.val=places c.castSucc :=
    congrArg places (Fin.ext (Nat.min_eq_left c.isLt.le))
  exact (congrArg Placed.privateWires ordinal).trans ((shape.privateWires c.castSucc).trans (width c))

/-- The true packet at each real cell ordinal has the private width, output
addresses and native instruction directory of the corresponding final cell. -/
theorem BootedPinStart.publishedCellFields {o time dest : ℕ} {ok : Prop} {words : Fin o → ℕ}
    {resident : (Fin (L).guessWidth → Bool) → Memory w → Prop}
    (paths : ProfilePaths (withStartup pinGeometry) (L).guessWidth (pub u) installed (regs u) initial ok
      time dest words resident)
    (address : ∀ j, arg (ptr j)=slot j)
    (reports : Fin C → List (List ℕ)) (directories : Fin C → CellSparse.Directory)
    (all : ∀ ret : Returns (withStartup pinGeometry) (pub u) installed (regs u) initial,
      Published dir p chunk at₀ hdr ptr arg (readings ret.val.2.2) ∧
        ∀ c : Fin C,
          (dir.privateWires c.castSucc=FinalCell.privateBits N cell state c.val ∧ dir.reports c.castSucc=reports c) ∧
            ∀ s pb db eb sc bu bytes,
              (dir.placed c.castSucc hdr s fs pb db eb sc bu bytes).directory=directories c)
    (g : Fin (L).guessWidth → Bool)
    (geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2) :
    let ram := readings geo.val.2.2
    resident g geo.val.2.2 ∧ B.used+traceCost (B.pins g).val.1+traceCost geo.val.1≤time ∧
    Published dir p chunk at₀ hdr ptr arg ram ∧
    ∃ fit : C+1+dir.words.length+(C+1)≤2^p,
    ∃ space : C+1+(Schema.coords (dir.referenceRows ptr).length).length+(C+1)≤2^chunk,
      let cells := atRanges (dest:=at₀) (H:=hdr) dir ptr fit space ram slot fs ext scratch burst external
      TypedBatch.SourceShape cells dir ∧
      (∀ c, CellMemory (cells c) ((cells c).publicBase+((Supplement.prefixParts (cells c)).flatMap Part.publicBuffer).length)
        (descriptorBank at₀ p+ram (descriptorBank at₀ p+(2^chunk+(Markers.stop space c).val))) ram) ∧
      ∀ c : Fin C,
        (Terminal.placeAt cells c.val).privateWires=externalBase N cell c.val (fun v => (state v).size) ∧
        (Terminal.placeAt cells c.val).reports=reports c ∧ (Terminal.placeAt cells c.val).directory=directories c := by
  intro ram
  obtain ⟨kept,clock,published,fit,space,shape,read,width⟩ :=
    B.publishedPrivateWidths dir ptr arg slot fs ext scratch burst external N cell state paths address
      (fun ret => ⟨(all ret).1,fun c => ((all ret).2 c).1.1⟩) g geo
  obtain ⟨ret,_⟩ := B.fullGeometryReturn g geo
  refine ⟨kept,clock,published,fit,space,shape,read,?_⟩
  intro c
  let places := atRanges (dest:=at₀) (H:=hdr) dir ptr fit space ram slot fs ext scratch burst external
  have ordinal : Terminal.placeAt places c.val=places c.castSucc :=
    congrArg places (Fin.ext (Nat.min_eq_left c.isLt.le))
  obtain ⟨⟨_,report⟩,source⟩ := (all ret).2 c
  refine ⟨width c,(congrArg Placed.reports ordinal).trans ((shape.reports c.castSucc).trans report),?_⟩
  exact (congrArg Placed.directory ordinal).trans (source slot _ _ _ _ _ _)

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
