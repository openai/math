import OAI.Computability.BorderVNP.DiagonalSignedCommonPlacement
import OAI.Computability.BorderVNP.PackedNativeDemandPlacement

/-! # Moving the canonical signed setup to the same physical placement RAM -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing RoutingISA Directory CellAddresses CellAddressCircuit CellAddressPhysical

variable {D C ne np ns d k b w : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edges : N.Edge ↪ Fin ne) (ports : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
    (width : ∀ j,bits (live j)=dir.block) (aux : N.Site → ℕ) (ids : N.Site ↪ Fin ns)
    (F : Fields ns ne np C d k b σ) (x : σ → Bool)
    (net : Represents N cell aux ids edges ports F x) (code : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^b)
    (head origin : ℕ) (before after : ℕ → ℕ)

local notation3 (prettyPrint := false) "originals" => privatePair N cell edges ports dir old live gap
local notation3 (prettyPrint := false) "residents" => livePair N cell edges ports dir old live gap
local notation3 (prettyPrint := false) "tabs" => bases origin ne C dir.entries
local notation3 (prettyPrint := false) "pr" => privateLayout head origin ne C dir.entries dir.description gap
local notation3 (prettyPrint := false) "pp" => ISA.placement after (tabs).privatePairs
local notation3 (prettyPrint := false) "lp" => ISA.placement after (tabs).livePairs

include width net code wireFit in
/-- Every in-range private and live table entry has the same cell and displacement
on the physical placement return as on the canonical network representation. -/
theorem returned_key_placements (img : Image F (ids ∘ old) (ports ∘ live ∘ finProdFinEquiv.symm) x origin before)
    (run : (pr).Image before dir.entries after) (room : (pr).Fits w before) :
    ∀ j,dir.keyPlacement originals residents j=dir.keyPlacement pp lp j := by
  let actual := img.networkPlacement N cell aux ids edges ports F net code wireFit dir old live width
    head origin gap before after run room
  let reference := referenceBank N cell edges ports dir old live gap width
  intro j
  have eqn : actual.key j=reference.key j :=
    networkPlacement_key_reference N cell edges ports dir old live gap width aux ids F x net code wireFit
      head origin before after img run room j
  have value := actual.entry j
  rw [eqn] at value
  exact (reference.entry j).trans value.symm

end Packing.RoutingOutputs.NativeDemands

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM Packing Packing.Directory TeamContraction

/-- Reinterpret the emitted writer at another table with the same values at all
real destination keys, retaining its own embedding of supplied words. -/
noncomputable def SlottedWriter.withKeyPlacements {w base : ℕ} {ar : CubeArena.Layout} {D : Directory.Layout}
    {pp lp pp' lp' : ℕ → ℕ × ℕ} {pins : Pins.Layout} {pub : Arg → Word w} {mem : Memory w}
    {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {width : I → ℕ}
    (writer : SlottedWriter ar D pp lp pins pub mem base cell id width)
    (keys : ∀ k,D.keyPlacement pp lp k=D.keyPlacement pp' lp' k) :
    SlottedWriter ar D pp' lp' pins pub mem base cell id width :=
  writer.commonPlacement ⟨writer.placement.key,writer.placement.width_eq,fun k => (keys k).symm.trans (writer.placement.entry k)⟩
    (fun _ => rfl)

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
