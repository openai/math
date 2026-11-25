import OAI.Computability.BorderVNP.FragmentDirectoryInputArena

/-! # The argument clock input of a genuine routing geometry publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Packing Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open GeometryAdvice

variable {W w J A s n d k D : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (pub : Arg → Word W) (m : Memory W)
    (a : SignedTaskArena.Layout) (N : Network D P bits) (cell : N.Site → Fin a.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cube.cables) (portID : P ↪ Fin n)
    (F : Fields s a.cube.cables n a.cube.cells d k w σ) {x : σ → Bool}
    {old : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fits : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (stride : ∀ c, suppliedSize N cell c ≤ a.cube.cellStride)
    (dir : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (raw profile gates words width tail : ℕ)

local notation "head" => readings pub 0
local notation "mem" => readings m
local notation "firstFree" => raw+7*dir.candidates
local notation "origin" => Allocation.dest firstFree profile gates words width
local notation "geoEnd" => Allocation.stop firstFree profile gates words width W
local notation "ctl" => controlsBase origin a.cube.cables a.cube.cells J A

include rep codes fits stride in
/-- The geometric representation, preserved native output columns and published
cell banks determine the entire argument-stage fragment input at the current
physical memory. Its dynamic row count comes from the compacted directory. -/
noncomputable def FragmentDirectoryInput.ofPublication {geo input scheduled written : ℕ → ℕ}
    {readerIn readerGuess readerGates teams : ℕ} (high : a.endAddress W readerIn readerGuess readerGates < 2^W)
    (cube : a.cube.header.header=geoEnd)
    (complete : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells J A+
      ((a.cube.cells+(J+a.cube.cells))+(37+tail))) ≤ words)
    (header : Header head origin a.cube.cables a.cube.cells J mem)
    (ctrl : mem (head+92)=ctl) (controls : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (base : head+112 ≤ raw) (rawAt : mem (head+8)=raw)
    (count : mem (head+9)=(dir.directory pp lp).length) (capacity : (dir.directory pp lp).length ≤ a.cube.maxRows)
    (host : mem (head+72)=a.cube.hostDirectory) (image : RoutingOutputs.Image F old ports x origin geo)
    (keep : ∀ z, origin ≤ z → z<origin+5*a.cube.cables+a.cube.cells → mem z=geo z)
    (axis : Fin (a.cube.n+1)) (assigned : CubeArena.DirectoryImage a.cube head ctl axis teams input scheduled written)
    (banks : ∀ c<a.cube.cells, mem (a.cube.hostDirectory+c*2+1) = written (a.cube.hostDirectory+c*2+1))
    (endpoints : LabelIndex.Endpoints (LabelIndex.layout head mem) mem) : FragmentDirectoryInput pub m := by
  have fitting := FragmentRows.fits_of_publication a N cell aux siteID edgeID portID F rep codes fits stride dir pp lp
    raw profile gates words width W tail high cube complete header ctrl (controls ⟨28,by decide⟩) base rawAt count
    capacity host image keep axis assigned banks endpoints
  have low : head+112 ≤ ctl := by
    dsimp only [controlsBase,bases,Allocation.dest,Allocation.temp]
    omega
  have geom := FragmentRows.controls_before_header (fresh := firstFree) (u := profile) (k := gates) (b := width) (w := W) complete
  have within : ctl+37 ≤ a.cube.header.header := cube ▸ geom
  have before := within.trans (FragmentRows.arena_order a).1
  exact ofArena pub m a fitting ctrl controls low before header.edges (count ▸ capacity) header.cells high

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
