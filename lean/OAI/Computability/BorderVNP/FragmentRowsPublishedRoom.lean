import OAI.Computability.BorderVNP.FragmentRowsArenaBounds

/-! # Native fragment allocation from the genuine routing and cell publications

The raw delivery scan uses the compacted rows at the reserved base. The
geometry supplies the cable endpoint ordinals and all cell lengths. The
cube's cell-bank writer supplies the physical pointers. Every output then
fits under the one signed-task word bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open BorderVNP.Cube Packing Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open DiagonalTallyAllocation DiagonalResidueRAM GeometryAdvice

/-- The final signed high-water word bounds the whole sparse fragment arena. -/
theorem fragment_limit_le (a : SignedTaskArena.Layout) (w u v k : ℕ) :
    a.fragments.limit ≤ a.endAddress w u v k := by
  have pre : a.fragments.limit ≤ a.before.limit := by
    rw [a.before.footprint]; change a.before.start ≤ _; omega
  have middle : a.before.limit ≤ a.after.start := by
    change a.before.limit ≤ a.before.limit+3*a.cube.cells+7*a.cube.cells+
      a.p.scratchStride*a.cube.cells+a.p.burstStride*a.cube.cells
    omega
  have upper : a.after.start ≤ a.after.localBase := by
    rw [AfterTasks.localBase,a.after.footprint]; omega
  exact (pre.trans (middle.trans upper)).trans (by
    dsimp only [SignedTaskArena.Layout.endAddress,SignedTaskArena.Layout.entry,gateBase,
      SignedTaskArena.Layout.valuation,SignedTaskArena.Layout.tallyBits]; omega)

variable {w head J A s n d k D : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (a : SignedTaskArena.Layout) (N : Network D P bits) (cell : N.Site → Fin a.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin a.cube.cables) (portID : P ↪ Fin n)
    (F : Fields s a.cube.cables n a.cube.cells d k w σ) {x : σ → Bool}
    {old : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val = c.val)
    (fits : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (stride : ∀ c, suppliedSize N cell c ≤ a.cube.cellStride)
    (dir : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (raw profile gates words width W tail : ℕ)

local notation "firstFree" => raw+7*dir.candidates
local notation "origin" => Allocation.dest firstFree profile gates words width
local notation "geoEnd" => Allocation.stop firstFree profile gates words width W
local notation "control" => controlsBase origin a.cube.cables a.cube.cells J A

include rep codes fits stride
set_option maxHeartbeats 700000 in
/-- The actual preserved native routing and bank images discharge all
range and data-dependent source conditions for the fragment ISA program. -/
theorem fits_of_publication {geo input scheduled written mem : ℕ → ℕ} {readerIn readerGuess readerGates teams : ℕ}
    (word : a.endAddress W readerIn readerGuess readerGates < 2^W) (cube : a.cube.header.header = geoEnd)
    (complete : a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells J A+
      ((a.cube.cells+(J+a.cube.cells))+(37+tail))) ≤ words)
    (header : RoutingOutputs.Header head origin a.cube.cables a.cube.cells J mem)
    (ctrl : mem (head+92)=control) (ctrl28 : mem (control+28)=a.controls 28)
    (base : head+112 ≤ raw) (rawAt : mem (head+8)=raw)
    (count : mem (head+9)=(dir.directory pp lp).length) (capacity : (dir.directory pp lp).length ≤ a.cube.maxRows)
    (host : mem (head+72)=a.cube.hostDirectory)
    (image : RoutingOutputs.Image F old ports x origin geo)
    (keep : ∀ z, origin ≤ z → z<origin+5*a.cube.cables+a.cube.cells → mem z=geo z)
    (axis : Fin (a.cube.n+1)) (assigned : CubeArena.DirectoryImage a.cube head control axis teams input scheduled written)
    (banks : ∀ c<a.cube.cells, mem (a.cube.hostDirectory+c*2+1) = written (a.cube.hostDirectory+c*2+1))
    (endpoints : LabelIndex.Endpoints (LabelIndex.layout head mem) mem) :
    (Layout.fromFrame head mem).Fits W mem := by
  have dataRoom := dir.directory_length_le pp lp
  have rawOrigin : firstFree ≤ origin := by dsimp only [Allocation.dest,Allocation.temp]; omega
  have limit := (fragment_limit_le a W readerIn readerGuess readerGates).trans_lt word
  have geometry := controls_before_header (fresh:=firstFree) (u:=profile) (k:=gates) (b:=width) (w:=W) complete
  have cable := FiniteEvaluator.CubeAllocation.host_ends_positive a.cube head mem N cell aux siteID edgeID portID F
    rep codes fits stride header image (fun z h₁ h₂ => keep z h₁ (by omega))
  apply fits_in_arena a mem header ctrl (ctrl ▸ ctrl28) host (by omega) (by rw [rawAt,count]; omega)
    (cube ▸ geometry) limit (count ▸ capacity) cable endpoints
  · intro i hi
    let j : Fin a.cube.cells := ⟨i,hi⟩
    have rel := header.ends
    have ctr := header.edges
    change mem (mem (head+87)+2*mem (head+7)+i) ≤ a.cube.cellStride
    rw [rel,ctr]
    have addr : (bases origin a.cube.cables a.cube.cells J).ends+2*a.cube.cables+i =
      (bases origin a.cube.cables a.cube.cells J).supplied+i := by dsimp only [bases]; omega
    rw [addr,keep _ (by dsimp only [bases]; omega) (by dsimp only [bases]; omega)]
    exact ((image.suppliedAt j).trans (SuppliedOffsets.cell_size N cell aux siteID edgeID portID F rep fits j)).le.trans (stride j)
  · intro c hc
    rw [Nat.mul_comm 2 c,banks c hc]
    exact (assigned.hostRows c hc).2

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
