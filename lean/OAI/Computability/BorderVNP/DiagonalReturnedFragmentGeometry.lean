import OAI.Computability.BorderVNP.DiagonalSignedFragmentPublication
import OAI.Computability.BorderVNP.DiagonalPublishedHostCables

/-! # Cable, supply and bank addresses in the returned signed report memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM BorderVNP.Cube Crossing Packing CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open FiniteEvaluator Diagonal.ExternalSew.Fragments

variable {dim sites np cb lb b w frame origin raw gap : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (a : Layout) (N : Network dim P bits) (cell : N.Site → Fin a.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin a.cube.cables) (portID : P ↪ Fin np)
    (F : Fields sites a.cube.cables np a.cube.cells cb lb b σ) {x : σ → Bool}
    (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) {geom placed : Memory w} {out written : ℕ → ℕ}
    {old : Fin D.entries → Fin sites} {ports : Fin (D.teams*D.sites) → Fin np} {signed : Bool}
local notation3 (prettyPrint := false) "initial" => readings (Directory.ISA.publish placed frame raw (D.directory pp lp))
local notation3 (prettyPrint := false) "tables" => bases origin a.cube.cables a.cube.cells D.entries
local notation3 (prettyPrint := false) "fields" => FragmentRows.Layout.fromFrame frame out

/-- The compacted publication survives the native signed report: both
cable passes use the original edge offsets, each cell's supply count
is the true network size, and every host pointer is the assigned bank. -/
theorem ReportWords.returnedGeometry (h : ReportWords a frame initial written out signed)
    (rep : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (image : Image F old ports x origin (readings geom))
    (placedAt : (privateLayout frame origin a.cube.cables a.cube.cells D.entries D.description gap).Image
      (readings geom) D.entries (readings placed))
    (first : frame+112 ≤ raw) (space : raw+7*D.candidates ≤ origin)
    (stop : origin+5*a.cube.cables+a.cube.cells ≤ a.cube.header.header)
    (header : Header frame origin a.cube.cables a.cube.cells D.entries initial)
    (host : initial (frame+72)=a.cube.hostDirectory)
    {ctl teams : ℕ} {chosen : Fin (a.cube.n+1)} {input scheduled : ℕ → ℕ}
    (assigned : CubeArena.DirectoryImage a.cube frame ctl chosen teams input scheduled written) :
    CableRows N cell edgeID portID (fields).host out ∧
    (∀ c : Fin a.cube.cells, out ((fields).supplied+c.val)=suppliedSize N cell c) ∧
    ∀ c : Fin a.cube.cells, out ((fields).host.cells+2*c.val+1)=a.cube.cellBank+c.val*a.cube.cellStride := by
  have kept (z : ℕ) (lo : origin≤z) (hi : z<origin+5*a.cube.cables+a.cube.cells) :
      out z=readings geom z := (h.geometry z (by omega) (by omega)).trans
        (published_geometry pp lp placedAt first space z lo (by dsimp only [bases]; omega))
  have edges : out (frame+7)=a.cube.cables :=
    (h.frame_word 7 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)).trans header.edges
  have ends : out (frame+87)=(tables).ends :=
    (h.frame_word 87 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)).trans header.ends
  have start : out (frame+6)=origin :=
    (h.frame_word 6 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)).trans header.cables
  refine ⟨CableRows.ofImage N cell edgeID portID _ _ aux siteID F rep ids fit image start ends edges
    (fun z lo hi => kept z lo (by omega)),?_,?_⟩
  · intro c
    change out (out (frame+87)+2*out (frame+7)+c.val)=_
    rw [ends,edges]
    have addr : (tables).ends+2*a.cube.cables+c.val=(tables).supplied+c.val := by dsimp only [bases]; omega
    rw [addr,kept _ (by dsimp only [bases]; omega) (by have := c.isLt; dsimp only [bases]; omega)]
    exact (image.suppliedAt c).trans (SuppliedOffsets.cell_size N cell aux siteID edgeID portID F rep fit c)
  · intro c
    change out (out (frame+72)+2*c.val+1)=_
    rw [(h.frame_word 72 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)).trans host,
      Nat.mul_comm 2 c.val,h.banks c.val c.isLt]
    exact (assigned.hostRows c.val c.isLt).2

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
