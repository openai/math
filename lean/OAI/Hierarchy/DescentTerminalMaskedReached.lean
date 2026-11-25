import OAI.Hierarchy.DescentTerminalMaskedCohorts
import OAI.Hierarchy.DescentTerminalResidentRank

namespace OAI
/-! # The actual terminal graph's local scalar ordinal in the measured sparse population -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentColonies DescentTerminalGraphPositions DescentTerminalCableOrder DescentPackedLocalAtoms
open Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist p : ℕ}
    (R:Reached W G price ε S k age z degree wire hist) (L : Order W.graph (S.hostSize age) p)
    (same : L.home=R.home)
local notation "C" => S.groupCount age*2^k
def chart (i : Fin (S.hostSize age)) : L.Nodes i↪Fin C :=
  (R.homeFiber L same i).trans (R.calendar i)
def rawResident (i : Fin (S.hostSize age)) (j : Fin (Fintype.card (L.Nodes i))) : Fin C :=
  chart R L same i ((L.nodes i).symm j)

omit [Fintype P] in
theorem raw_rank (ranks : ∀u,L.nodeRank u=(R.placement.site R.vertex R.valid.coordinates u).val) (i : Fin (S.hostSize age))
    (mask : Fin C→Word 1) (live : ∀c,mask c≠0 ↔ ∃u,chart R L same i u=c) (v : Fin (Fintype.card (L.Nodes i))) :
    mask (rawResident R L same i v)≠0 ∧ earlier mask (rawResident R L same i v)=v.val := by
  let u:=(L.nodes i).symm v
  have actual:=R.rank_read L same ranks i u
  have hmask:=mask_prefix (chart R L same i) (fun c=>decide (mask c≠0)) (by simpa using live) u
  have comb : ((L.nodes i) u).val=(Finset.univ.filter (fun c=>mask c≠0 ∧ c<chart R L same i u)).card := by
    exact actual.trans (by simpa [chart] using hmask)
  refine ⟨(live _).mpr ⟨u,rfl⟩,?_⟩
  simpa [earlier,present,Finset.filter_filter,rawResident,u] using comb.symm

end
end Hierarchy.DescentSixParty.Reached

end OAI
