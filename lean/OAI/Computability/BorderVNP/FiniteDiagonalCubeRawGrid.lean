import OAI.Computability.BorderVNP.FiniteDiagonalCubeRawTapes
import OAI.Computability.BorderVNP.FiniteDiagonalCubeGrid
import OAI.Computability.BorderVNP.CubePhysicalGreedyTally

/-! # The field diagonal sum on the physical evaluator's complete raw choices

The owner schedule for a profile depends on the minimum cut of its selected
packets, the actual incoming data, and their public product labels. Each
term retains its own routed payloads and all bits of each cell's flat private
vector, before filtering any checks or combining any signs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] {T : N.Tables F}

/-- The public numbered site rows and the incoming deliveries used by the
actual greedy assignment of groups to teams. -/
structure FieldRawLayout (L : FieldPacketPlan N F) (S : FieldSiteDirectory N T) where
  /-- Number of site slots in the public frame. -/
  sites : ℕ
  /-- Real public ordering of the inherited work regions. -/
  siteID : N.Site ↪ Fin sites
  /-- The operands delivered to cells after the incoming index checks. -/
  Operand : Type
  finiteOperand : Fintype Operand
  /-- The cell receiving each operand. -/
  recv : Operand → L.Cell
  /-- Number of incoming bits for each delivered operand. -/
  dataWidth : Operand → ℕ

attribute [instance] FieldRawLayout.finiteOperand

namespace FieldRawLayout

variable {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T} (V : FieldRawLayout L S)

/-- Team owner computed by the real first-minimum-cut and greedy group schedule. -/
def owners (R : ℕ) (select : Packet L.dimension L.alphabet L.blocks → Selector L.dimension L.alternatives L.copies) :
    Fin L.alphabet → Fin (R+1) :=
  greedyOwner R L.bitWidth L.supply L.label V.recv V.dataWidth select

/-- Raw routed payload choices and the complete private wire and work bits. -/
abbrev Raw (R : ℕ) := S.RoutedRaw L (V.owners R)

/-- Each full raw choice array reconstructs its work bits and physical cube assignment. -/
noncomputable def read (R : ℕ) : V.Raw R ≃ (S.Work × L.Path) :=
  S.routedRawEquiv L V.siteID (V.owners R)

end FieldRawLayout
end FiniteDiagonal

namespace FinitePrewire

open Crossing Packing ParseBatch.Prewire TeamContraction FieldTeam FiniteDiagonal
open scoped BigOperators Classical

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

variable {D R r t d link inner n b K h : ℕ} {Edge : Type} [Fintype Edge]
  {F : Type*} [Field F] [Fintype F]
  (G : Wiring R r t d link inner n Edge)
  (teams : PackPorts Unit b K h ≃ Fin (R+1))
  (H : ProfileSum (ValuedPack F D (packWidth (fun _ : Fin r × Fin (publicWidth G) => 1) b K h)))
  (plans : ∀ i : H.Index, FieldPacketPlan (H.term i).1 F)
  (dirs : ∀ i : H.Index, FieldSiteDirectory (H.term i).1 (H.term i).2)
  (frames : ∀ i : H.Index, FieldRawLayout (plans i) (dirs i))

/-- Each complete raw term has one exterior assignment, one adaptive history
and the data choices of that history's real cell and cube layout. -/
abbrev GridRawTerm (R r link : ℕ) {P : Type} [Fintype P] {bits : P → ℕ}
    (H : ProfileSum (ValuedPack F D bits)) (plans : ∀ i : H.Index, FieldPacketPlan (H.term i).1 F)
    (dirs : ∀ i : H.Index, FieldSiteDirectory (H.term i).1 (H.term i).2)
    (frames : ∀ i : H.Index, FieldRawLayout (plans i) (dirs i)) :=
  (Exterior R r link → Bool) × (i : H.Index) × (frames i).Raw R

/-- Product of every scalar/sign observation and every selected cube vertex on these literal bits. -/
noncomputable def rawValue (pin : Fin d → Bool) (raw : GridRawTerm R r link H plans dirs frames) : F :=
  let i := raw.2.1
  let a := (frames i).read R raw.2.2
  (dirs i).pathValue (plans i) (historyPorts G teams pin raw.1) a.2 a.1

omit [Fintype Edge] [Fintype F] in
/-- Summing all raw private bits contracts the real sparse tables at the
independently opened host ends, then sums the ordinary cube expansion. -/
theorem sum_rawValue (pin : Fin d → Bool) :
    (∑ raw : GridRawTerm R r link H plans dirs frames, rawValue G teams H plans dirs frames pin raw) =
      ∑ a : GridAssignedTerm R r link H, gridAssignedWeight G teams H pin a := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  refine Finset.sum_congr (Finset.ext fun _ => by simp) fun ext _ => ?_
  rw [Fintype.sum_sigma,Fintype.sum_sigma]
  refine Finset.sum_congr (Finset.ext fun _ => by simp) fun i _ => ?_
  exact ((dirs i).value_eq_raw_sum (plans i) (frames i).siteID ((frames i).owners R)
    (historyPorts G teams pin ext)).symm

/-- The substituted tensor is the field sum on the actual layout's raw
assignments, including the complete, possibly nondeterministic private tapes. -/
theorem field_contraction_eq_raw_values
    (B : ValuedPack F D (fun _ : Fin r × Fin (publicWidth G) => 1)) (pin : Fin d → Bool)
    (computes : ∀ ext team, B.tensor (fun p _ => publicBits G team pin ext p) = fieldValue G F pin ext team)
    (expand : ∀ ports, (unshortened B b K h).tensor ports = ∑ i, (H.term i).tensor ports) :
    fieldContraction G F pin = ∑ raw : GridRawTerm R r link H plans dirs frames,
      rawValue G teams H plans dirs frames pin raw :=
  (field_contraction_eq_grid_assignments G teams H B pin computes expand).trans
    (sum_rawValue G teams H plans dirs frames pin).symm

end FinitePrewire

end BorderVNP
end Computability
end OAI
