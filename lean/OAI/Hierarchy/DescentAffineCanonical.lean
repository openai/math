import OAI.Hierarchy.DescentAffineColors
import OAI.Hierarchy.DescentSparseStep

namespace OAI
/-! # The first affine color on the actual occupied colonies -/

namespace Hierarchy.DescentAffineColors

@[simp] theorem code_linear_offset {k : ℕ} (j : Candidate k) : code (linear j) (offset j)=j := by
  simp [code,linear,offset,Fin.snoc_init_self]

end Hierarchy.DescentAffineColors

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentWalshTables DescentAffineColors
open scoped BigOperators Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {k d : ℕ} {P : Type*} {bits : P→ℕ}
variable (N : Network d P bits) (core : Finset N.Edge) (position : N.Site→V)
variable (block : N.Site→Block k) (full : N.Site→ℕ) (near : V→Finset V) (D a B unit : ℕ)
variable (small : ∀ (v : V) (x : Block k), blockMass N position block full v x ≤ unit * B)
local notation "home" => occupiedHome N position block full near D a (unit*B) small
local notation "Col" => occupied N (unit*B) near D a (blockMass N position block full) small position block
local notation "traffic" => nativeTraffic N core home

def affineDirectory : Fin (Fintype.card Col) → Block k → ℕ := fun t x =>
  DescentPacking.slab (live traffic) (fun u => (address k).symm (block u))
    (groupStream home ((Fintype.equivFin Col).symm t)) ((address k).symm x)

/-- Ties are resolved by ascending unsigned affine code, as in the native scan. -/
def FirstPaint (j : Candidate k) : Prop :=
  let rows := affineDirectory N core position block full near D a B unit small
  (scanMinimum (scoreAt rows) (List.range (2^(k+1)))).1=some (j.val,score rows j)

omit [Fintype V] in
theorem firstPaint_unique {j u : Candidate k}
    (left : FirstPaint N core position block full near D a B unit small j)
    (right : FirstPaint N core position block full near D a B unit small u) : j=u := by
  unfold FirstPaint at left right
  exact Fin.ext (congrArg Prod.fst (Option.some.inj (left.symm.trans right)))

omit [Fintype V] in
/-- The true ordered minimizer satisfies the square-root bound on the occupied population. -/
theorem first_paint (hu : 0<unit) (covered : ∀v,unit*live traffic v≤full v) :
    ∃ j : Candidate k, FirstPaint N core position block full near D a B unit small j ∧
      affineBalance N core position block full near D a B unit small (linear j) (offset j) := by
  let rows := affineDirectory N core position block full near D a B unit small
  let weight := fun (c : Col) i => DescentPacking.slab (live traffic)
    (fun u => (address k).symm (block u)) (groupStream home c) i
  let names := Fintype.equivFin Col
  obtain ⟨j,selected,best⟩ := DescentAffineColors.first rows
  refine ⟨j,selected,?_⟩
  refine occupied_bound rows names.toEmbedding weight ?_ ?_ B ?_ j best
  · intro c i
    simp [rows,affineDirectory,names,weight]
  · intro x outside
    exact (outside (names.surjective x)).elim
  · exact actual_slab_cap N core position block full near D a B unit small hu covered


end
end Hierarchy.DescentSixParty.StarKeys

end OAI
