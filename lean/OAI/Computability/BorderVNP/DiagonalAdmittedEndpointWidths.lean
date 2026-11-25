import OAI.Computability.BorderVNP.DiagonalSharedDeclarationCapacity
import OAI.Computability.BorderVNP.RoutingISAScheduleClockFiniteIncidence

/-! # Actual source and receiver incidence of the admitted signed declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open RoutingISA RoutingISA.Evaluator.ScheduleClock RouteRecords TeamScales Finset
open private loads_owned from OAI.Computability.BorderVNP.CubeTeamRowClock

/-- The shared and received portions of every symbol fit the true native
load of its first-minimum team on any admitted declaration. -/
theorem declarationCapacity.incident_cap {n d R X blocks b K h : ℕ} {A Cell : Type*} [Fintype A]
    {decl : LengthDeclaration n d} {label : Cell → Label (n+1) d} {recv : A → Cell} {size : A → ℕ}
    (admitted : declarationCapacity R X blocks b K h decl label recv size) (u : Fin (R+1)) :
    let weight := declarationWeight blocks b K h decl label recv size
    let group := fun x : Fin d => TeamNative.owner R weight x.val
    (∑ x : Fin d, if group x=u then SharedRows.incident blocks K h decl x+
      incomingWidth label recv size decl.1 x else 0) ≤ X/256 := by
  intro weight group
  have loaded := admitted.1 u
  change TeamNative.loads R weight d u ≤ 1000000*X/256 at loaded
  rw [loads_owned,←Fin.sum_univ_eq_sum_range] at loaded
  have share : 1000000*(∑ x : Fin d, if group x=u then SharedRows.incident blocks K h decl x+
      incomingWidth label recv size decl.1 x else 0) ≤
      (∑ x : Fin d, if group x=u then weight x.val else 0) := by
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x _
    by_cases hit : group x=u
    · simp only [hit,ite_true,weight,declarationWeight,dite_eq_left x.isLt,GroupWeights.incidentWidth_eq_strict,
        TeamNative.scaledWeight]
      exact Nat.le_add_right _ _
    · simp [hit]
  have bound := share.trans loaded
  omega

/-- The published seven-word directory supplies the actual width and host of
each receiver. Its data and shared rows obey the incidence bound on every team,
including when both endpoints of a row are local. -/
theorem declarationCapacity.row_endpoints {n d R X blocks b K h cells : ℕ} {decl : LengthDeclaration n d}
    (dir : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (label : Fin cells → Label (n+1) d)
    (recv : Fin (dir.directory pp lp).length → Fin cells)
    (hosts : ∀ i, (recv i).val=(dir.directory pp lp)[i.val].cell)
    (admitted : declarationCapacity R X blocks b K h decl label recv (fun i => (dir.directory pp lp)[i.val].width))
    (processors : 0<dir.processors) (fields : 0<dir.fields) (two : dir.fields≤2) (block : 0<dir.block)
    (u : Fin (R+1)) :
    let data := dir.directory pp lp
    let weight := declarationWeight blocks b K h decl label recv (fun i => data[i.val].width)
    let group := fun x : Fin d => TeamNative.owner R weight x.val
    let owner := fun c : ℕ => if e : c<cells then group (label ⟨c,e⟩ decl.1) else 0
    let row := combinedRow data owner blocks K h decl group
    (∑ i ∈ range (data.length+d.choose 2), endpointWidth (row i) u.val) ≤
      3*dir.processors*dir.literal+X/256 := by
  intro data weight group owner row
  have same (i : Fin data.length) : owner data[i.val].cell=group (label (recv i) decl.1) := by
    rw [←hosts i]
    exact dite_eq_left (recv i).isLt
  have full := endpointWidths_le data owner blocks K h decl group (fun i => label (recv i) decl.1) same u
  have sent := dir.populated_outgoing pp lp u.val processors fields block
  have factor : (dir.fields+1)*(dir.processors*dir.literal) ≤ 3*dir.processors*dir.literal := by
    rw [Nat.mul_assoc 3]
    exact Nat.mul_le_mul_right _ (by omega)
  exact full.trans (Nat.add_le_add (sent.trans factor) (admitted.incident_cap u))

end Cube.Physical

end BorderVNP
end Computability
end OAI
