import OAI.Computability.BorderVNP.PackedFinalCellObservationTail
import OAI.Computability.BorderVNP.CubePhysicalRetainedBottom

/-! # A placed guard recovers the birth work and the true incident words

The actual sparse row group contains the terminal site's translated records
and the final cable and port ties. At a fixed cell bank, its checked observations
recover the original site's work and every forced retained and incident lane.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Placement

open Crossing CellAddresses CellSparse
open scoped Classical
open private site_checked from OAI.Computability.BorderVNP.PackedFinalCellObservationTail

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits' : P → ℕ}
variable (N : Network D P bits') {Cell : Type} (cell : N.Site → Cell) (c : Cell)
variable (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M) (portID : P ↪ Fin np)
variable (state : Site.Programs N)
private abbrev prog := fun v : N.Site => (state v).program
private abbrev sizes := fun v : N.Site => (state v).program.size

/-- A site's successful placed rows are equivalent to one birth work vector,
with the same observation list, whose forced extension and true local input
exactly occupy this site's slice of the original guessed cell bank. -/
theorem checked_site_birth_iff (g : Fin (guessedSize N cell c) → Bool)
    (a : Fin (siteSize N cell c (sizes N state)) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (merged : List (List Factor)) (base : N.Site → ℕ) (v : {v : N.Site // cell v=c})
    (loc : (state v.val).birth.Local) (schema : (state v.val).program.Schema)
    (span : base v.val+(state v.val).program.boxes.length ≤ merged.length)
    (get : ∀ j < (state v.val).program.boxes.length, merged.getD (base v.val+j) [] = (state v.val).program.boxes.getD j [])
    (relative : (state v.val).program.RelativeBoxes) (os : List (Bool × Option ℕ)) :
    let L := state v.val
    let inputs := canonical N cell c edgeID portID v g x ∘ Fin.cast L.size
    let z := siteWords N cell c siteID (sizes N state) a v
    let dir := (⟨merged,siteRows N cell c siteID edgeID portID (prog N state) base v,[]⟩ : Directory)
    dir.guardedObservations (lookup (bank N cell c (sizes N state) g a x)) = some os ↔
      ∃ orig : Fin L.birth.work → Bool, L.birth.observe (bits orig (L.retention.readInput inputs)) = some os ∧
        z = Fin.append (L.retention.complete inputs orig) inputs := by
  intro L inputs z dir
  let program := prog N state
  let s := L.program
  let mem := lookup (bank N cell c (sizes N state) g a x)
  let shift := siteBase N cell c siteID (sizes N state) v
  let work : Fin s.work → Bool := fun j => z (Fin.castAdd s.incoming j)
  have tiesSpec : (∀ r ∈ ties N cell c siteID edgeID portID program v, r.Valid merged mem) ↔ z = Fin.append work inputs := by
    have both := ties_valid N cell c siteID edgeID portID program v L.size g a x merged
    constructor
    · intro all
      have same := both.mp all
      funext j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · exact (Fin.append_left work inputs k).symm
      · rw [Fin.append_right]
        exact congrFun same (Fin.cast L.size k)
    · intro eq
      apply both.mpr
      funext j
      change z (Fin.natAdd s.work (Fin.cast L.size.symm j)) = _
      rw [eq,Fin.append_right]
      simp [inputs]
  have result (placed : z=Fin.append work inputs) :
      s.placedObserve merged shift (base v.val) mem = s.observe (bits work inputs) := by
    rw [s.placed_observe merged shift (base v.val) (fun r hr => (schema r hr).1) span get (relative.reachable shift)]
    apply L.retention.locality loc
    intro j hj
    change j < s.work+L.program.incoming at hj
    rw [bits,dite_eq_left hj]
    exact (site_at N cell c (sizes N state) siteID g a x v ⟨j,hj⟩).trans (congrFun placed ⟨j,hj⟩)
  change (⟨merged,siteRows N cell c siteID edgeID portID program base v,[]⟩ : Directory).guardedObservations mem = _ ↔ _
  rw [site_checked]
  by_cases hz : z=Fin.append work inputs
  · rw [ite_eq_left (tiesSpec.mpr hz)]
    change s.placedObserve merged shift (base v.val) mem = some os ↔ _
    rw [result hz,L.retention.observe_iff loc]
    constructor
    · rintro ⟨orig,birth,complete⟩
      exact ⟨orig,birth,complete ▸ hz⟩
    · rintro ⟨orig,birth,complete⟩
      refine ⟨orig,birth,funext fun j => ?_⟩
      exact (Fin.append_left _ _ j).symm.trans (congrFun complete (Fin.castAdd _ j)).symm
  · rw [ite_eq_right (mt tiesSpec.mp hz)]
    constructor
    · intro bad; cases bad
    · rintro ⟨orig,_,complete⟩
      apply hz.elim
      have eq : work = L.retention.complete inputs orig := funext fun j =>
        (congrFun complete (Fin.castAdd _ j)).trans (Fin.append_left _ _ j)
      exact eq.symm ▸ complete

end Packing.Inherited.Placement

end BorderVNP
end Computability
end OAI
