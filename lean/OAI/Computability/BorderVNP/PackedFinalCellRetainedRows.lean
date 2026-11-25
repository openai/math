import OAI.Computability.BorderVNP.PackedFinalCellRetainedGuard

/-! # The complete cell guard on the retained sites in their native row order -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open scoped Classical
open private combine append_groups from OAI.Computability.BorderVNP.CellGuardedObservations

private theorem combine_some {α : Type*} (a b : Option (List α)) (out : List α) :
    combine a b = some out ↔ ∃ x y, a=some x ∧ b=some y ∧ x++y=out := by
  cases a <;> cases b <;> simp [combine]

/-- Every successful merged guard splits into the actual checked observations
of each site, in the order of the padded, stably sorted physical rows. -/
theorem Directory.flatMap_guarded_iff {V : Type*} (sites : List V) (distinct : sites.Nodup)
    (boxes : List (List Factor)) (rows : V → List Record) (bank : ℕ → Bool) (out : List (Bool × Option ℕ)) :
    (⟨boxes,sites.flatMap rows,[]⟩ : Directory).guardedObservations bank = some out ↔
      ∃ chunks : V → List (Bool × Option ℕ), (∀ v∈sites,
        (⟨boxes,rows v,[]⟩ : Directory).guardedObservations bank=some (chunks v)) ∧ sites.flatMap chunks=out := by
  induction sites generalizing out with
  | nil =>
    simp [Directory.guardedObservations,Directory.observations,Directory.occurrences]
  | cons v vs ih =>
    have fresh := List.nodup_cons.mp distinct
    rw [List.flatMap_cons,append_groups,combine_some]
    constructor
    · rintro ⟨x,y,head,tail,rfl⟩
      obtain ⟨chunks,each,rfl⟩ := (ih fresh.2 y).mp tail
      let all := Function.update chunks v x
      have outside (u : V) (hu : u∈vs) : all u=chunks u := Function.update_of_ne (show u≠v from fun eq => fresh.1 (eq ▸ hu)) ..
      refine ⟨all,?_,?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with eq | belongs
        · subst u; simpa only [all,Function.update_self] using head
        · rw [outside u belongs]; exact each u belongs
      · rw [List.flatMap_cons,show all v=x from Function.update_self ..]
        exact congrArg (x++·) (List.flatMap_congr outside)
    · rintro ⟨all,each,rfl⟩
      exact ⟨all v,vs.flatMap all,each _ List.mem_cons_self,
        (ih fresh.2 _).mpr ⟨all,fun u hu => each u (.tail _ hu),rfl⟩,rfl⟩

end CellSparse

namespace Packing.Inherited.FinalCell

open Crossing CellAddresses CellSparse BankBoxOrdinal
open scoped Classical
open private firstBox_span from OAI.Computability.BorderVNP.PackedFinalCellObservationTail
open private off from OAI.Computability.BorderVNP.PackedBankSortedCell

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits' : P → ℕ}
variable (N : Network D P bits') (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
variable (portID : P ↪ Fin np) (state : Site.Programs N) (owner : Fin ns → ℕ)
private abbrev program := fun v : N.Site => (state v).program
private abbrev sizes := fun v : N.Site => (state v).program.size

/-- From the actual checked compact directory recover each live site's intrinsic
work and observation list. Conversely these birth witnesses with exactly their
forced work and incoming lanes reconstruct the whole checked list, including
sites with zero observations. -/
theorem guarded_birth_iff (c : ℕ) (reports : List (List ℕ)) (ho : ∀ v, owner (siteID v)=cell v)
    (birthLocal : ∀ v, (state v).birth.Local) (schema : ∀ v, (state v).program.Schema)
    (relative : ∀ v, (state v).program.RelativeBoxes) (g : Fin (guessedSize N cell c) → Bool)
    (a : Fin (siteSize N cell c (sizes N state)) → Bool) (x : Fin (suppliedSize N cell c) → Bool)
    (out : List (Bool × Option ℕ)) :
    let live := sites siteID owner c
    let mem := lookup (bank N cell c (sizes N state) g a x)
    (directory owner N cell siteID edgeID portID (program N state) c reports).guardedObservations mem = some out ↔
      ∃ chunks : N.Site → List (Bool × Option ℕ), live.flatMap chunks=out ∧
        ∀ v (hv : v∈live), let vv : {v : N.Site // cell v=c} := ⟨v,(ho v).symm.trans (site_owner siteID owner hv)⟩
          let L := state v
          let inputs := Placement.canonical N cell c edgeID portID vv g x ∘ Fin.cast L.size
          ∃ orig : Fin L.birth.work → Bool, L.birth.observe (bits orig (L.retention.readInput inputs)) = some (chunks v) ∧
            siteWords N cell c siteID (sizes N state) a vv = Fin.append (L.retention.complete inputs orig) inputs := by
  intro live mem
  let progs := program N state
  let merged := live.flatMap fun u => (progs u).boxes
  let first := firstBox siteID owner progs
  let rs := fun v => (progs v).placedRows (off N cell siteID progs v) (first v) ++ binding N cell siteID edgeID portID progs v
  change (⟨merged,live.flatMap rs,[]⟩ : Directory).guardedObservations mem=some out ↔ _
  rw [Directory.flatMap_guarded_iff live (sites_nodup siteID owner c)]
  have one (v : N.Site) (hv : v∈live) (chunk : List (Bool × Option ℕ)) :
      let vv : {v : N.Site // cell v=c} := ⟨v,(ho v).symm.trans (site_owner siteID owner hv)⟩
      let L := state v
      let inputs := Placement.canonical N cell c edgeID portID vv g x ∘ Fin.cast L.size
      (⟨merged,rs v,[]⟩ : Directory).guardedObservations mem = some chunk ↔
        ∃ orig : Fin L.birth.work → Bool, L.birth.observe (bits orig (L.retention.readInput inputs)) = some chunk ∧
          siteWords N cell c siteID (sizes N state) a vv = Fin.append (L.retention.complete inputs orig) inputs := by
    have same := (ho v).symm.trans (site_owner siteID owner hv)
    subst c
    exact Placement.checked_site_birth_iff N cell (cell v) siteID edgeID portID state g a x merged first ⟨v,rfl⟩
      (birthLocal v) (schema v) (firstBox_span N (cell v) siteID owner progs hv) (box_get siteID owner progs hv) (relative v) chunk
  constructor
  · rintro ⟨chunks,each,flat⟩
    exact ⟨chunks,flat,fun v hv => (one v hv _).mp (each v hv)⟩
  · rintro ⟨chunks,flat,each⟩
    exact ⟨chunks,fun v hv => (one v hv _).mpr (each v hv),flat⟩

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
