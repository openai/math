import OAI.Computability.BorderVNP.PackedFinalCellRetainedRows
import OAI.Computability.BorderVNP.DiagonalSiteTagRead

/-! # Recovering the tagged observation fiber from the checked cell bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

variable {inc : ℕ} (L : Site.Lineage inc)

/-- The original private work occupies the initial portion of the physically
staged site word, before the inherited and final incidence intervals. -/
def originalWord (slab : Fin L.program.size → Bool) (j : Fin L.birth.work) : Bool :=
  slab ((j.castLE L.retention.work_le).castAdd L.program.incoming)

/-- A correctly retained site yields its actual birth work at this prefix. -/
theorem originalWord_complete (inputs : Fin L.program.incoming → Bool) (orig : Fin L.birth.work → Bool) :
    L.originalWord (Fin.append (L.retention.complete inputs orig) inputs) = orig := by
  funext j
  change Fin.append (L.retention.complete inputs orig) inputs ((j.castLE L.retention.work_le).castAdd _) = orig j
  rw [Fin.append_left]
  exact L.retention.complete_prefix inputs orig j

end Packing.Inherited.Site.Lineage

namespace Packing.Inherited.FinalCell

open Crossing CellAddresses CellSparse BankBoxOrdinal Diagonal.CellEntries
open scoped Classical

variable {D M np ns : ℕ} {P : Type*} [Fintype P] {bits' : P → ℕ}
variable (N : Network D P bits') (cell : N.Site → ℕ) (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin M)
variable (portID : P ↪ Fin np) (state : Site.Programs N) (owner : Fin ns → ℕ)
variable (c : ℕ) (g : Fin (guessedSize N cell c) → Bool) (x : Fin (suppliedSize N cell c) → Bool)

private abbrev progs := fun v : N.Site => (state v).program
private abbrev widths := fun v : N.Site => (state v).program.size

/-- True final incidence vector of a site in this cell, in the local program's
input order. -/
noncomputable abbrev currentInput (v : {v : N.Site // cell v=c}) :=
  Placement.canonical N cell c edgeID portID v g x ∘ Fin.cast (state v.val).size

/-- Given the original private bits selected at this term, the real final guard
accepts exactly the canonical retained and incident lanes of all nonzero tagged
sites. The checked output is their genuine observation list in the native stable
order, including successful occurrences whose field value specializes to zero. -/
theorem guarded_tagged_iff {Param Gadget : Type*} (number : Gadget ↪ ℕ)
    (tag : N.Site → Entry Param Gadget) (compatible : (v : N.Site) → (Fin (state v).birth.work → Bool) → Prop)
    (read : (v : {v : N.Site // cell v=c}) → (state v.val).birth.TagRead
      ((state v.val).retention.readInput (currentInput N cell edgeID portID state c g x v))
      (compatible v.val) (tag v.val) number)
    (reports : List (List ℕ)) (ho : ∀ v, owner (siteID v)=cell v)
    (birthLocal : ∀ v, (state v).birth.Local) (schema : ∀ v, (state v).program.Schema)
    (relative : ∀ v, (state v).program.RelativeBoxes)
    (a : Fin (siteSize N cell c (widths N state)) → Bool)
    (selected : ∀ v : {v : N.Site // cell v=c}, compatible v.val ((state v.val).originalWord
      (siteWords N cell c siteID (widths N state) a v))) (out : List (Bool × Option ℕ)) :
    let live := sites siteID owner c
    let mem := lookup (bank N cell c (widths N state) g a x)
    let obs := fun v : N.Site => if hv : cell v=c then (read ⟨v,hv⟩).observations else []
    (directory owner N cell siteID edgeID portID (progs N state) c reports).guardedObservations mem = some out ↔
      live.flatMap obs = out ∧ ∀ v (hv : v∈live),
        let vv : {v : N.Site // cell v=c} := ⟨v,(ho v).symm.trans (site_owner siteID owner hv)⟩
        let input := currentInput N cell edgeID portID state c g x vv
        tag v ≠ 0 ∧ siteWords N cell c siteID (widths N state) a vv =
          Fin.append ((state v).retention.complete input (read vv).work) input := by
  intro live mem obs
  apply (guarded_birth_iff N cell siteID edgeID portID state owner c reports ho birthLocal schema relative g a x out).trans
  let word := siteWords N cell c siteID (widths N state) a
  let input := currentInput N cell edgeID portID state c g x
  have see (v : {v : N.Site // cell v=c}) (orig : Fin (state v.val).birth.work → Bool) (chunk : List (Bool × Option ℕ))
      (birth : (state v.val).birth.observe (bits orig ((state v.val).retention.readInput (input v)))=some chunk)
      (placed : word v = Fin.append ((state v.val).retention.complete (input v) orig) (input v)) :
      tag v.val≠0 ∧ orig=(read v).work ∧ chunk=(read v).observations := by
    have raw := selected v
    have recovered := (congrArg (state v.val).originalWord placed).trans ((state v.val).originalWord_complete (input v) orig)
    exact ((read v).read orig chunk (recovered ▸ raw)).mp birth
  constructor
  · rintro ⟨chunks,flat,checked⟩
    have each (v : N.Site) (hv : v∈live) :
        let vv : {v : N.Site // cell v=c} := ⟨v,(ho v).symm.trans (site_owner siteID owner hv)⟩
        (tag v ≠ 0 ∧ word vv = Fin.append ((state v).retention.complete (input vv) (read vv).work) (input vv)) ∧
          chunks v = obs v := by
      let vv : {v : N.Site // cell v=c} := ⟨v,(ho v).symm.trans (site_owner siteID owner hv)⟩
      obtain ⟨orig,birth,placed⟩ := checked v hv
      obtain ⟨passed,eq,seen⟩ := see vv orig (chunks v) birth placed
      refine ⟨⟨passed,eq ▸ placed⟩,?_⟩
      simpa only [obs,dite_eq_left (show cell v=c from vv.property)] using seen
    exact ⟨(List.flatMap_congr fun v hv => (each v hv).2.symm).trans flat,fun v hv => (each v hv).1⟩
  · rintro ⟨flat,all⟩
    refine ⟨obs,flat,?_⟩
    intro v hv
    let vv : {v : N.Site // cell v=c} := ⟨v,(ho v).symm.trans (site_owner siteID owner hv)⟩
    have hit := all v hv
    refine ⟨(read vv).work,?_,hit.2⟩
    exact ((read vv).read _ _ (read vv).chosen).mpr ⟨hit.1,rfl,dite_eq_left (show cell v=c from vv.property)⟩

end Packing.Inherited.FinalCell

end BorderVNP
end Computability
end OAI
