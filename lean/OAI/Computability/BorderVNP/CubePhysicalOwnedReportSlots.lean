import OAI.Computability.BorderVNP.CubePhysicalCellOperandOrder
import OAI.Computability.BorderVNP.PackedBundleGroups

/-! # Inverting the actual stable owner directory of unary reports

An owned cell's bundle rows are the stable filter of original source ordinals
by the final cell. Within a source the native ordinal is the original sidecar
position followed by the copy index. Inverting both tables gives exactly the
routed original slots owned by the chosen team.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open Packing.BundleDirectory
open scoped Classical

variable {l : ReportLayout} {N C copies : ℕ} {Team Slots : Type*} (cs : List (ReportCell l))
    (owner : Fin N → Fin C) (team : Fin C → Team) (t : Team)
    (cells : Fin cs.length ≃ {c : Fin C // team c = t})
    (bundle : Fin N → ReportBundle)
    (grouped : ∀ i : Fin cs.length, cs[i].bundles = (sourceRows owner (cells i).val.val).map bundle)

/-- Physical cell row and local original bundle row. -/
abbrev OwnedBundle {l : ReportLayout} (cs : List (ReportCell l)) :=
  (i : Fin cs.length) × Fin cs[i].bundles.length

/-- The exact stable source-filter lookup, including repeated header or sidecar payloads. -/
noncomputable def ownedBundleEquiv : OwnedBundle cs ≃ {r : Fin N // team (owner r) = t} := by
  let localOrd (i : Fin cs.length) : Fin cs[i].bundles.length ≃ {r : Fin N // owner r = (cells i).val} :=
    (finCongr (by rw [grouped i,List.length_map])).trans
      (((List.nodup_finRange N).filter _).getEquiv (sourceRows owner (cells i).val.val) |>.trans
        (Equiv.subtypeEquivRight fun r => mem_sourceRows.trans Fin.ext_iff.symm))
  exact (Equiv.sigmaCongrRight localOrd).trans
    ((Equiv.sigmaCongrLeft (β := fun c : {c : Fin C // team c = t} => {r : Fin N // owner r = c.val}) cells).trans
      (Equiv.sigmaSubtypeFiberEquivSubtype owner (fun _ => Iff.rfl)))

/-- The typed report data at a stable bundle row are the original source data of
that precise ordinal, even when different origins have identical headers. -/
theorem ownedBundleEquiv_read (r : OwnedBundle cs) :
    cs[r.1].bundles[r.2] = bundle ((ownedBundleEquiv cs owner team t cells bundle grouped r).val) := by
  let i := r.1
  let j := r.2
  let src := sourceRows owner (cells i).val.val
  have len : cs[i].bundles.length = src.length := (congrArg List.length (grouped i)).trans (List.length_map ..)
  have fit : j.val < src.length := j.isLt.trans_le len.le
  change cs[i].bundles[j.val] = bundle (src[j.val]'fit)
  have eq := congrArg (fun xs : List ReportBundle => xs[j.val]?) (grouped i)
  change cs[i].bundles[j.val]? = (src.map bundle)[j.val]? at eq
  have hl : cs[i].bundles[j.val]? = some cs[i].bundles[j.val] := List.getElem?_eq_getElem j.isLt
  have hr : src[j.val]? = some src[j.val] := List.getElem?_eq_getElem fit
  rw [hl,List.getElem?_map,hr] at eq
  exact Option.some.inj eq


variable (slotRow : Slots → Fin N)

private def slotsBySource :
    (Σ r : {r : Fin N // team (owner r) = t}, Fin copies × {v : Slots // slotRow v = r.val}) ≃
      (Fin copies × {v : Slots // team (owner (slotRow v)) = t}) where
  toFun u := ⟨u.2.1,⟨u.2.2.val,(congrArg (team ∘ owner) u.2.2.property).trans u.1.property⟩⟩
  invFun u := ⟨⟨slotRow u.2.val,u.2.property⟩,u.1,⟨u.2.val,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨r,hr⟩,c,⟨v,hv⟩⟩
    change slotRow v = r at hv
    subst r
    rfl
  right_inv := fun _ => rfl

/-- Invert the actual stable per-team cell rows, the original one-copy sidecar
and the row-major copy offset. The two small hypotheses concern only the original
bundle header and one-copy source list. -/
noncomputable def ownedUseEquiv
    (clone : ∀ r, (bundle r).header.copies = copies)
    (mark : ∀ r, Fin (bundle r).positions.length ≃ {v : Slots // slotRow v = r}) :
    UseOccurrence cs ≃ (Fin copies × {v : Slots // team (owner (slotRow v)) = t}) := by
  let row := ownedBundleEquiv cs owner team t cells bundle grouped
  let pos (r : OwnedBundle cs) : Fin cs[r.1].bundles[r.2].useCount ≃
      Fin copies × {v : Slots // slotRow v = (row r).val} := by
    let b := cs[r.1].bundles[r.2]
    have matchRow : b = bundle (row r).val := ownedBundleEquiv_read cs owner team t cells bundle grouped r
    have c : b.header.copies = copies := (congrArg (fun z : ReportBundle => z.header.copies) matchRow).trans (clone _)
    let p := (finCongr (congrArg (fun z : ReportBundle => z.positions.length) matchRow)).trans (mark _)
    exact finProdFinEquiv.symm.trans ((p.prodCongr (finCongr c)).trans (Equiv.prodComm _ _))
  exact ((Equiv.sigmaAssoc _).symm.trans (Equiv.sigmaCongrRight pos)).trans
    ((Equiv.sigmaCongrLeft (β := fun r : {r : Fin N // team (owner r) = t} =>
      Fin copies × {v : Slots // slotRow v = r.val}) row).trans (slotsBySource owner team t slotRow))

include cells grouped in
/-- The native writer's actual sparse-copy charge is bounded by all original power
slots over all copies, and equals precisely this team's owned subset. -/
theorem ownedUseCount [Fintype Slots] (clone : ∀ r, (bundle r).header.copies = copies)
    (mark : ∀ r, Fin (bundle r).positions.length ≃ {v : Slots // slotRow v = r}) :
    (∑ i : Fin cs.length, ∑ j : Fin cs[i].bundles.length, cs[i].bundles[j].useCount) =
      copies * Fintype.card {v : Slots // team (owner (slotRow v)) = t} := by
  rw [← occurrence_card cs,Fintype.card_congr (ownedUseEquiv cs owner team t cells bundle grouped slotRow clone mark),
    Fintype.card_prod,Fintype.card_fin]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
