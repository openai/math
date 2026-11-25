import OAI.ThreeFlat.Diagonal.CompressorDemandCounts
import OAI.ThreeFlat.Diagonal.CompressorOrderIndex
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI
/-! # The ordinal of a CD motif within its AB bundle -/

namespace ThreeFlat.Diagonal
open scoped Classical BigOperators

namespace CompressorRegularize
variable {A B : Type*} [Fintype A] [LinearOrder A] [DecidableEq B] {Q : ℕ}

theorem numbering_position (f : A → B) (h : ∀ b, (incident f b).card = Q) (e : A) :
    (numbering f h e).2.val = ∑ a : {z : A // f z = f e}, if a.val < e then 1 else 0 := by
  let p := f e
  let s := incident f p
  let a : s := ⟨e,by simp [s,incident,p]⟩
  let j := (s.orderIsoOfFin (h p)).symm a
  have val : ((s.orderIsoOfFin (h p)) j).val = e :=
    congrArg Subtype.val ((s.orderIsoOfFin (h p)).apply_symm_apply a)
  change j.val = _
  have rank := sorted_index s (h p) j
  rw [val] at rank
  rw [← rank]
  calc
    _ = ∑ z ∈ s, if z < e then 1 else 0 := (Finset.sum_boole _ _).symm
    _ = _ := Finset.sum_subtype s (by simp [s,incident,p]) _

end CompressorRegularize

namespace CompressorPacking
open Computability.VPVNP.Compression
variable {V H Tag L : Type*} {c d : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)

theorem motif_position (code : Arc V H Tag L d c ↪ ℕ) (hc : 2 ≤ c) (m : P.Motif) :
    (motifNumbers P code hc m).2.val =
      ∑ a : {q : P.Motif // P.bundle q = P.bundle m}, if code a.val.val < code m.val then 1 else 0 := by
  let : LinearOrder P.Motif := LinearOrder.lift' (fun q : P.Motif => code q.val)
    (code.injective.comp Subtype.val_injective)
  unfold motifNumbers
  apply CompressorRegularize.numbering_position

theorem motif_position_scan (code : Arc V H Tag L d c ↪ ℕ) (hc : 2 ≤ c) (m : P.Motif) :
    let p := P.bundle m
    (motifNumbers P code hc m).2.val =
      ∑ side : Bool, ∑ i : Fin d, ∑ u : BitWord c,
        if acceptedCenter P p side i u ∧ code (atCenter P p side i u) < code m.val then 1 else 0 := by
  dsimp only
  rw [motif_position]
  rw [cd_scan P (fun a => if code a < code m.val then 1 else 0) (P.bundle m)]
  simp only [ite_and]

end CompressorPacking
end ThreeFlat.Diagonal

end OAI
