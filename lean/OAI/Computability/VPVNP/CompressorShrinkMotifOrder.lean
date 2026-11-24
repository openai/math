import OAI.Computability.VPVNP.ShrinkStatePass
import OAI.Computability.VPVNP.CompressorRecordsBundleLists
import OAI.Computability.VPVNP.CompressorRecordsShrink

/-!
# The physical order of shrinking terms

A CD occurrence is stored in the row of its assigned port, at the
lane-relative rank used to split the AB bundle. The product of the two
ordinals indexes the dense demand, term and score arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkMotifOrder

open Compression Compression.PackingData

variable {V H Tag L : Type} {n d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (cd : P.BundleNumbering) (site : Site V Tag L ≃ Fin n)

/-- Bundle ordinal followed by the CD rank inside that bundle. -/
def number : P.Motif ≃ Fin ((n*d)*pieceCount d c) :=
  (((Equiv.sigmaFiberEquiv P.bundle).symm.trans (Equiv.sigmaEquivProdOfEquiv cd)).trans
    ((BundleLists.portIndex site).prodCongr (Equiv.refl _))).trans finProdFinEquiv

theorem number_val (m : P.Motif) : (number P cd site m).val =
    (BundleLists.portIndex site (P.bundle m)).val * pieceCount d c + (cd (P.bundle m) ⟨m,rfl⟩).val := by
  change _ + _ * _ = _ * _ + _
  ac_rfl

theorem number_fiber (b : Site V Tag L × Fin d) (r : Fin (pieceCount d c)) :
    (number P cd site ((cd b).symm r).1).val =
      (BundleLists.portIndex site b).val * pieceCount d c + r.val := by
  let m := (cd b).symm r
  rw [number_val]
  generalize he : (cd b).symm r = x
  obtain ⟨x,hb⟩ := x
  have hr := congrArg (cd b) he
  rw [Equiv.apply_symm_apply] at hr
  subst b
  rw [← hr]

/-- The dense order uses the same base, tag and lane numerals as the
shrinking graph scans. -/
noncomputable abbrev stateNumber {a g : ℕ} (X : State a (packingLaneBits a g)) :=
  number X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex)

/-- The cardinal-length form can be used directly by history readers. -/
noncomputable def entries {a g : ℕ} (X : State a (packingLaneBits a g)) :
    Fin (Fintype.card X.packingData.Motif) ≃ X.packingData.Motif :=
  let e := stateNumber X
  (finCongr ((Fintype.card_congr e).trans (Fintype.card_fin _))).trans e.symm

theorem entries_ordinal {a g : ℕ} (X : State a (packingLaneBits a g)) (m : X.packingData.Motif) :
    ((entries X).symm m).val = (stateNumber X m).val := rfl

end CompressorRecords.ShrinkMotifOrder

end VPVNP
end Computability
end OAI
