import OAI.ThreeFlat.Diagonal.PhysicalRefreshImage
import OAI.ThreeFlat.Diagonal.RefreshChoiceImage

namespace OAI
/-! # Numeric table choices of the physical refresh transition -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking Native RefreshDemandRows RefreshTies MotifOuterTerms MotifIntegerChoice
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
  (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))

private abbrev dense (z : A.Base × BitWord rem) := profile (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z
private abbrev numeric (q : Block (Fintype.card A.Base) rem) :=
  profile (numberedRefreshGraph A) (tagOrdinal s).symm (SlotImage.demandWidth (numberedRefreshWidths A)) q

private abbrev digits (b : RefreshMotif.Ties (2^s) → ℕ) :=
  Histogram (T.block (RefreshMotif.selected b T.base)).Alphabet (score b T.base (RefreshMotif.selected b T.base))

abbrev numberedRefreshBranches :=
  T.Branch (numberedRefreshGraph A) (tagOrdinal s).symm (SlotImage.demandWidth (numberedRefreshWidths A))

def numBlockEquiv : A.Base × BitWord rem ≃ Block (Fintype.card A.Base) rem := A.order.prodCongr (Equiv.refl _)

theorem numProfile_inv (q : Block (Fintype.card A.Base) rem) :
    numeric A q=dense A ((numBlockEquiv A).symm q) := by
  have m := numProfile A ((numBlockEquiv A).symm q)
  change numeric A (numBlockEquiv A ((numBlockEquiv A).symm q))=_ at m
  simpa using m

/-- Relabel a real move's family of histograms into source-numbered hardware
coordinates, transporting only along equal demand vectors. -/
def numBranches : refreshBinaryBranches T A ≃ numberedRefreshBranches T A :=
  (Equiv.piCongrLeft' (fun z=>digits T (dense A z)) (numBlockEquiv A)).trans
    (Equiv.piCongrRight (fun q=>Equiv.cast (congrArg (digits T) (numProfile_inv A q).symm)))

/-- Return a histogram count by the fixed finite-tile symbol ordinal. -/
def symbolAt (b : RefreshMotif.Ties (2^s) → ℕ) (x : digits T b) (n : ℕ) : ℕ :=
  if hit : n<Fintype.card (T.block (RefreshMotif.selected b T.base)).Alphabet then
    (x.val ((Fintype.equivFin _).symm ⟨n,hit⟩)).val else 0

private theorem symbolAt_transport {b b' : RefreshMotif.Ties (2^s) → ℕ} (eq : b=b')
    (x : digits T b) (n : ℕ) :
    symbolAt T b' ((Equiv.cast (congrArg (digits T) eq)) x) n=symbolAt T b x n := by cases eq; rfl

theorem numBranches_symbol (x : refreshBinaryBranches T A) (q : Block (Fintype.card A.Base) rem) (n : ℕ) :
    symbolAt T (numeric A q) (numBranches T A x q) n =
      symbolAt T (dense A ((numBlockEquiv A).symm q)) (x ((numBlockEquiv A).symm q)) n :=
  symbolAt_transport T (numProfile_inv A q).symm _ n

/-- A fixed grid's supply width depends on the demand profile and its
histogram. Transporting both along a profile identity leaves this integer unchanged. -/
private def localWidth (b : RefreshMotif.Ties (2^s) → ℕ) (x : digits T b) (e : Expander.Arc c) : ℕ :=
  let j := RefreshMotif.selected b T.base
  histWidth (T.block j).output x e + score b T.base j*(T.block j).bits

private theorem localWidth_transport {b b' : RefreshMotif.Ties (2^s) → ℕ} (eq : b=b')
    (x : digits T b) (e : Expander.Arc c) :
    localWidth T b' ((Equiv.cast (congrArg (digits T) eq)) x) e=localWidth T b x e := by cases eq; rfl

theorem numBranches_width (x : refreshBinaryBranches T A) (q : Block (Fintype.card A.Base) rem) (e : Expander.Arc c) :
    T.widths (numberedRefreshGraph A) (tagOrdinal s).symm (SlotImage.demandWidth (numberedRefreshWidths A))
      (numBranches T A x) q e =
      T.widths (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) x ((numBlockEquiv A).symm q) e :=
  localWidth_transport T (numProfile_inv A q).symm _ e

/-- Coordinate by coordinate, the stage prepass supplies the same copy count,
grid entry, and number of active symbols as the mathematical branch register. -/
theorem descriptor_real (z : A.Base × BitWord rem) (f : Fin 3) :
    RefreshStageNav.descriptorWord (numberedRefreshGraph A) (numberedRefreshWidths A)
      T.base (fun j=>Fintype.card (T.block j).Alphabet) (numBlock A z,f) =
      if f.val=0 then refreshBinaryCopies T A z else if f.val=1 then
        (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z).val
      else Fintype.card (refreshBinaryEntry T A z).Alphabet := by
  change (if f.val=0 then score (numeric A _) T.base (tileNumber (numeric A _) T.base) else
    if f.val=1 then (tileNumber (numeric A _) T.base).val else
    Fintype.card (T.block (tileNumber (numeric A _) T.base)).Alphabet)=_
  rw [show numeric A (numBlock A z)=dense A z from numProfile A z]
  rfl

variable (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
  (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ)

theorem descriptor_real_record (i : Fin (refreshBinaryFamily T A hm hh sym rows zero conn).motifs) (f : Fin 3) :
    let Q := refreshBinaryFamily T A hm hh sym rows zero conn
    let z := (refreshBlockOrder A).symm i
    RefreshStageNav.descriptorWord (numberedRefreshGraph A) (numberedRefreshWidths A)
      T.base (fun j=>Fintype.card (T.block j).Alphabet) (numBlock A z,f) =
      if f.val=0 then Q.copies i else if f.val=1 then
        (T.winner (refreshBinaryGraph A) (tagOrdinal s).symm (refreshBinaryInput A) z).val
      else Fintype.card (Q.alphabet i) := descriptor_real T A _ f

end

end ThreeFlat.Diagonal.PhysicalStage

end OAI
