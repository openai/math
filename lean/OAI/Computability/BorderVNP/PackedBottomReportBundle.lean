import OAI.Computability.BorderVNP.PackedBottomSelectedReports
import OAI.Computability.BorderVNP.PackedBottomBundleHeader
import OAI.Computability.BorderVNP.DiagonalTallyReportModel

/-! # The scanner's actual immutable payload and weighted-copy choices

The report-side source list is extracted before private wiring and padding
are added. The opaque payload still contains the complete staged and padded
one-copy box. The scanner's bit at each row-major occurrence is the actual
original selected wire in its physical copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse DiagonalTallyCellReports

/-- The true typed report bundle for a one-copy payload and its original marked
sources. Its use function reads only the selected fine lane of each actual copy. -/
def physicalBundle (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool) : ReportBundle where
  header := h
  factors := body
  positions := positions h.orig original
  uses i :=
    let rc := finProdFinEquiv.symm i
    bank (h.boxBase+rc.2.val*h.stride+(selectedWires original)[rc.1.val]'(by
      have bound := rc.1.isLt
      simpa only [selectedWires_length,positions_length] using bound))

/-- Resolving the physical copy index returns the selected original wire and the
two immutable source labels written in the decoded private metadata. -/
theorem physicalBundle_use (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool)
    (r : Fin (positions h.orig original).length) (i : Fin h.copies) :
    (physicalBundle h body original bank).uses (finProdFinEquiv (r,i)) =
      bank (h.boxBase+i.val*h.stride+(selectedWires original)[r.val]'(by
        simpa only [positions_length,selectedWires_length] using r.isLt)) := by
  let get (p : Fin (positions h.orig original).length × Fin h.copies) :=
    bank (h.boxBase+p.2.val*h.stride+(selectedWires original)[p.1.val]'(by
      simpa only [selectedWires_length,positions_length] using p.1.isLt))
  exact congrArg get (finProdFinEquiv.symm_apply_apply (r,i))

/-- Every listed position/copy pair denotes precisely its own native operand row. -/
theorem physicalBundle_source (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool)
    (r : Fin (positions h.orig original).length) (i : Fin h.copies) :
    (physicalBundle h body original bank).source (finProdFinEquiv (r,i)) = (positions h.orig original)[r.val] := by
  have hp : 0 < h.copies := i.pos
  have hv : (finProdFinEquiv (r,i)).val / h.copies = r.val := by
    change (i.val+h.copies*r.val)/h.copies = r.val
    rw [Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt i.isLt,Nat.zero_add]
  let j : Fin (positions h.orig original).length := ⟨(finProdFinEquiv (r,i)).val/h.copies,hv ▸ r.isLt⟩
  change (positions h.orig original)[j.val] = (positions h.orig original)[r.val]
  exact congrArg (fun a : Fin (positions h.orig original).length => (positions h.orig original)[a.val])
    (show j = r from Fin.ext hv)

/-- With a passing one-copy table and the actual supplemental records, the outer
guessed bit at the compact cursor is precisely the corresponding original wire
choice used by the native report operand. -/
theorem physicalBundle_use_forced (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool)
    (boxes : List (List Factor)) (cursor : ℕ) (r : Fin (positions h.orig original).length) (i : Fin h.copies)
    (hs : h.stride = bottomStride h.orig h.cap) (hc : count original ≤ h.cap)
    (reportPass : ∀ row ∈ reportRows h.boxBase h.orig h.cap h.copies cursor original, row.Valid boxes bank)
    (boxPass : ∀ f ∈ stage h.orig original, (f.observe bank (h.boxBase+i.val*h.stride) i.val).isSome = true) :
    (physicalBundle h body original bank).uses (finProdFinEquiv (r,i)) =
      bank (cursor+r.val*h.copies+i.val) := by
  have bound : r.val < count original := by simpa only [positions_length] using r.isLt
  have selected := ((stage_pass bank _ i.val h.orig original).mp boxPass).2 ⟨r.val,bound⟩
  have bound' := (reportRows_valid bank boxes h.boxBase h.orig h.cap h.copies cursor original hc).mp reportPass
    i.val i.isLt r.val (lt_of_lt_of_le bound hc)
  rw [physicalBundle_use]
  exact selected.symm.trans (by simpa only [hs,stageValue,ite_eq_left bound] using bound')

end Packing.BottomReports

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited DiagonalTallyCellReports
open scoped Classical

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (sites : N.Site ↪ Fin ns) (edges : N.Edge ↪ Fin ne)
variable (ports : P ↪ Fin np) (channels : Q ↪ Fin qe) (groups : A ↪ Fin qa) (v : C)
variable (rules : ∀ w : {u : N.Site // cell u = v}, Rule N w.val)

local notation "G" => grouped (H := H) (src := src) (dst := dst) N cell position width owner
local notation "fs" => GridBoxes.factors N cell v sites edges ports rules

/-- The actual report bundle handed to the cell scanner. Its opaque body includes
private fine ties, both padding checks and all staged original factors; the sidecar
lists only the original weighted sources. -/
noncomputable def reportBundle (slot base copies capFine capReport : ℕ) (bank : ℕ → Bool) : ReportBundle :=
  let orig := capFine+incoming G v
  let hdr : BundleHeader := ⟨slot,copies,base,bottomStride orig capReport,capReport,orig⟩
  physicalBundle hdr (stored N cell position pack width owner lane aligned sites edges ports channels groups v
    rules capFine capReport) fs bank

/-- The physical private box is read with its full original one-copy body and the
weighted-only metadata is decoded at its fixed public displacement. -/
theorem delivered_bundle {description w : ℕ} (mem : VPVNP.BurstRAM.Memory w)
    (Hbit bodyCap slot base copies capFine capReport : ℕ) (bank : ℕ → Bool) :
    let b := reportBundle N cell position pack width owner lane aligned sites edges ports channels groups v rules
      slot base copies capFine capReport bank
    (Packet.Source.boxBody b.factors).length ≤ bodyCap →
    Hbit+bodyCap+(TallySidecar.bits Hbit b.positions).length ≤ description →
    (∀ j : Fin description, (mem (slot+j.val)).val =
      (Packet.Source.siteWithTally Hbit bodyCap b.factors (TallySidecar.bits Hbit b.positions) j).toNat) →
    DiagonalTallyBits.WordsAt mem (slot+Hbit+bodyCap) (TallySidecar.words Hbit b.positions) := by
  intro b hbody hfit arrived
  exact TallySidecar.delivered_words mem slot Hbit bodyCap b.factors b.positions hbody hfit arrived

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
