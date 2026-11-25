import OAI.Computability.BorderVNP.DiagonalReportBatchFiber
import OAI.Computability.BorderVNP.CubePhysicalMergedCellRead
import OAI.Computability.BorderVNP.PackedFinalCellFiniteTagged
import Mathlib.Data.List.NodupEquivFin

/-! # Scalar operands on the actual returned private count tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open Crossing CellSparse Packing.Inherited Packing.BottomReports DiagonalTallyCellReports
open private countPart_injective from OAI.Computability.BorderVNP.DiagonalCheckedCellReport
open scoped Classical

/-- The public site list, in increasing physical row order and with empty slots removed. -/
noncomputable def cellSiteOrder {V : Type} {C ns : ℕ} (cell : V → Fin C) (id : V ↪ Fin ns)
    (owner : Fin ns → ℕ) (ho : ∀ v, owner (id v)=(cell v).val) (c : Fin C) :
    Fin (FinalCell.sites id owner c.val).length ≃ {v // cell v=c} :=
  ((FinalCell.sites_nodup id owner c.val).getEquiv _).trans (Equiv.subtypeEquivRight fun v => by
    constructor
    · intro hv
      exact Fin.ext ((ho v).symm.trans (FinalCell.site_owner id owner hv))
    · intro hv
      exact FinalCell.mem_sites_of_owner id owner v c.val ((ho v).trans (congrArg Fin.val hv)))

/-- Observations in the passed directory occur in the same order as the native cell rows. -/
theorem cellSiteOrder_flatMap {V α : Type} {C ns : ℕ} (cell : V → Fin C) (id : V ↪ Fin ns)
    (owner : Fin ns → ℕ) (ho : ∀ v, owner (id v)=(cell v).val) (c : Fin C)
    (reads : {v // cell v=c} → List α) :
    (List.ofFn (cellSiteOrder cell id owner ho c)).flatMap reads =
      (FinalCell.sites id owner c.val).flatMap (fun v => if h : cell v=c then reads ⟨v,h⟩ else []) := by
  let l := FinalCell.sites id owner c.val
  let order := cellSiteOrder cell id owner ho c
  let chunk := fun v => if h : cell v=c then reads ⟨v,h⟩ else []
  have eq : (List.ofFn order).map Subtype.val = l := by
    rw [List.map_ofFn]
    exact List.ofFn_get l
  have part (v : {v // cell v=c}) : reads v = chunk v.val := by
    simp only [chunk,dite_eq_left v.property]
  calc
    _ = (List.ofFn order).flatMap (chunk ∘ Subtype.val) := congrArg (fun f => (List.ofFn order).flatMap f) (funext part)
    _ = ((List.ofFn order).map Subtype.val).flatMap chunk := by simp only [Function.comp_def,List.flatMap_map]
    _ = _ := congrArg (List.flatMap chunk) eq

variable {l : ReportLayout} {V : Type} {C ns w n : ℕ} (cell : V → Fin C) (id : V ↪ Fin ns)
    (owner : Fin ns → ℕ) (ho : ∀ v, owner (id v)=(cell v).val) (c : Fin C)
    (s : AssignedCell l) (pass : s.Passing w n) (r : ReportCell l)
    (canonical : r.bits=s.spelling) (seen : {v // cell v=c} → List (Bool × Option ℕ))
    (split : (FinalCell.sites id owner c.val).flatMap (fun v => if h : cell v=c then seen ⟨v,h⟩ else []) =
      s.observations) (refs : Fin l.gadgets → ℕ)

/-- A canonical native return checks every reported digit against the observations of
the original compact cell. The address is relative to its actual private and boundary
bit prefix, independently of the position of this cell in the outer report table. -/
noncomputable def returnedCellRead : CellRead {v // cell v=c} l.gadgets where
  count := (FinalCell.sites id owner c.val).length
  order := cellSiteOrder cell id owner ho c
  directory := s.initial
  bank := lookup (s.pre++r.bits)
  reportLength := (congrArg List.length pass.layout).trans (countFields_length ..)
  observed := seen
  reads := (Directory.guarded_some.mp (pass.seen r.bits)).2.trans (congrArg some
    (split.symm.trans (cellSiteOrder_flatMap cell id owner ho c seen).symm))
  pass := by
    have parts := List.append_inj (show countPart r.counts ++ (r.bundles.flatMap fun b => List.ofFn b.uses) =
      countPart (observationCounts s.observations l.gadgets l.countWidth) ++ useTape s.pre s.bundles from canonical)
      (by rw [countPart_length,countPart_length])
    have valid := (r.checkedCounts s.pre s.observations pass.range pass.fit).mpr (countPart_injective parts.1)
    have length : s.pre.length = s.privateWires+s.boundary.length := by simp [AssignedCell.pre]
    rw [length,←pass.layout] at valid
    rw [pass.unsigned.weight_guarded,ite_eq_left (show ∃ os, _ from ⟨_,pass.seen r.bits,valid⟩)]
    decide
  zeroAddr := l.zeroAddr
  references := refs

/-- The relative count fields checked by the sparse evaluator and the physical
digits read by the writer start at the same offset in this cell. -/
theorem returnedCellRead_fields (prefixSize : r.privateWires+r.supplied = s.privateWires+s.boundary.length) :
    let read := returnedCellRead cell id owner ho c s pass r canonical seen split refs
    read.directory.reportedCounts = countFields (r.privateWires+r.supplied) l.gadgets l.countWidth ∧
      ∀ g j, r.counts g j = read.bank (r.privateWires+r.supplied+g.val*l.countWidth+j.val) := by
  intro read
  rw [prefixSize]
  refine ⟨pass.layout,?_⟩
  intro g j
  have length : s.pre.length = s.privateWires+s.boundary.length := by simp [AssignedCell.pre]
  change r.counts g j = lookup (s.pre++r.bits) (s.privateWires+s.boundary.length+g.val*l.countWidth+j.val)
  rw [←length]
  exact ((r.bankRead s.pre).1 g j).symm

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
