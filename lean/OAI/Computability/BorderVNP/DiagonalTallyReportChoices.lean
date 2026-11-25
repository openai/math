import OAI.Computability.BorderVNP.DiagonalTallyReportBatch
import Mathlib.Data.List.OfFn

/-! # Coordinates for the complete native stream of checked cell reports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

/-- Consecutive bits of an arbitrary native guess tape. -/
def reportSlice (a : ℕ → Bool) (p n : ℕ) := List.ofFn fun i : Fin n => a (p+i.val)

private theorem slice_append (a : ℕ → Bool) (p n m : ℕ) :
    reportSlice a p n ++ reportSlice a (p+n) m=reportSlice a p (n+m) := by
  simp [reportSlice,List.ofFn_add,Nat.add_assoc]

/-- Replace only the guessed use bits of an immutable bottom site. -/
def ReportBundle.withTape (b : ReportBundle) (a : ℕ → Bool) (p : ℕ) : ReportBundle :=
  {b with uses := fun i => a (p+i.val)}

/-- Copy every site header and one-copy payload, assigning its actual expanded number
of consecutive native choice bits. -/
def tapeBundles (a : ℕ → Bool) : ℕ → List ReportBundle → List ReportBundle
  | _,[] => []
  | p,b::bs => b.withTape a p :: tapeBundles a (p+b.useCount) bs

@[simp] theorem tapeBundles_length (a : ℕ → Bool) (p : ℕ) (bs : List ReportBundle) :
    (tapeBundles a p bs).length=bs.length := by
  induction bs generalizing p <;> simp [tapeBundles, *]

@[simp] theorem tapeBundles_useCount (a : ℕ → Bool) (p : ℕ) (bs : List ReportBundle) :
    (tapeBundles a p bs).map ReportBundle.useCount=bs.map ReportBundle.useCount := by
  induction bs generalizing p <;> simp [tapeBundles,ReportBundle.withTape,ReportBundle.useCount, *]

theorem tapeBundles_bits (a : ℕ → Bool) (p : ℕ) (bs : List ReportBundle) :
    (tapeBundles a p bs).flatMap (fun b => List.ofFn b.uses)=
      reportSlice a p (bs.map ReportBundle.useCount).sum := by
  induction bs generalizing p with
  | nil => simp [tapeBundles,reportSlice]
  | cons b bs ih =>
    simp only [tapeBundles,List.flatMap_cons,ih,List.map_cons,List.sum_cons]
    exact slice_append ..

/-- Row-major gadget fields, followed by the true retained sites' expanded flags. -/
def ReportCell.withTape {l : ReportLayout} (c : ReportCell l) (a : ℕ → Bool) (p : ℕ) : ReportCell l :=
  {c with counts := fun g j => a (p+(g.val*l.countWidth+j.val)),
          bundles := tapeBundles a (p+l.gadgets*l.countWidth) c.bundles}

@[simp] theorem ReportCell.withTape_tailWidth {l : ReportLayout} (c : ReportCell l) (a : ℕ → Bool) (p : ℕ) :
    (c.withTape a p).tailWidth=c.tailWidth := by simp [tailWidth,withTape]

@[simp] theorem ReportCell.withTape_headerWords {l : ReportLayout} (c : ReportCell l) (a : ℕ → Bool) (p : ℕ) :
    (c.withTape a p).headerWords=c.headerWords := by simp [headerWords,withTape]

theorem ReportCell.withTape_bits {l : ReportLayout} (c : ReportCell l) (a : ℕ → Bool) (p : ℕ) :
    (c.withTape a p).bits=reportSlice a p c.tailWidth := by
  simp only [bits,withTape,tapeBundles_bits,tailWidth]
  rw [← slice_append]
  exact congrArg (fun xs => xs++_) (List.ofFn_mul (fun i : Fin (l.gadgets*l.countWidth) => a (p+i.val))).symm

/-- Decode the complete native choice tape against the true ordered physical cells. -/
def tapeCells {l : ReportLayout} (a : ℕ → Bool) : ℕ → List (ReportCell l) → List (ReportCell l)
  | _,[] => []
  | p,c::cs => c.withTape a p :: tapeCells a (p+c.tailWidth) cs

@[simp] theorem tapeCells_length {l : ReportLayout} (a : ℕ → Bool) (p : ℕ) (cs : List (ReportCell l)) :
    (tapeCells a p cs).length=cs.length := by
  induction cs generalizing p <;> simp [tapeCells, *]

theorem tapeCells_bits {l : ReportLayout} (a : ℕ → Bool) (p : ℕ) (cs : List (ReportCell l)) :
    reportBits (tapeCells a p cs)=reportSlice a p (reportBits cs).length := by
  induction cs generalizing p with
  | nil => simp [reportBits,tapeCells,reportSlice]
  | cons c cs ih =>
    change (c.withTape a p).bits++reportBits (tapeCells a (p+c.tailWidth) cs)=_
    rw [c.withTape_bits,ih]
    simp only [reportBits,List.flatMap_cons,List.length_append,c.bits_length]
    exact slice_append ..

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
