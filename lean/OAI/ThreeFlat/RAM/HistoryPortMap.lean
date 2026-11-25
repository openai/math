import OAI.ThreeFlat.Diagonal.HistoryPortLayout
import OAI.ThreeFlat.RAM.HistoryJoinScan

namespace OAI
/-! # Actual affine source maps for inherited and freshly private bits -/

namespace ThreeFlat.RAM.HistoryPortMap

open Diagonal.HistoryContraction Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr BitLayout
open scoped BigOperators

/-- Input `[offset in child, split, first block base, second block base]`.
The two bases are absolute bit-source addresses after the selected join. -/
def word (w k : ℕ) : Term w k 4 :=
  Term.select .lt (.result 0) (.result 1) (Term.binary .add (.result 2) (.result 0))
    (Term.binary .add (.result 3) (Term.binary .sub (.result 0) (.result 1)))

def piecewise (x split first second : ℕ) := if x < split then first+x else second+(x-split)

theorem eval_word {w k : ℕ} (params : Fin k → Word w) (m : Memory w) (vs : Fin 4 → Word w) :
    (word w k).eval params m vs = if vs 0 < vs 1 then vs 2+vs 0 else vs 3+(vs 0-vs 1) := by
  by_cases order : vs 0 < vs 1 <;>
    simp [word,Term.eval_select,Term.eval_binary,Term.eval,BinaryOp.eval,Comparison.test,order]

variable {S : Shape} {Pins F : Type*} [CommSemiring F] (L : PortLayout S Pins)
    {R : Rewrite S F} {t : Fin R.count} (W : PortLayout (R.target t) Pins)
    (children : (R.target t).Site → ℕ) (ord : ∀ v, Fin (children v) ≃ {i // R.owner t i = v})

/-- Every child pin map is two affine runs. The public run uses the parent's
inherited external-pin interval, the private run uses its guessed old halves. -/
theorem child_map (v : (R.target t).Site) (i : Fin (children v)) (j : Fin (L.form.width (ord v i).val)) :
    let out := L.inherit W children ord
    let extBegin := ∑ a : Fin i.val, L.ext (ord v (Fin.castLE i.isLt.le a)).val
    let halfBegin := ∑ a : Fin i.val, L.halfBits (ord v (Fin.castLE i.isLt.le a)).val
    sourceAddress (L.previousWire out children ord v i (L.inheritedIndex W children ord v i) j) =
      piecewise j.val (L.ext (ord v i).val) (2+extBegin) (2+out.form.width v+halfBegin) := by
  intro out extBegin halfBegin
  refine Fin.addCases (fun x => ?_) (fun x => ?_) j
  · simp only [PortLayout.previousWire,Fin.append_left,sourceAddress,Fin.val_castAdd,
      PortLayout.inherited_offset,piecewise,ite_eq_left x.isLt]
    dsimp [extBegin]
    omega
  · have high : ¬ L.ext (ord v i).val + x.val < L.ext (ord v i).val := by omega
    have index : (finSigmaFinEquiv (n:=L.oldWidths children ord v) ⟨i,x⟩).val=halfBegin+x.val :=
      finSigmaFinEquiv_apply (n:=L.oldWidths children ord v) ⟨i,x⟩
    simp only [PortLayout.previousWire,Fin.append_right,sourceAddress,hiddenBase,Fin.val_natAdd,
      piecewise,ite_eq_right high]
    rw [index]
    omega

/-- The kernel's first interval points into the parent's own private prefix;
its second points to its exposed output half-port bits. -/
theorem kernel_map (v : (R.target t).Site) (j : Fin (L.hidden children ord v+W.halfBits v)) :
    sourceAddress (L.kernelWire W children ord v j) =
    piecewise j.val (L.hidden children ord v) (2+W.form.width v) (2+W.ext v) := by
  refine Fin.addCases (fun x => ?_) (fun x => ?_) j
  · simp only [PortLayout.kernelWire,Fin.append_left,sourceAddress,hiddenBase,Fin.val_castAdd,
      piecewise,ite_eq_left x.isLt]
  · have high : ¬ L.hidden children ord v + x.val < L.hidden children ord v := by omega
    simp only [PortLayout.kernelWire,Fin.append_right,sourceAddress,Fin.val_natAdd,piecewise,ite_eq_right high]
    omega

end ThreeFlat.RAM.HistoryPortMap

end OAI
