import OAI.Computability.NearSquareRoot.CRTTableBoxRun
import OAI.Computability.NearSquareRoot.FixedCandidateArrays

/-! # The ordered physical address changes of both CRT stream passes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream
open IntegerMultiplication Code DigitPacking FixedPoint

noncomputable section

abbrev Switch (n : ℕ) := Fin (Nat.clog 2 (box n).length) × Bool × ℕ

variable {n : ℕ} (h : Directory n)

def order (n : ℕ) (inv : Bool) : List (Switch n) :=
  CRTTable.switchOrder (box n).length (BoxScale.width (addressBits n)) inv

include h in
theorem fits (g : Fin (box n).length) : BoxFin.modulus (box n) g ≤ 2^CRTTable.axisWidth (box n) g :=
  (h.axisBounds _ (List.get_mem _ g)).2.2.2

/-- Permutation of flat physical indices performed by one controlled switch layer. -/
def slot (inv : Bool) (s : Switch n) : Equiv.Perm (Fin (capacity n)) :=
  let := BoxFin.modulus_neZero h
  ((index h).symm.trans (CRTTable.switchPerm _ _ (fits h) inv s)).trans (index h)

/-- The record at a source index travels with that index. -/
def step (inv : Bool) (v : Array n) (s : Switch n) : Array n := v ∘ (slot h inv s).symm

def outcome (inv : Bool) (v : Array n) : Array n :=
  bif inv then afterInverseCRT h v else route h v

private theorem fold_conjugate {T X Y : Type*} (p : T → Equiv.Perm X) (e : X ≃ Y)
    (l : List T) (x : X) :
    l.foldl (fun y t => ((e.symm.trans (p t)).trans e) y) (e x) =
      e (l.foldl (fun z t => p t z) x) := by
  induction l generalizing x with
  | nil => rfl
  | cons t l ih => simpa only [List.foldl_cons,Equiv.trans_apply,Equiv.symm_apply_apply] using ih (p t x)

private theorem fold_scatter {T X V : Type*} (p : T → Equiv.Perm X) (l : List T)
    (v : X → V) (x : X) :
    (l.foldl (fun a t => a ∘ (p t).symm) v) (l.foldl (fun y t => p t y) x) = v x := by
  induction l generalizing v x with
  | nil => rfl
  | cons t l ih =>
    simpa only [List.foldl_cons,Function.comp_apply,Equiv.symm_apply_apply] using
      ih (v ∘ (p t).symm) ((p t) x)

def destination (inv : Bool) : Equiv.Perm (Fin (capacity n)) :=
  let := BoxFin.modulus_neZero h
  bif inv then (BoxFin.crtSlotPerm h).symm else BoxFin.crtSlotPerm h

theorem fold_slot (inv : Bool) (x : Fin (capacity n)) :
    (order n inv).foldl (fun y s => slot h inv s y) x = destination h inv x := by
  let := BoxFin.modulus_neZero h
  obtain ⟨z,rfl⟩ := (index h).surjective x
  let a := BoxFin.modulus (box n)
  let w := CRTTable.axisWidth (box n)
  let act := CRTTable.switchPerm a w (fits h) inv
  calc
    _ = index h ((order n inv).foldl (fun y s => act s y) z) :=
      fold_conjugate _ (index h) _ z
    _ = index h ((bif inv then (CRT.paddedPermutation a (fun g => Fin (BoxFin.padding (box n) g))).symm
        else CRT.paddedPermutation a (fun g => Fin (BoxFin.padding (box n) g))) z) :=
      congrArg (index h) (CRTTable.boxSwitches_run h inv z)
    _ = _ := by
      let p := CRT.paddedPermutation a (fun g => Fin (BoxFin.padding (box n) g))
      cases inv
      · exact congrArg (fun x => index h (p x)) ((index h).symm_apply_apply z).symm
      · exact congrArg (fun x => index h (p.symm x)) ((index h).symm_apply_apply z).symm

/-- The complete sweep is the balanced CRT in either direction, including every padded slot. -/
theorem fold_step (inv : Bool) (v : Array n) : (order n inv).foldl (step h inv) v = outcome h inv v := by
  funext y
  have e := fold_scatter (slot h inv) (order n inv) v ((destination h inv).symm y)
  rw [fold_slot,Equiv.apply_symm_apply] at e
  cases inv <;> exact e

end
end FixedCandidate.CRTStream

end NearSquareRoot
end Computability
end OAI
