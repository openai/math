import OAI.Hierarchy.TaggedWideOrderCore
import OAI.Hierarchy.TaggedPassExit
import Mathlib.Data.Fin.Tuple.Take

namespace OAI
/-! # Reading physical rows from the retained pack prefix -/

noncomputable section
namespace Hierarchy.Tagged.WideOrder

open ThreeFlat Routing SortNetwork
open Radix
open scoped Classical

variable {w : ℕ}

/-- The actual outgoing scatter reads exactly the retained rectangular prefix,
in pack-major, lane-minor order. -/
theorem leave_before (s : PassShape) (room : s.packBits ≤ 2*s.digitBits) (real : Fin w)
    (X : Records s.globalHeight (s.pack*w)) :
    (List.ofFn (fun i : Fin s.nextRows => fun b : Fin w =>
      RadixStage.staticRead s.leave (pack X) (i,b))).filter (fun v => v real) =
      before s.packs real X := by
  let out (i : Fin s.nextRows) : Bits w := fun b => RadixStage.staticRead s.leave (pack X) (i,b)
  have dims := s.exact_packs room
  have fit : s.packs ≤ 2^s.globalHeight := Nat.le_pow_clog (by decide : 1<2) _
  have access (r : Fin s.packs) (j : Fin s.pack) :
      out (Fin.cast dims (finProdFinEquiv (r,j))) = lane (X (r.castLE fit)) j := by
    funext b
    let i := Fin.cast dims (finProdFinEquiv (r,j))
    have hp : 0<s.pack := Nat.two_pow_pos _
    have div : i.val / s.pack = r.val := by
      change (j.val+s.pack*r.val)/s.pack=r.val
      rw [Nat.add_mul_div_left j.val r.val hp, Nat.div_eq_of_lt j.isLt,Nat.zero_add]
    have rem : i.val % s.pack = j.val := by
      change (j.val+s.pack*r.val)%s.pack=j.val
      rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]
    have inside : i.val/s.pack < 2^s.globalHeight := div.trans_lt (r.isLt.trans_le fit)
    have wire : s.leave (i,b) = .inl ((Fintype.equivFin (Payload s.globalHeight (s.pack*w)))
        (r.castLE fit,finProdFinEquiv (j,b))) := by
      simp only [PassShape.leave,dite_eq_left inside]
      apply congrArg Sum.inl
      apply congrArg (Fintype.equivFin _)
      apply Prod.ext (Fin.ext div)
      exact congrArg finProdFinEquiv (Prod.ext (Fin.ext rem) rfl)
    change Sum.elim (pack X) id (s.leave (i,b))=_
    rw [wire]
    simp [pack,lane,Function.uncurry]
  have flatten (v : Fin (s.packs*s.pack) → Bits w) : List.ofFn v =
      (List.ofFn (fun i : Fin s.packs =>
        List.ofFn (fun j : Fin s.pack => v (finProdFinEquiv (i,j))))).flatten := by
    simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm s.pack, Nat.add_comm]
      using List.ofFn_mul v
  change (List.ofFn out).filter _ = _
  rw [List.ofFn_congr dims.symm out, flatten]
  simp_rw [access]
  unfold before
  rw [← Fin.ofFn_take_eq_take_ofFn fit id]
  simp [List.filter_flatten, List.flatMap, live, Fin.take, Function.comp_def]

/-- The physical wide sort followed by its outgoing scatter produces an
ordered live row list and preserves the input sequence in every digit bucket. -/
theorem pass_read (s : PassShape) (room : s.packBits ≤ 2*s.digitBits)
    (digit : Fin s.digitBits → Fin w) (real dummy : Fin w) (X : Records s.globalHeight (s.pack*w))
    (same : Homogeneous (Nat.two_pow_pos _) digit real X)
    (flags : ∀ i j, lane (X i) j dummy = !(lane (X i) j real))
    (support : ∀ i : Row s.globalHeight, lane (X i) ⟨0,Nat.two_pow_pos _⟩ real = true →
      i.val < s.packs) :
    let out := SortedBlock.stable (s.wideDigit digit dummy) X
    let rows := (List.ofFn (fun i : Fin s.nextRows => fun b : Fin w =>
      RadixStage.staticRead s.leave (pack out) (i,b))).filter (fun v => v real)
    rows.Pairwise (fun a b => SortedBlock.readKey digit a ≤ SortedBlock.readKey digit b) ∧
      ∀ a, bucket (SortedBlock.readKey digit) a rows =
        bucket (SortedBlock.readKey digit) a (observed real X) := by
  let hp : 0 < s.pack := Nat.two_pow_pos _
  dsimp only
  simp only [leave_before s room]
  change (before s.packs real (SortedBlock.stable (order hp digit dummy) X)).Pairwise _ ∧ _
  have keep := trim real (SortedBlock.stable (order hp digit dummy) X)
    (sorted_support hp digit real dummy X same flags support)
  change _ ∧ ∀ a, bucket (SortedBlock.readKey digit) a
    (before s.packs real (SortedBlock.stable (order hp digit dummy) X)) = _
  rw [keep]
  exact ⟨sorted hp digit real dummy X same flags, buckets hp digit real dummy X same flags⟩


end Hierarchy.Tagged.WideOrder

end
end OAI
