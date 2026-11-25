import OAI.ThreeFlat.Diagonal.CompressorNativeTags
import OAI.ThreeFlat.Diagonal.CompressorSweepSimulation

namespace OAI
/-! # The native first-free tag row agrees with the graph's canonical offset scan -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.Compression RAM.DescriptorExpr
open scoped Fin.NatCast
variable {V : Type*} {w k d t : ℕ}

def tagEmb (fit : t ≤ w) : BitWord t ↪ Word w where
  toFun := tagWord fit
  inj' := by
    intro a b eq
    have same : (tagWord fit a).val = (tagWord fit b).val := congrArg (fun x : Word w => x.val) eq
    exact (tagOrdinal t).injective (Fin.ext same)

theorem tagChoices (fit : t ≤ w) :
    (List.ofFn fun i : Fin (2^t) => (i.val : Word w)) =
      (List.ofFn (tagOrdinal t).symm).map (tagEmb fit) := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Fin.ext
  change i.val % 2^w = (tagOrdinal t ((tagOrdinal t).symm i)).val
  rw [Equiv.apply_symm_apply]
  exact Nat.mod_eq_of_lt (i.isLt.trans_le (Nat.pow_le_pow_right (by decide) fit))

theorem offset_val {T : TagColumns w k 1} {G : SlotGraph V d} {shift : V × Fin d → BitWord t}
    {f : V → BitWord t} {fit : t ≤ w} {addr : V → Word w} {pub : Fin k → Word w}
    {m : Memory w} {p : Word w} (R : TagReads T G shift f fit addr pub m (fun _ => p))
    (x : V) (ptr : p - T.offsets.eval pub m (fun _ => p) = addr x) (one : (1 : Word w) ≠ 0) :
    (offsetRow T d t).eval pub m (fun _ => p) =
      tagWord fit (Ordered.pick (Ordered.tagBan G shift x f) 0 (List.ofFn (tagOrdinal t).symm)) := by
  let v : Term w k 1 := .binary .sub (.result 0) T.offsets
  have hv : v.eval pub m (fun _ => p) = addr x := by simpa [v,Term.eval,BinaryOp.eval] using ptr
  have bans : ((Ordered.directions d).flatMap (tagDirection T v)).map
      (fun z => z.eval pub m (fun _ => p)) = (Ordered.tagBan G shift x f).map (tagEmb fit) := by
    simp only [Ordered.tagBan,List.map_flatMap]
    apply congrArg (List.flatMap · (Ordered.directions d))
    funext i
    exact eval_tagDirection R v x hv i
  rw [offsetRow,eval_firstFree one]
  change Ordered.pick _ _ _ = _
  rw [bans,tagChoices fit,← tagWord_zero (t:=t) fit]
  exact pick_map (tagEmb fit) (Ordered.tagBan G shift x f) 0 (List.ofFn (tagOrdinal t).symm)

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
