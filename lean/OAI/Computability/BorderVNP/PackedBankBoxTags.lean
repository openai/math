import OAI.Computability.BorderVNP.PackedBankBoxPhysical
import OAI.Computability.BorderVNP.DiagonalTaggedRound
import OAI.Computability.BorderVNP.ParseBatchBitCounts

/-! # Exact paid-entry tags at a physical sewn site

The tagged polynomial-ring round carries an occurrence of the gadget label
of each selected one-copy matrix address. This is the same address that the
merged sparse box reports, irrespective of the value after specialization.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidPhysical

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals
open Diagonal.CellEntries
open scoped Classical

variable {D m : ℕ} [NeZero D] {E : Type*} [Field E] (e : PaidIdentity E D m)
    {P : Type*} {bits : P → ℕ} {Param Gadget : Type*} (src : Pack D P bits (Entry Param Gadget))
    (field : src.layout.Tables E) {A : Type} [Fintype A] (bin : src.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (positive : src.layout.Edge → Bool) (first : Fin D × Bool)
    (q : ProfileCounts e (blocks src.layout bin perm m))

/-- The true factor in the tagged combining step at this paid site is the product of
the gadget events at the actual addresses reported by the sparse-box directory. -/
theorem tagged_read (position : e.Entry → Gadget) (s : A) (a : Fin e.count) (v : (e.net a).Site)
    (y : (roundTags src bin perm e position positive first q).layout.Assignment) (ports : Ports bits) :
    let p : Pack D P bits E := ⟨src.layout,field⟩
    let out := roundTags src bin perm e position positive first q
    out.layout.read out.table y ports (site e p bin perm positive first q s a v) =
      ∏ i : Fin ((q s).val a), gadget (Param := Param) (position (PaidBox.selectedEntry e a v (q s).val
        (profileWires e p bin perm positive first q s y) i)) := rfl

/-- Expanding the paid-site observation list never toggles the assignment sign. -/
theorem observed_sign {n : ℕ} (ids : Fin n → ℕ) :
    ((List.ofFn fun i => (false,some (ids i))).map Prod.fst).foldl Bool.xor false = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.ofFn_succ,List.map_cons,List.foldl_cons,Bool.xor_self] using ih (fun i => ids i.succ)

private theorem observed_ids {n : ℕ} (ids : Fin n → ℕ) :
    (List.ofFn fun i => (false,some (ids i))).filterMap Prod.snd = List.ofFn ids := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.ofFn_succ,ih]

open private count_ofFn_sum from OAI.Computability.BorderVNP.ParseBatchBitCounts in
/-- The natural-ID tally of the actual sparse gadget events is the gadget component
of the tagged product at each original position. An injective numbering permits the
paid entries to be merged with other kinds of gadgets in the shared count namespace. -/
theorem observed_count {Param Gadget : Type*} {n : ℕ} (pos : Fin n → Gadget) (number : Gadget ↪ ℕ)
    (g : Gadget) :
    ((List.ofFn fun i => (false,some (number (pos i)))).filterMap Prod.snd).count (number g) =
      (counters (∏ i, gadget (Param := Param) (pos i))).2 g := by
  classical
  rw [observed_ids, count_ofFn_sum, counters_prod (fun i => gadget (Param := Param) (pos i))
    (fun _ => WithZero.coe_ne_zero), counters_passed, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [gadget,counters_passed,Finsupp.single_apply,number.injective.eq_iff]

end Packing.PaidPhysical

end BorderVNP
end Computability
end OAI
