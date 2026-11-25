import OAI.Computability.BorderVNP.PackedFrozenSchemaLeaves
import OAI.Computability.BorderVNP.PackedFrozenSchemaMeasures
import OAI.Computability.BorderVNP.PackedFrozenHistoryCapacity
import OAI.Computability.BorderVNP.PackedFrozenBottomSeed

/-! # Local roster, scalar-tag and payload capacities of each concrete immutable block -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing CellSparse CellPacketGeometry.History Shortening.PublicCapacity Shortening.StaticRows
open PackedHistoryCircuit.Normalized
open scoped Classical

private theorem constant_sum {A : Type*} (L : List A) (c : ℕ) :
    (L.map fun _ => c).sum = L.length*c := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]; omega

private theorem nine_words {R : Type} (rs : List R) (w : ℕ) :
    tagWords (NineWords.schema rs w) = rs.length*9 := by
  simp only [tagWords,NineWords.schema,List.length_ofFn,constant_sum]

private theorem hook_words (old D w : ℕ) :
    tagWords (HookTape.schema old D w) = Fintype.card (InheritedHook.Row old D)*9 := by
  change ((HookTape.rows old D).map fun _ => 9).sum = _
  rw [constant_sum]
  exact congrArg (· * 9) (hook_length w old D)

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- For each measurement, the actual retained, seed-main and hook block has linear
sparse volume. Only its bit-level payload introduces a factor equal to the word width. -/
theorem fresh_measure_le (M : Measure) (old : Shape) (np n w : ℕ) (A : Type) [Fintype A]
    (ports : np ≤ old.sites) (arity : Fintype.card A = n) :
    M.count (freshFormat e A old.edges np w) ≤
      roundSlots e (0,false)*physicalRows (old.sew e n)*(w+1) := by
  let cap := roundSlots e (0,false)*physicalRows (old.sew e n)
  have hr := (round_cards e (0,false) old np w n A ports arity).1
  have ht := (round_cards e (0,false) old np 1 n A ports arity).2
  have hb := (round_cards e (0,false) old np w n A ports arity).2
  have upper : cap ≤ cap*(w+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change _ ≤ cap*(w+1)
  cases M with
  | slots =>
    exact hr.trans upper
  | payload =>
    exact hb.trans (Nat.mul_le_mul_left cap (Nat.le_succ w))
  | rows =>
    change (((LayerRows.schema old.edges D np w).append
      ((Birth.schema e (0,false) A w).append (HookTape.schema old.edges D w))).rows.length) ≤ _
    rw [Schema.append_length,Schema.append_length,layer_length,birth_length,hook_length]
    apply le_trans _ upper
    simpa only [RoundRows,Fintype.card_sum] using hr
  | words =>
    change tagWords ((LayerRows.schema old.edges D np w).append
      ((Birth.schema e (0,false) A w).append (HookTape.schema old.edges D w))) ≤ _
    rw [Schema.append_words,Schema.append_words,hook_words]
    have oldWords : tagWords (LayerRows.schema old.edges D np w) = Fintype.card (Layer.Row old.edges D np)*9 :=
      (nine_words _ w).trans (congrArg (· * 9) (layer_length w old.edges D np))
    rw [oldWords]
    apply (Nat.add_le_add_left (Nat.add_le_add_right (birth_tagWords_le w e (0,false) A) _) _).trans
    apply le_trans _ upper
    simpa only [RoundData,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,Nat.mul_one,cap] using ht

/-- The actual subdivision emits nine tagged words per reserved endpoint, port or relay.
All four measurements are bounded by the resulting physical site and edge count. -/
theorem subdivision_measure_le (M : Measure) (s : Shape) (np extra w : ℕ) (ports : np ≤ s.sites) :
    M.count (Format.subdivision s.edges np extra w) ≤ 18*physicalRows (s.subdivide extra)*(w+1) := by
  let r := Fintype.card (Subdivision.Gates.Row s.edges np extra)
  let cap := physicalRows (s.subdivide extra)
  have h : r ≤ 2*cap := subdivision_card s np extra ports
  have words : r*9 ≤ 18*cap := (Nat.mul_le_mul_right 9 h).trans_eq (by ring)
  have upper : 18*cap ≤ 18*cap*(w+1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  change _ ≤ 18*cap*(w+1)
  cases M with
  | slots => exact h.trans ((by omega : 2*cap ≤ 18*cap).trans upper)
  | rows => exact (subdivision_length w s.edges np extra).le.trans (h.trans ((by omega : 2*cap ≤ 18*cap).trans upper))
  | words =>
    have H : tagWords (Subdivision.Gates.tapeSchema s.edges np extra w) = r*9 :=
      (nine_words _ w).trans (congrArg (· * 9) (subdivision_length w s.edges np extra))
    exact H.le.trans (words.trans upper)
  | payload =>
    change Fintype.card (Subdivision.Gates.Row s.edges np extra × Fin 9 × Fin w) ≤ _
    simp only [Fintype.card_prod,Fintype.card_fin,←Nat.mul_assoc]
    exact (Nat.mul_le_mul_right _ words).trans (Nat.mul_le_mul_left _ (Nat.le_succ w))

namespace Seed

open Cover DeckGrid Diagonal.ExternalSew

variable {q depth qe qa : ℕ} (n r : ℕ)
variable (order : Fin (GridHosts.tileCount q depth) ≃ (Fin q → Deck (depth+2)))
variable (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe) (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa)
variable (copies holes w H : ℕ)
local notation3 "rs" => Seed.rows n r order position channels groups copies
local notation3 "V" => GridHosts.tileCount q depth
local notation3 "rate" => 2+2*Fintype.card (Direction q)

omit [NeZero D] in
/-- Each of the four base measurements comes from the actual routed seed tape. Only the
explicitly reserved holes add to the row count; they contain no scalar payload. -/
theorem bottom_measure_le (M : Measure) (vacant : holes ≤ H*V) :
    M.count (Format.bottom rs holes w) ≤ (9*(rate)+H)*(w+1)*V := by
  have row := row_slots n r order position channels groups copies holes
  have bits := payload_slots n r order position channels groups copies holes w
  have scalars := payload_slots n r order position channels groups copies holes 1
  have capacity : V*(rate)+holes ≤ (9*(rate)+H)*V := by
    nlinarith only [vacant,Nat.zero_le (V*(rate))]
  have full : (9*(rate)+H)*V ≤ (9*(rate)+H)*(w+1)*V :=
    Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  cases M with
  | slots => exact row.trans (capacity.trans full)
  | rows => exact (bottom_length rs holes w).le.trans (row.trans (capacity.trans full))
  | words =>
    change tagWords (Bottom.schema rs holes w) ≤ _
    rw [bottom_tagWords]
    rw [Bottom.card_payload,Nat.mul_one] at scalars
    apply scalars.trans
    nlinarith only [full,Nat.zero_le (H*V)]
  | payload =>
    apply bits.trans
    nlinarith only [Nat.zero_le (H*V),Nat.zero_le (H*w*V),Nat.zero_le ((rate)*V)]

end Seed

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
