import OAI.Computability.BorderVNP.PackedSewnRecordEmitter
import OAI.Computability.BorderVNP.PackedFrozenSchemaBounds
import OAI.Computability.BorderVNP.PackedTerminalRoutingCapacity

/-! # Physical row and immutable field counts of the exterior sewing tape

Every candidate fragment reserves its clamp and equality record slots. The
six clamp tags and nine equality tags are charged separately in the roster,
while both records read the same nine-word scalar bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open CellPacketGeometry.History Shortening.PublicCapacity PackedHistoryCircuit.Normalized.SelectedSchedule
open private tags count count_le from OAI.Computability.BorderVNP.PackedSewnRecordEmitter

/-- The chronological roster has two opcode slots at every possible fragment. -/
theorem schema_length (n w : ℕ) : (schema n w).rows.length = 2*n := by
  simp [schema,List.length_flatMap,Nat.mul_comm]

/-- The reserved row pin type has exactly the roster length. -/
theorem row_card (n : ℕ) : Fintype.card (Row n) = 2*n := by simp [Row,Nat.mul_comm]

/-- All immutable scalar bits use the one shared nine-word bank per fragment. -/
theorem payload_card (n w : ℕ) : Fintype.card (Payload n w) = 9*n*w := by simp [Payload]; ring

/-- The roster includes six clamp tags followed by nine equality tags for each candidate. -/
theorem schema_tagWords (n w : ℕ) : tagWords (schema n w) = 15*n := by
  have h (xs : List (Fin n)) : ((xs.flatMap (fun i => [(i,false),(i,true)])).map
      (fun r => (tags r.2).length)).sum = 15*xs.length := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.map_nil,
        tags,List.length_ofFn,count,Bool.false_eq_true,ite_false,ite_true,List.sum_cons,List.sum_nil,
        List.length_cons] at ih ⊢
      omega
  exact (h (List.finRange n)).trans (congrArg (15*·) (@List.length_finRange n))

/-- The appended exterior section fits the same nine-field and word-width limits as final bindings. -/
theorem schema_bounded (n w : ℕ) {cap W : ℕ} (nine : 9≤cap) (width : w≤W) :
    (Format.ofSchema (schema n w)).Bounded cap W := by
  refine ⟨(schema_length n w).trans (row_card n).symm,fun r => ?_,fun _ => width⟩
  change (tags r.2).length ≤ cap
  simpa only [tags,List.length_ofFn] using (count_le r.2).trans nine

/-- Exact increment of each frozen format measure when sewing is appended to the true predecessor history. -/
theorem append_count (S : Format) (n w : ℕ) (M : Measure) :
    M.count (S.append (Format.ofSchema (schema n w))) = M.count S +
      match M with
      | .slots | .rows => 2*n
      | .words => 15*n
      | .payload => 9*n*w := by
  rw [M.append]
  congr 1
  cases M
  · exact row_card n
  · exact schema_length n w
  · exact schema_tagWords n w
  · exact payload_card n w

/-- The actual old site lookup rows, both directions of each old cable, and all six
reserved original team/tile fragments fit the selected terminal routing rectangle. -/
theorem fragment_slots_le (s : Shape) (cells original replicas tiles : ℕ) :
    s.sites + (2*s.edges + 6*(replicas+1)*tiles) + 1 ≤ routingRows s cells original ((replicas+1)*tiles) := by
  unfold routingRows CellAddressCircuit.count
  rw [Nat.mul_assoc 6]
  omega

/-- Additional source volume of the actual sewn format in the history template. -/
theorem schema_volume (s : Shape) (cells original replicas tiles w : ℕ) :
    let n := 2*s.edges+6*(replicas+1)*tiles
    (schema n w).rows.length + tagWords (schema n w) ≤ 17*routingRows s cells original ((replicas+1)*tiles) ∧
      Fintype.card (Payload n w) ≤ 9*routingRows s cells original ((replicas+1)*tiles)*w := by
  intro n
  have total := fragment_slots_le s cells original replicas tiles
  have h : n ≤ routingRows s cells original ((replicas+1)*tiles) := by dsimp [n]; omega
  rw [schema_length,schema_tagWords,payload_card]
  exact ⟨(by omega),Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)⟩

end Packing.Inherited.FrozenTape.Sewn

end BorderVNP
end Computability
end OAI
