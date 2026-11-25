import OAI.Computability.BorderVNP.CubeScatterTrialPrefix
import OAI.Computability.BorderVNP.CubeScatterVisits
import OAI.Computability.BorderVNP.CubeISAOwnedSingleRowModel

/-! # Feeding native singleton trials from their ordered row interval -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.SingleRowData

open RoutingISA Physical Physical.Owned VPVNP.BurstRAM

variable {w n d blocks width : ℕ} (D : SingleRowData n d (blocks*width))

/-- Total label-indexed input for the singleton row machine obtained from an
assignment on the genuine singleton slots. Only pairs with an equal coordinate
reach a singleton visit. -/
def extendSlots (single : SingleSlot n d blocks width → Bool) (uv : Label (n+1) d × Label (n+1) d)
    (j : Fin (blocks*width)) : Bool :=
  if h : ¬∀ i, uv.1 i ≠ uv.2 i then single (⟨uv,h⟩,j) else false

/-- Restricting the extended bits to a physical singleton recovers its exact input word. -/
theorem extendSlots_apply (single : SingleSlot n d blocks width → Bool) (z : SingleSlot n d blocks width) :
    extendSlots single z.1.val z.2 = single z := by
  simp only [extendSlots,dite_eq_left z.1.property]

/-- The prescribed bit of one genuine singleton slot. -/
def slotBit (z : SingleSlot n d blocks width) : Bool := D.value z.1.val z.2

/-- The crossing words consumed by this trial. Diagonal bits are private. -/
def trialWords (t : Fin (singlePairTrials n d)) : List Bool :=
  if D.selected t ∧ D.left ≠ D.right then D.bits t else []

/-- The ordered singleton words actually copied by this row, empty on the diagonal. -/
def crossingWords := if D.left = D.right then [] else (singleVisits blocks width D.axis D.left D.right).map D.slotBit

/-- Filtering one trial's slot offsets emits precisely the selected singleton bits. -/
theorem candidate_bits (t : Fin (singlePairTrials n d)) :
    (((List.finRange (blocks*width)).filterMap (singleTrial D.axis D.left D.right t)).map D.slotBit) =
      if D.selected t then D.bits t else [] := by
  by_cases ok : D.selected t
  · rw [ite_eq_left ok]
    let f := fun j : Fin (blocks*width) => (singleOrderedEquiv blocks width D.axis D.left D.right (⟨t,ok⟩,j)).val
    have eq := (List.filterMap_eq_map_iff_forall_eq_some (f := singleTrial D.axis D.left D.right t)
      (g := f) (l := List.finRange (blocks*width))).mpr (fun j _ => by simp only [singleTrial,dite_eq_left ok]; rfl)
    rw [eq,List.map_map,bits,List.ofFn_eq_map]
    rfl
  · have skipped : (List.finRange (blocks*width)).filterMap (singleTrial D.axis D.left D.right t) = ([] : List (SingleSlot n d blocks width)) :=
      List.filterMap_eq_nil_iff.mpr (fun _ _ => by simp only [singleTrial,dite_eq_right ok])
    rw [ite_eq_right ok,skipped,List.map_nil]

private theorem all_words : (List.finRange (singlePairTrials n d)).flatMap D.trialWords = D.crossingWords := by
  by_cases eq : D.left = D.right
  · simp [crossingWords,eq,trialWords]
  · rw [crossingWords,ite_eq_right eq,singleVisits,List.map_flatMap]
    apply List.flatMap_congr
    intro t _
    rw [D.candidate_bits]
    by_cases yes : D.selected t
    · rw [trialWords,ite_eq_left ⟨yes,eq⟩,ite_eq_left yes]
    · rw [trialWords,ite_eq_right (fun h => yes h.1),ite_eq_right yes]

/-- The native cursor counts exactly the preceding accepted off-diagonal bit intervals. -/
theorem before_cursor (m : Memory w) (k : ℕ) (hk : k ≤ singlePairTrials n d) :
    (D.before m k).1 = D.crossing+(trialPrefix D.trialWords k).length := by
  induction k with
  | zero => simp [before,trialPrefix]
  | succ k ih =>
    let t : Fin (singlePairTrials n d) := ⟨k,hk⟩
    have tv : t.val = k := rfl
    have prev := ih (by omega)
    rw [trialPrefix_step _ t]
    by_cases ok : D.selected t
    · rw [D.before_visit m t ok]
      by_cases eq : D.left=D.right
      · have skip : ¬ (D.selected t ∧ D.left ≠ D.right) := fun h => h.2 eq
        simp only [crossWords,ite_eq_left eq,trialWords,ite_eq_right skip,List.append_nil,Nat.add_zero,tv,prev]
      · have go : D.selected t ∧ D.left ≠ D.right := ⟨ok,eq⟩
        simp only [crossWords,ite_eq_right eq,trialWords,ite_eq_left go,List.length_append,bits,List.length_ofFn,tv,prev,Nat.add_assoc]
    · rw [D.before_skip m t ok]
      simpa only [trialWords,ok,false_and,ite_false,List.append_nil] using prev

/-- At the row boundary the cursor has consumed the complete ordered singleton list. -/
theorem final_cursor (m : Memory w) : (D.before m (singlePairTrials n d)).1 = D.crossing+D.crossingWords.length := by
  simpa only [trialPrefix_full,all_words] using D.before_cursor m _ le_rfl

private theorem single_streams (same : Bool) (bs : List Bool) :
    (singlePositions same bs).filterMap Position.selectorBit = [] ∧
      (singlePositions same bs).filterMap Position.crossBit = if same then [] else bs := by
  cases same <;> induction bs with
    | nil => simp [singlePositions]
    | cons x xs ih => simp_all [singlePositions,List.filterMap_cons,Position.selectorBit,Position.crossBit]

/-- An ordered shared interval and separated singleton banks prepare all native
trials. The diagonal needs only destination separation because its bits are private. -/
theorem preparedRow_of_streams (src : Set ℕ) (m : Memory w) (stream : Resident src m D.crossing D.crossingWords)
    (dest : ∀ (t : Fin (singlePairTrials n d)), D.selected t → ∀ j < blocks*width,
      D.address t+j ∉ src ∧ D.address t+j < 2^w) : D.PreparedRow src m := by
  rw [← D.all_words] at stream
  intro t ok
  let c : Cursor := ⟨D.selector,(D.before m t.val).1,D.address t⟩
  have ss := single_streams (decide (D.left=D.right)) (D.bits t)
  have sel : Resident src m c.selector ((D.positions t).filterMap Position.selectorBit) :=
    ss.1 ▸ Resident.nil src m c.selector
  have eq : (D.positions t).filterMap Position.crossBit = D.trialWords t := by
    rw [positions,ss.2]
    by_cases he : D.left=D.right <;> simp [trialWords,he,ok]
  have cr : Resident src m c.crossing ((D.positions t).filterMap Position.crossBit) := by
    change Resident src m (D.before m t.val).1 _
    rw [eq,D.before_cursor m t.val t.isLt.le]
    exact Resident.atTrial D.trialWords t stream
  exact prepared_of_streams src (D.positions t) c m sel.bits cr.bits sel.addresses cr.addresses
    (fun j hj => dest t ok j (by simpa only [positions,singlePositions,List.length_map,bits,List.length_ofFn] using hj))

end Cube.Scatter.SingleRowData

end BorderVNP
end Computability
end OAI
