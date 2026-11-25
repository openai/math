import OAI.Computability.NearSquareRoot.SynchronizedBatchDecode
import OAI.Computability.NearSquareRoot.SynchronizedBatchPhases

/-! # Reading phase coefficients from actual emitted slot descriptors -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open Matrix IntegerMultiplication.Code SynchronizedLayers SynchronizedLayers.ScheduleProgram
  AxisWord SynchronizedBorrowing PhaseTable

noncomputable section

/-- Index in the three-table Walsh factorization. -/
def phaseRound (micro : ℕ) : Fin 3 := if micro = 3 then 0 else if micro = 5 then 1 else 2

/-- Scalar-field dispatch used after looking up an axis and a batch. -/
def phaseField {n : ℕ} (micro activeCount : ℕ) (bit : Fin 2) (pair : Fin n) (placed : ℂ) : ℂ :=
  if micro = 0 then placed else
    RoutedWalsh.table (fun s : Fin n => decide (s.val < activeCount)) (phaseRound micro) (bit,pair)

variable {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
  (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
  (bits : Address a c ≃ Fin 2 × Fin (Fintype.card (Address a c)/2))

/-- Apply the two scalar readout formulas at valid local axis and batch fields. -/
def typedPhase (precision : ℕ) (i : Fin m) (b : Fin 15) (x : Inst) (t : Tally) (p : Address a c) : ℂ :=
  let B := fiberCount a c i
  let pos := axisLayout a c spectator i p
  let q := SlotQuery.fromInst (a i) (k i) precision x
  phaseField t.length (size B b * 2^k i) (bits p).1 (bits p).2
    (placedCoefficient q (first B b) (size B b) pos.1.val (finSumFinEquiv pos.2).val)

/-- Query the local coefficient in the concrete descriptor. -/
def phaseAt (precision : ℕ) (z : SlotDescriptor) (p : Address a c) : ℂ :=
  if hi : z.1.1.length < m then
    if hb : z.1.2.1.length < 15 then
      typedPhase a c k spectator bits precision ⟨z.1.1.length,hi⟩ ⟨z.1.2.1.length,hb⟩ z.1.2.2 z.2 p
    else 1
  else 1

theorem phaseAt_encode (precision : ℕ) (i : Fin m) (b : Fin 15) (x : Inst) (t : Tally) (p : Address a c) :
    let B := fiberCount a c i
    let pos := axisLayout a c spectator i p
    phaseAt a c k spectator bits precision (encode (i,b,x),t) p =
      phaseField t.length (size B b * 2^k i) (bits p).1 (bits p).2
        (placedCoefficient (SlotQuery.fromInst (a i) (k i) precision x) (first B b) (size B b)
          pos.1.val (finSumFinEquiv pos.2).val) := by
  change phaseAt a c k spectator bits precision (encode (i,b,x),t) p =
    typedPhase a c k spectator bits precision i b x t p
  simp [phaseAt, encode, i.isLt, b.isLt]

variable (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)
  (he : Even (Fintype.card (Address a c)))

private theorem lower_phaseAt (precision : ℕ) (i : Fin m) (b : Fin 15) (x : Inst)
    (hx : x ∈ fixedWord (tally (k i))) (z : SlotDescriptor)
    (hz : z ∈ lower (encode (i,b,x))) (hk : slotKind z = .diagonal) :
    (decodeSlot a c k spectator har hborrow bits he z).matrix bits =
      diagonal (phaseAt a c k spectator bits precision z) := by
  by_cases h10 : x.1.length = 10
  · have hL : lower (encode (i,b,x)) = microcode.map (fun t => (encode (i,b,x),t)) := by
      simp [lower, encode, h10]
    rw [hL] at hz
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    have H (j : Fin 3) :
        (decodeSlot a c k spectator har hborrow bits he (encode (i,b,x),tally (2*j.val+3))).matrix bits =
          diagonal (phaseAt a c k spectator bits precision (encode (i,b,x),tally (2*j.val+3))) := by
      rw [decode_routed_phase]
      apply congrArg diagonal
      funext p
      rw [phaseAt_encode]
      fin_cases j <;> rfl
    simp only [microcode, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h|h|h|h|h|h|h|h <;> subst t
    all_goals first | contradiction | exact H 0 | exact H 1 | exact H 2
  · have hL : lower (encode (i,b,x)) = [(encode (i,b,x),[])] := by simp [lower, encode, h10]
    rw [hL,List.mem_singleton] at hz
    subst z
    have hphase : x.1.length ∈ phaseTags := by
      obtain h | h | h | h := fixedWord_tag _ hx
      · exact h
      all_goals simp [slotKind, encode, instructionKind, h] at hk
    rw [decode_direct_matrix _ _ _ _ _ _ _ _ _ h10, PhaseTable.gateMatrix_phase _ _ _ _ _ _ _ _ _ hphase precision]
    congr 1
    funext p
    rw [phaseAt_encode]
    rfl

/-- Every actual local diagonal descriptor agrees at every address with the
numeric phase lookup. -/
theorem decode_phaseAt (precision : ℕ) (z : SlotDescriptor)
    (hz : z ∈ localSlots (block (List.ofFn fun i => tally (k i)))) (hk : slotKind z = .diagonal) :
    (decodeSlot a c k spectator har hborrow bits he z).matrix bits =
      diagonal (phaseAt a c k spectator bits precision z) := by
  rw [localSlots,block_eq_typed] at hz
  obtain ⟨d,hd,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨⟨i,b,x⟩,hg,rfl⟩ := List.mem_map.mp hd
  obtain ⟨i',_,hi⟩ := List.mem_flatMap.mp hg
  obtain ⟨b',_,hb⟩ := List.mem_flatMap.mp hi
  obtain ⟨x',hx,h⟩ := List.mem_map.mp hb
  cases h
  exact lower_phaseAt a c k spectator bits har hborrow he precision i b x hx z hz hk

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
