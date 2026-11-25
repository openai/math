import OAI.Computability.NearSquareRoot.SynchronizedRowMembership
import OAI.Computability.NearSquareRoot.SynchronizedBoxRow

/-! # Exact local cases of an emitted permutation slot -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication.Code SynchronizedBlocks SynchronizedLayers SynchronizedLayers.ScheduleProgram AxisWord

/-- Each permutation is either a direct bit permutation from the local transform or
one of the two routes around a placed half-Walsh. The local axis and batch are
the actual typed indices used to generate its descriptor. -/
theorem local_permutation_cases {m : ℕ} (w : Fin m → ℕ) (z : SlotDescriptor)
    (hz : z ∈ localSlots (block (List.ofFn fun i => tally (w i))))
    (hk : slotKind z = .permutation) :
    ∃ (i : Fin m) (b : Fin 15) (op : Inst), op ∈ fixedWord (tally (w i)) ∧
      z.1 = encode (i,b,op) ∧
      ((z.2=[] ∧ (op.1.length=0 ∨ op.1.length=18)) ∨
        (op.1.length=10 ∧ (z.2=tally 1 ∨ z.2=tally 8))) := by
  obtain ⟨d,hd,hz⟩ := List.mem_flatMap.mp hz
  rw [block_eq_typed] at hd
  obtain ⟨⟨i,b,op⟩,hg,rfl⟩ := List.mem_map.mp hd
  obtain ⟨i',_,hi⟩ := List.mem_flatMap.mp hg
  obtain ⟨b',_,hb⟩ := List.mem_flatMap.mp hi
  obtain ⟨x,hx,h⟩ := List.mem_map.mp hb
  cases h
  refine ⟨i,b,op,hx,?_⟩
  by_cases ht : op.1.length = 10
  · rw [show lower (encode (i,b,op)) = microcode.map (fun t => (encode (i,b,op),t)) by simp [lower,encode,ht]] at hz
    obtain ⟨t,hm,rfl⟩ := List.mem_map.mp hz
    refine ⟨rfl,Or.inr ⟨ht,?_⟩⟩
    simp only [microcode,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with h|h|h|h|h|h|h|h <;> subst t <;> simp_all [slotKind,microKind]
  · rw [show lower (encode (i,b,op)) = [(encode (i,b,op),[])] by simp [lower,encode,ht],List.mem_singleton] at hz
    subst z
    refine ⟨rfl,Or.inl ⟨rfl,?_⟩⟩
    by_contra! hn
    simp [slotKind,encode,instructionKind,hn.1,hn.2] at hk
    by_cases h14 : op.1.length = 14 <;> simp [ht,h14] at hk

theorem directed_permutation_cases {k : ℕ} {dir : Bool} {r : Bool × Row SlotDescriptor}
    (hr : r ∈ directedPlan (dir,tally k)) (hperm : r.2.1 = kindCode .permutation)
    (j : Fin ((CoprimeBox.box k).length/4)) {z : SlotDescriptor} (hz : readBlock r.2 j.val = some z) :
    ∃ (i : Fin (count j)) (b : Fin 15) (op : Inst),
      op ∈ fixedWord (tally (expAt (CoprimeBox.box k) j i)) ∧ z.1 = encode (i,b,op) ∧
      ((z.2=[] ∧ (op.1.length=0 ∨ op.1.length=18)) ∨
        (op.1.length=10 ∧ (z.2=tally 1 ∨ z.2=tally 8))) := by
  obtain ⟨hl,hk⟩ := directed_read_spec hr j hz
  exact local_permutation_cases (expAt (CoprimeBox.box k) j) z hl (kindCode_injective (hk.trans hperm))

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
