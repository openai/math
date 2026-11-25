import OAI.Computability.NearSquareRoot.SynchronizedBatchDecode

/-! # The executable slot stream on a padded block

The setup writes the fixed-bit lowering of every batch in every axis pass.
The product of these literal slots acts by the tensor of the padded Fourier
transforms. Their serialized tags agree with their physical slot kinds.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open IntegerMultiplication.Code AxisWord SynchronizedPadding ResidueFourier

variable {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
  (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
  (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)

private theorem typed_fixed {g : Fin m × Fin 15 × Inst} (hg : g ∈ typed k) :
    g.2.2 ∈ fixedWord (tally (k g.1)) := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hg
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp hi
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact hx

private theorem slot_product {A : Type} [Monoid A] (eval : SlotDescriptor → A)
    (gate : Fin m × Fin 15 × Inst → A)
    (h : ∀ g, ((lower (encode g)).map eval).prod = gate g) (l : List (Fin m × Fin 15 × Inst)) :
    ((localSlots (l.map encode)).map eval).prod = (l.map gate).prod := by
  induction l with
  | nil => simp [localSlots]
  | cons g l ih =>
    simp only [List.map_cons, List.prod_cons]
    change (((lower (encode g) ++ localSlots (l.map encode)).map eval).prod) = gate g * (l.map gate).prod
    rw [List.map_append, List.prod_append, h, ih]

/-- Act on all spectator fibers in the fifteen disjoint batches for each axis,
using the generated microinstructions in their actual order. -/
theorem localSlots_correct
    (bits : Address a c ≃ Fin 2 × Fin (Fintype.card (Address a c) / 2))
    (he : Even (Fintype.card (Address a c))) (hwrap : ∀ i, 2 * a i - 1 ≤ 2 ^ k i)
    (hspec : ∀ i, 8 ≤ Fintype.card (Spectators a c i)) :
    let w := localSlots (block (List.ofFn fun i => tally (k i)))
    (w.map (fun r => (decodeSlot a c k spectator har hborrow bits he r).matrix bits)).prod =
        tensorMatrix (fun i => axisPadding (b := Fin (c i)) (axisMatrix (a i))) ∧
      ∀ r ∈ w, (decodeSlot a c k spectator har hborrow bits he r).kind = slotKind r := by
  dsimp only
  rw [block_eq_typed]
  constructor
  · exact (slot_product _ _ (decode_lower_prod a c k spectator har hborrow bits he) (typed k)).trans
      (typed_prod a c k spectator har hborrow hwrap hspec)
  · intro r hr
    obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hg
    exact decode_lower_kind a c k spectator har hborrow bits he x (typed_fixed k hx) r hr

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
