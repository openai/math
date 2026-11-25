import OAI.Computability.BorderVNP.PackedHistoryGeometryBranch
import OAI.Computability.BorderVNP.PackedRoutingCompiled

/-! # The routed sparse memory image for each accepted original history

The terminal emitter writes cable triples, source and destination offsets, private and
live pairs, and the remaining public output words. The physical prefix produces those
arrays on the very same path that reads the chosen original pack history.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork RoutingISA RoutingISA.Evaluator GeometryFrameEncoding
open Shortening.Adaptive Packing Packing.RoutingOutputs DiagonalResidueRAM ParseBatchSort

variable {s m n c d k b j a o : ℕ} {Z : Type*} [Fintype Z]

/-- The full routing word emitter, sharing the single guard already computed by the public
history circuit. Selecting its word wires costs zero gates. -/
noncomputable def routingEmitter (F : CellAddressCircuit.Fields s m n c d k b Z) (hk : k ≤ b)
    (old : Fin j → Fin s) (ports : Fin a → Fin n) (rest : VerifierNetwork.Frame Z (Outputs o b)) :
    VerifierNetwork.Frame Z (Fin (m*3+(RoutingOutputs.count m c j a+o)) × Fin b) := (full F hk old ports rest).select Sum.inl

variable {K T reserve W : ℕ} {A : ℕ → Type*} {V G : ℕ → Type} [∀ i, Fintype (V i)] [∀ i, Fintype (G i)]
variable {X : Type*} [Fintype X]

set_option maxHeartbeats 950000 in
/-- The row image, exact array of remaining public words, and surviving low-memory data
of every complete native prefix agree with the terminal state of the unique original pack
history. Each true private substitution is counted exactly once at the physical reader. -/
theorem bounded_routing_images (epoch : ∀ i, (Fin K → A i) → ProfileSum (A (i+1)))
    (good : ∀ i, A i → Prop) (closed : Capacity.Closed (outerSystem T epoch) good)
    (leaf : {v // good 0 v}) (C : Codec (Capacity.restrict (outerSystem T epoch) good closed) G)
    (rep : Represents A V) (steps : Steps K T V G) (correct : LocalCorrect C (fun i z v => rep i z v.val) steps)
    (bottom : VerifierNetwork.Frame X (V 0)) (x : X → Bool) (base : rep 0 (bottom.eval x) leaf.val)
    (widths : ℕ → ℕ) (order : ∀ i, G i ≃ Fin (widths i)) (fit : broadcastWidth K widths T ≤ reserve)
    (F : CellAddressCircuit.Fields s m n c d k b ((X ⊕ Fin reserve) ⊕ V T)) (hk : k ≤ b) (hb : b ≤ W)
    (old : Fin j → Fin s) (ports : Fin a → Fin n) (rest : VerifierNetwork.Frame ((X ⊕ Fin reserve) ⊕ V T) (Outputs o b))
    (body : Code) (guesses : ℕ) (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (mem : Memory W)
    (time dest : ℕ) (word : Fin reserve → Bool) {resident : (Fin guesses → Bool) → Memory W → Prop} :
    let hist := compile steps T le_rfl (repeatLeaf K bottom T)
    let ord := broadcastOrder K widths order T
    let ok := validProfile ord fit (fun g => hist.eval (Sum.elim x g) (.inr ()) = true) word
    let emit := routingEmitter F hk old ports rest
    let accepted := acceptedOuterBounded epoch good closed leaf C rep steps correct bottom x base
    let E := acceptedBroadcastOfEquiv ord fit _ accepted
    ProfilePaths body guesses pub mac bank mem ok time dest (emittedWords hist ord fit emit x word) resident →
    (Nonempty (Returns body pub mac bank mem) ↔ ∃! q, (E q).val = word) ∧
    ∀ q, (E q).val = word → ∃ z : V T → Bool, rep T z ((packHistory leaf.val epoch T).term q) ∧
      ∃ R : (Fin guesses → Bool) ≃ Returns body pub mac bank mem, ∀ g,
        let v := R g
        let y := Sum.elim (Sum.elim x word) z
        v.val.1.flatMap TeamRAM.Event.choices = List.ofFn g ∧ traceCost v.val.1 ≤ time ∧ signedWeight v.val.1 = 1 ∧
        Image F old ports y dest (readings v.val.2.2) ∧
        (∀ i : Fin o, v.val.2.2 (dest+m*3+RoutingOutputs.count m c j a+i.val) = DiagonalResidueRAM.word W
          (value fun t => rest.eval y (.inl (i,t)))) ∧ resident g v.val.2.2 := by
  intro hist ord ok emit accepted E paths
  obtain ⟨exactly,hs⟩ := bounded_history_paths epoch good closed leaf C rep steps correct bottom x base widths order fit
    emit body guesses pub mac bank mem time dest word paths
  refine ⟨exactly,fun q eq => ?_⟩
  obtain ⟨z,represented,R,eff⟩ := hs q eq
  refine ⟨z,represented,R,fun g => ?_⟩
  let y := Sum.elim (Sum.elim x word) z
  have raw (i : Fin (m*3+(RoutingOutputs.count m c j a+o))) : (R g).val.2.2 (dest+i.val) = DiagonalResidueRAM.word W
      (value fun t => (full F hk old ports rest).eval y (.inl (i,t))) := by
    apply Fin.ext
    rw [word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0<2) hb))]
    simpa only [emit,routingEmitter,Frame.select_eval,y,readings] using (eff g).2.2.2 i
  have img := of_packed_words F hk hb old ports rest y dest (R g).val.2.2 raw
  exact ⟨(eff g).1,(eff g).2.1,(eff g).2.2.1,img.1,img.2,paths.memory (R g) g (eff g).1⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
