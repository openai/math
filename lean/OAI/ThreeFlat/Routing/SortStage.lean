import OAI.ThreeFlat.Routing.SortNetwork
import OAI.ThreeFlat.Routing.SpillHalvings

namespace OAI
/-! # A deterministic stable sort with exposed input and output arrays

Output payloads are supplied at named external pins. Only the destination
labels and transported source indices are guessed, with exactly one viable
choice for each correctly sorted output.
-/

namespace ThreeFlat.Routing.SortNetwork

open scoped BigOperators Classical
noncomputable section

private abbrev Registers (m : ℕ) := Payload m m ⊕ Payload m m
private abbrev Interface (m u : ℕ) := Payload m u ⊕ Payload m u
private abbrev StageSource (m u : ℕ) := BitSource (Fintype.card (Registers m)) (Fintype.card (Interface m u))

private def expose {m u : ℕ} : Sources m u → StageSource m u
  | .constant b => .constant b
  | .pin j => .pin (Fintype.equivFin _ (.inl ((Fintype.equivFin (Payload m u)).symm j)))
  | .hidden j =>
    match (Fintype.equivFin (Hidden m u)).symm j with
    | .inl x => .hidden (Fintype.equivFin _ (.inl x))
    | .inr (.inl x) => .hidden (Fintype.equivFin _ (.inr x))
    | .inr (.inr x) => .pin (Fintype.equivFin _ (.inr x))

private def stageGuesses (m : ℕ) : (Labels m × Labels m) ≃ (Fin (Fintype.card (Registers m)) → Bool) where
  toFun z h := match (Fintype.equivFin (Registers m)).symm h with
    | .inl (i,j) => original (z.1 i) j
    | .inr (i,j) => original (z.2 i) j
  invFun h :=
    (fun i => addressEquiv m (fun j => h (Fintype.equivFin _ (Sum.inl (i,j)))),
     fun i => addressEquiv m (fun j => h (Fintype.equivFin _ (Sum.inr (i,j)))))
  left_inv z := by simp [original]
  right_inv h := by
    funext j
    obtain ⟨z,rfl⟩ := (Fintype.equivFin (Registers m)).surjective j
    rcases z with ⟨i,k⟩ | ⟨i,k⟩ <;> simp [original]

private abbrev G (m : ℕ) := Option (Edge m)
private def oldGate {m : ℕ} : G m → Gate m
  | none => none
  | some e => some (some e)

private def stagePart {K : Type*} [Zero K] [One K] {m u k : ℕ}
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) :
    (g : G m) → BitNetwork K (arity m u k (oldGate g))
  | none => S
  | some _ => compareBits K (m+k)

private def stageNet {K : Type*} [Zero K] [One K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) :
    BitNetwork K (Fintype.card (Interface m u)) :=
  BitNetwork.glue (stagePart S) (fun g p => expose (wires keyBit (oldGate g) p))

private theorem expose_read {m u : ℕ} (tag source : Labels m) (x y : Payload m u → Bool) (s : Sources m u) :
    (expose s).read (stageGuesses m (tag,source)) (Sum.elim x y ∘ (Fintype.equivFin _).symm) =
      s.read (hiddenBits tag source (Function.curry y)) (pack (Function.curry x)) := by
  cases s with
  | constant b => rfl
  | pin j => simp [expose,BitSource.read,pack]
  | hidden j =>
    obtain ⟨z,rfl⟩ := (Fintype.equivFin (Hidden m u)).surjective j
    rcases z with ⟨i,b⟩ | (⟨i,b⟩ | ⟨i,b⟩) <;>
      simp [expose, stageGuesses, BitSource.read, hiddenBits]

/-- The output array indexed by its stable permutation. -/
def sortedPins {m u k : ℕ} (keyBit : Fin k → Fin u) (input : Payload m u → Bool) :
    Payload m u → Bool :=
  let key := fun x : Fin u → Bool => addressEquiv k (x ∘ keyBit)
  Function.uncurry (Function.curry input ∘ Tuple.sort (key ∘ Function.curry input))

private theorem stageNet_eval {K : Type*} [CommSemiring K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) (hS : RealizesTaggedSwitch S)
    (x y : Payload m u → Bool) :
    TypedWiring.value (stageNet keyBit S) (Sum.elim x y) =
      if sortedPins keyBit x = y then 1 else 0 := by
  let key := fun t : Fin u → Bool => addressEquiv k (t ∘ keyBit)
  let input := Function.curry x
  let output := Function.curry y
  let σ := Tuple.sort (key ∘ input)
  change (stageNet keyBit S).eval (Sum.elim x y ∘ (Fintype.equivFin _).symm) = _
  rw [stageNet, BitNetwork.glue_eval, ← (stageGuesses m).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_option,stagePart,oldGate,arity,expose_read]
  have term (tag source : Labels m) :
      S.eval (fun j => (wires keyBit none j).read (hiddenBits tag source output) (pack input)) *
        (∏ e : Edge m, (compareBits K (m+k)).eval (fun j =>
          (wires keyBit (some (some e)) j).read (hiddenBits tag source output) (pack input))) =
      if tag = (σ.symm : Labels m) ∧ source = (σ : Labels m) ∧ output = input ∘ σ then 1 else 0 := by
    rw [switch_at keyBit hS]
    simp_rw [compare_at, wordValue_append_lt_iff]
    simp only [original, Equiv.apply_symm_apply, Fintype.prod_ite_zero,Finset.prod_const_one]
    change _ * (if ∀ e : Edge m, toLex (key (output e.1), source e.1) <
        toLex (key (output (next e)), source (next e)) then (1 : K) else 0) = _
    simp only [adjacent_edges (fun j => toLex (key (output j), source j))]
    have stable : StableRouting key input tag source output ↔
      tag = (σ.symm : Labels m) ∧ source = (σ : Labels m) ∧ output = input ∘ σ :=
      stableRouting_iff key input tag source output
    simp only [← stable, StableRouting,taggedSwitch]
    split_ifs <;> simp_all
  change (∑ tag : Labels m, ∑ source : Labels m,
    S.eval (fun j => (wires keyBit none j).read (hiddenBits tag source output) (pack input)) *
      ∏ e : Edge m, (compareBits K (m+k)).eval (fun j =>
        (wires keyBit (some (some e)) j).read (hiddenBits tag source output) (pack input))) = _
  simp_rw [term,ite_and]
  have iffout : output = input ∘ σ ↔ sortedPins keyBit x = y := by
    constructor
    · intro h
      simpa [sortedPins,σ,key,input,output] using (congrArg Function.uncurry h).symm
    · intro h
      simpa [sortedPins,σ,key,input,output] using (congrArg Function.curry h).symm
  simp [iffout]

/-- The stable-sort stage exposes every output payload bit. -/
def stage {K : Type*} [CommSemiring K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) (hS : RealizesTaggedSwitch S) :
    Spill.Stage K (Payload m u) (Payload m u) where
  network := stageNet keyBit S
  run x := some (sortedPins keyBit x)
  checked x y := by simpa using stageNet_eval keyBit S hS x y

@[simp] theorem stage_run {K : Type*} [CommSemiring K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) (hS : RealizesTaggedSwitch S)
    (x : Payload m u → Bool) : (stage keyBit S hS).run x = some (sortedPins keyBit x) := rfl

theorem stage_cells {K : Type*} [CommSemiring K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) (hS : RealizesTaggedSwitch S) :
    (stage keyBit S hS).network.cells ≤ S.cells + 2^m*((m+k+2)*96) := by
  have hc : Fintype.card (Edge m) ≤ 2^m := by
    simpa using Fintype.card_subtype_le (fun i : Fin (2^m) => i.val+1 < 2^m)
  simpa [stage,stageNet,Fintype.sum_option,stagePart,compareBits_cells] using
    Nat.add_le_add_left (Nat.mul_le_mul_right ((m+k+2)*96) hc) S.cells

theorem stage_internal {K : Type*} [CommSemiring K] {m u k : ℕ} (keyBit : Fin k → Fin u)
    (S : BitNetwork K (Fintype.card (SwitchPin m (m+u)))) (hS : RealizesTaggedSwitch S) :
    (stage keyBit S hS).network.internal ≤ 2^m*(m+m) + S.internal +
        2^m*((m+k+1)+(m+k+2)*80) := by
  have hc : Fintype.card (Edge m) ≤ 2^m := by
    simpa using Fintype.card_subtype_le (fun i : Fin (2^m) => i.val+1 < 2^m)
  simp only [stage,stageNet,BitNetwork.glue_internal,Fintype.sum_option,stagePart,compareBits_internal,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Registers,Payload,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin]
  nlinarith [Nat.mul_le_mul_right ((m+k+1)+(m+k+2)*80) hc]

end
end ThreeFlat.Routing.SortNetwork

end OAI
