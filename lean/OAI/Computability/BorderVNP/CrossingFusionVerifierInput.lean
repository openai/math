import OAI.Computability.BorderVNP.CrossingFusionWitnesses

/-!
# Bit blocks of the full side verifier

There is a block for each terminal word, padded mode code, occupation mask
and private path. The good assignments have a unique encoding. Rejecting
other mode codes or invalid occupation masks therefore preserves the
multiplicity of the full signed path sum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

open VPVNP

variable {m d : ℕ} {w : WireStates (leastEnergy m) (2^m)} {left : Bool} {b : Fin d → Bool}

/-- Coordinates of the bit assignment passed to all of the circuit blocks. -/
abbrev Raw (f : Checkers w left b) :=
  (Fin d × Fin m) ⊕ (Fin d × Fin (Nat.clog 2 (2*leastEnergy m))) ⊕
    (Σ i : Fin (d+1), Fin (i.val * leastEnergy m)) ⊕ (Σ i : Fin d, Fin (f i).guesses)

/-- All typed inputs and witnesses of the signed path sum. -/
abbrev Data (f : Checkers w left b) := (Fin d → Fin (2^m)) ×
  (Fin d → Fin (2*leastEnergy m)) × States d (leastEnergy m) × LocalGuesses f

/-- Terminal words, padded mode words, occupation masks and private witnesses written into the shared input. -/
noncomputable def encode (f : Checkers w left b) (g : Data f) : Raw f → Bool :=
  Sum.elim (fun t => RAMSerialization.wordBits m (g.1 t.1) t.2)
    (Sum.elim (fun t => RAMSerialization.wordBits _ ((g.2.1 t.1).castLE (Nat.le_pow_clog Nat.one_lt_two _)) t.2)
      (Sum.elim (fun t => (g.2.2.1 t.1).val t.2) (fun t => g.2.2.2 t.1 t.2)))

/-- Read the terminal words from a supplied bit assignment. -/
noncomputable def readTerm (f : Checkers w left b) (r : Raw f → Bool) (i : Fin d) : Fin (2^m) :=
  (RAMSerialization.wordBits m).symm (fun k => r (.inl (i,k)))

/-- Read the padded mode code. The range test enforces the published mode bound. -/
noncomputable def readMode (f : Checkers w left b) (r : Raw f → Bool) (i : Fin d) :
    Fin (2 ^ Nat.clog 2 (2*leastEnergy m)) :=
  (RAMSerialization.wordBits _).symm (fun k => r (.inr (.inl (i,k))))

/-- The state mask at one boundary of the chain. -/
def readState (f : Checkers w left b) (r : Raw f → Bool) (i : Fin (d+1)) (k : Fin (i.val * leastEnergy m)) :
    Bool := r (.inr (.inr (.inl ⟨i,k⟩)))

/-- Private path bits of one stage. -/
def readPath (f : Checkers w left b) (r : Raw f → Bool) (i : Fin d) (k : Fin (f i).guesses) :
    Bool := r (.inr (.inr (.inr ⟨i,k⟩)))

@[simp] theorem readTerm_encode (f : Checkers w left b) (g : Data f) (i : Fin d) :
    readTerm f (encode f g) i = g.1 i := by simp [readTerm, encode]

@[simp] theorem readMode_encode (f : Checkers w left b) (g : Data f) (i : Fin d) :
    readMode f (encode f g) i = (g.2.1 i).castLE (Nat.le_pow_clog Nat.one_lt_two _) := by
  simp [readMode, encode]

@[simp] theorem readState_encode (f : Checkers w left b) (g : Data f) (i : Fin (d+1)) :
    readState f (encode f g) i = (g.2.2.1 i).val := rfl

@[simp] theorem readPath_encode (f : Checkers w left b) (g : Data f) (i : Fin d) :
    readPath f (encode f g) i = g.2.2.2 i := rfl

/-- No two assignments of the typed tensor path give the same bit pattern. -/
theorem encode_injective (f : Checkers w left b) : Function.Injective (encode f) := by
  intro g g' h
  apply Prod.ext
  · funext i
    simpa using congrArg (fun r => readTerm f r i) h
  apply Prod.ext
  · funext i
    apply Fin.ext
    simpa using congrArg (fun r => (readMode f r i).val) h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa using congrArg (fun r => readState f r i) h
  · funext i
    simpa using congrArg (fun r => readPath f r i) h

/-- Legal raw assignments use valid modes and satisfy every local energy cutoff. -/
def legal (f : Checkers w left b) (r : Raw f → Bool) : Prop :=
  (∀ i, (readMode f r i).val < 2*leastEnergy m) ∧
    ∀ i, (StateIndex.validFrame (i.val * leastEnergy m)).eval (readState f r i) () = true

/-- Testing mode ranges and energies gives precisely the image of the typed encoding. -/
theorem legal_iff (f : Checkers w left b) (r : Raw f → Bool) :
    legal f r ↔ r ∈ Set.range (encode f) := by
  constructor
  · rintro ⟨hm, hs⟩
    let g : Data f := ⟨readTerm f r, fun i => ⟨(readMode f r i).val, hm i⟩,
      fun i => ⟨readState f r i, hs i⟩, readPath f r⟩
    refine ⟨g, ?_⟩
    funext t
    rcases t with ⟨i,k⟩ | ⟨i,k⟩ | ⟨i,k⟩ | ⟨i,k⟩
    · simp [g, encode, readTerm]
    · have e : ((g.2.1 i).castLE (Nat.le_pow_clog Nat.one_lt_two _)) = readMode f r i := Fin.ext rfl
      simp [encode, e, readMode]
    · rfl
    · rfl
  · rintro ⟨g,rfl⟩
    exact ⟨fun i => by simp,
      fun i => by simpa using (g.2.2.1 i).property⟩

private theorem next_occupancy_cast {E E' : ℕ} (h : E = E') (v : StateIndex.ValidMask E) :
    (rankedStates E' (Fin.cast (congrArg stateCountAt h) (maskIndex E v))).val =
      StateIndex.occupancy v.val := by
  cases h
  simp [rankedStates, maskIndex, StateIndex.validMaskEquiv]

/-- Canonical input bits read by the mode verifier at its lower-energy boundary. -/
theorem stageQuery_old (i : Fin d) (x : Fin d → Fin (2^m)) (j : Fin d → Fin (2*leastEnergy m))
    (v : States d (leastEnergy m)) (k : Fin (i.val*leastEnergy m)) :
    stageQuery i x j v (.inr (.inr (.inl k))) = (v i.castSucc).val k := by
  apply Bool.eq_iff_iff.mpr
  exact decide_eq_true_iff.trans (StateIndex.mem_occupancy _ _)

/-- Canonical input bits read by the mode verifier at the shared upper-energy boundary. -/
theorem stageQuery_next (i : Fin d) (x : Fin d → Fin (2^m)) (j : Fin d → Fin (2*leastEnergy m))
    (v : States d (leastEnergy m)) (k : Fin (i.val*leastEnergy m + leastEnergy m)) :
    stageQuery i x j v (.inr (.inr (.inr k))) =
      (v i.succ).val (k.cast (Nat.succ_mul i.val (leastEnergy m)).symm) := by
  change decide (k.val ∈ (rankedStates _ (Fin.cast _ (maskIndex _ (v i.succ)))).val) = _
  refine (congrArg (fun S : Finset ℕ => decide (k.val ∈ S))
    (next_occupancy_cast (Nat.succ_mul i.val (leastEnergy m)) (v i.succ))).trans ?_
  apply Bool.eq_iff_iff.mpr
  exact decide_eq_true_iff.trans (StateIndex.mem_occupancy (v i.succ).val
    (k.cast (Nat.succ_mul i.val (leastEnergy m)).symm))

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI
