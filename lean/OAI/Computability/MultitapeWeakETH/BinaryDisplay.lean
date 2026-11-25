import OAI.Computability.MultitapeWeakETH.CorrectedDisplay

/-! # Packing the corrected display into its common binary supply -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open VPVNP.WireTensor Finset
open scoped Classical
noncomputable section
variable {n b N : ℕ} [NeZero N] (G : Network n b) {K : Type} [Field K]

abbrev binarySupply (K : Type) [Field K] := wireNetwork (k:=K) (src G (N:=N)) (dst G)
  (fun e => Fin (2^width G e))

theorem alphabet_card (e : Wire G) :
    Fintype.card (TablePipeline.Alphabet (CoreMessage G) Message e) = 2^width G e := by
  rw [← Nat.card_eq_fintype_card]
  rcases e with ⟨i,e⟩ | ⟨i,j⟩ | j | j <;>
    simp [TablePipeline.Alphabet,CoreMessage,Message,width,Word,pow_mul,mul_comm]

/-- The local decoding maps depend solely on the graph and wire widths.
The same decoding works for all shifts and all rows. -/
theorem decode_restriction : Restricts (binarySupply G K (N:=N)) (typedSupply G K (N:=N)) := by
  let a := Sum.elim (coreSrc G (N:=N)) (auxSrc G)
  let b' := Sum.elim (coreDst G (N:=N)) (auxDst G)
  have a_eq : src G (N:=N) = a := by funext e; rcases e with ⟨i,e⟩ | h <;> rfl
  have b_eq : dst G (N:=N) = b' := by funext e; rcases e with ⟨i,e⟩ | h <;> rfl
  unfold binarySupply
  rw [a_eq,b_eq]
  apply TablePipeline.restrict_alphabets
  intro e
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  rw [alphabet_card,Fintype.card_fin]

def decode := Classical.choose (decode_restriction G (N:=N) (K:=K))

def binaryMaps {L : ℕ} (hb : 0 < b) (l r : Fin L → Fin n)
    (tables : Fin 4 → (v : Fin G.vertices) → G.View v → K)
    (v : Site G N) (p : Pin G v) (z : (demand G hb l r (K:=K)).Basis v)
    (wire : (binarySupply G K (N:=N)).Basis v) : K :=
  ∑ x, maps G hb l r tables v p z x * decode G v x wire

theorem binary_contraction {L : ℕ} (hb : 0 < b) (l r : Fin L → Fin n)
    (tables : Fin 4 → (v : Fin G.vertices) → G.View v → K) (p : ∀ v : Site G N, Pin G v) :
    applyLocal (fun v => binaryMaps G hb l r tables v (p v)) (binarySupply G K).coeff =
      applyLocal (fun v => maps G hb l r tables v (p v)) (typedSupply G K).coeff := by
  have h := Classical.choose_spec (decode_restriction G (K:=K) (N:=N))
  change applyLocal (decode G) (binarySupply G K).coeff = (typedSupply G K).coeff at h
  rw [← h,applyLocal_comp]
  rfl

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
