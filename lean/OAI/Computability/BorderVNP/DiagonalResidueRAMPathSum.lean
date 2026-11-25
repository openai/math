import OAI.Computability.BorderVNP.DiagonalResidueRAMRealization

/-! # The finite signed sum of staged residue traces used by the enclosing evaluator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BooleanTranscript VPVNP.BurstRAM RoutingISA

variable {w u v k : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
variable (s : Bank w) (mem : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
variable (c : Circuit (Fin u ⊕ Fin v) k) (x : Fin u → Bool)
variable (L : Layout base start dense src v k w) (hpub : (pub 0).val+30 < 2^w)
variable (hframe : packFrame pub mem dense start (6+3*k+u))
variable (hbits : DiagonalTallyBits.WordsAt mem dense ((payload w base start c src).map BurstRAM.wordBits))
variable (hsrc : ∀ i, mem (src i) = wordBit w (x i))

/-- The witness equivalence on physical staged memory, preserving one path
for each accepting bit assignment. -/
noncomputable def stagedWitnessEquiv :
    {y : Fin v → Bool // c.eval (Sum.elim x y) = true} ≃ StagedPaths pub mac s mem := by
  classical
  let h := prepare_runs pub mac s mem base start dense src c x L hpub hframe hbits hsrc
  let z := h.choose
  let mz := h.choose_spec.choose
  have hr := h.choose_spec.choose_spec
  have prep : Runs pub mac prepare s mem hr.1.choose z mz := hr.1.choose_spec.1
  have hf : (frame base (start+6) c).fits w := ⟨L.valuation.trans (Nat.le_add_right _ _),by
    change start+6+3*k < _; have := L.packed; omega⟩
  exact (witnessEquiv pub mac base (start+6) c x z mz hf hr.2.1 hr.2.2.1 hr.2.2.2).trans (prefixEquiv prep)

include L hpub hframe hbits hsrc in
/-- All native event histories, including the prefix, form a finite type.
This statement applies even when the verifier has no accepting witnesses. -/
theorem staged_finite : Finite (StagedPaths pub mac s mem) := by
  exact Finite.of_equiv {y : Fin v → Bool // c.eval (Sum.elim x y) = true}
    (stagedWitnessEquiv pub mac s mem base start dense src c x L hpub hframe hbits hsrc)

/-- Signed contribution of a chronological trace. -/
def signedWeight (es : List (TeamRAM.Event w)) : ℤ :=
  (es.map fun e => e.sign.value).prod

/-- A checked positive trace contributes one, including for an empty sequence. -/
theorem TraceOK.signedWeight {es : List (TeamRAM.Event w)} {bs : List Bool} {n : ℕ}
    (h : TraceOK es bs n) : signedWeight es = 1 := by
  have he : ∀ e ∈ es, e.sign = .plus := h.2.2
  unfold DiagonalResidueRAM.signedWeight
  clear h
  induction es with
  | nil => rfl
  | cons a es ih =>
    rw [List.map_cons,List.prod_cons,he a (by simp)]
    exact (one_mul _).trans (ih (fun e he' => he e (by simp [he'])))

include L hpub hframe hbits hsrc in
/-- The signed sum over all actual staged native paths is their cardinality.
The enclosing team may choose its own equivalent finite enumeration. -/
theorem staged_signed_sum [Fintype (StagedPaths pub mac s mem)] :
    (∑ path : StagedPaths pub mac s mem, signedWeight path.val) = (Nat.card (StagedPaths pub mac s mem) : ℤ) := by
  have one (z : StagedPaths pub mac s mem) : signedWeight z.val = 1 := by
    obtain ⟨_,_,h⟩ := staged_trace pub mac s mem base start dense src c x L hpub hframe hbits hsrc z
    exact h.signedWeight
  simp [one,Nat.card_eq_fintype_card]

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
