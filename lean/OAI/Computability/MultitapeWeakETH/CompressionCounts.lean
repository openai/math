import OAI.Computability.MultitapeWeakETH.FactorizedCompression
import OAI.Computability.VPVNP.PairSimulationAssemblyBounds
import OAI.Computability.VPVNP.PairSimulationSelectorBounds

/-! # Numbers of outer terms and summands at an individual final site -/

namespace OAI.Computability.MultitapeWeakETH.FactorizedCompression

open VPVNP Compression NetworkKernel CompressorRecords PairSimulation.LocalHistory
open scoped Classical
noncomputable section

/-- A bounded, self-delimiting choice stream embeds in exactly L bits.
Its parser recovers the choice regardless of the trailing zero padding. -/
theorem card_reader {I : Type} [Fintype I] (c : ChoiceReader I) (L : ℕ)
    (bounded : ∀ i, (c.encode i).length ≤ L) : Fintype.card I ≤ 2^L := by
  let pad (i : I) := c.encode i ++ List.replicate (L-(c.encode i).length) false
  have len (i : I) : (pad i).length = L := by simp [pad,bounded i]
  let key (i : I) : Fin L → Bool := fun j => (pad i)[j.val]'(by rw [len]; exact j.isLt)
  have recover (i : I) : List.ofFn (key i) = pad i := by apply List.ext_getElem <;> simp [key,len]
  have inj : Function.Injective key := by
    intro x y he
    have same := (recover x).symm.trans ((congrArg List.ofFn he).trans (recover y))
    have parse (i : I) := (c.read_iff (pad i) i (List.replicate (L-(c.encode i).length) false)).mpr rfl
    have eq := parse x
    rw [same,parse y] at eq
    exact (congrArg Prod.fst (Option.some.inj eq)).symm
  simpa using Fintype.card_le_of_injective key inj

variable {k R : Type} [Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
    (f : B.Entry → R) (hf : B.IsSolution f) {n : ℕ} (T : ℕ) (h : T*S.laneBits ≤ n)
    (X : State (S.degreeExponent 0) n)

/-- Count the admitted histories without paying again for selector strings
that already travel in shared payloads. -/
theorem outer_choices :
    let E := B.execute f hf T h X
    @Fintype.card E.Choices (choiceFintype E) ≤ 2^(((S.steps+1)*T) * (X.positions * scanConstant B *
      (scanConstant B + Nat.clog 2 (B.growthConstant^T*(X.maxWireWidth+1)+1)))) := by
  let E := B.execute f hf T h X
  let _ : Fintype E.Choices := choiceFintype E
  exact card_reader (executeOuterReader B f hf T h X) _ (executeOuterReader_bits_le B f hf T h X)

/-- Local readers from the verified compressor evaluate the same recursively
pushed factor used in the factorized contraction identity. -/
theorem finalParsers_factors {L : Type} [Fintype L] {κ : L → R} {N Y : Network}
    (c : TermChain R N Y) (r : ChainParsers κ c) (P : SiteParsers κ N) :
    (finalParsers c r P).factors = evaluate c P.factors := by
  induction c with
  | done => rfl
  | more t rec tail ih => exact ih _ _

theorem local_summands (z : (B.execute f hf T h X).Choices) (P : SiteParsers f X.network)
    (L : ℕ) (hL : ∀ u a p, ((P.read u a).encode p).length ≤ L) :
    let chain := (B.execute f hf T h X).termChain (B.records f hf T h X) z
    let Q := finalParsers chain (selectedParsers B f hf T h X z) P
    ∀ v a, Fintype.card (Q.witnesses v a).Choice ≤
      2^(B.growthConstant^T * max L (B.growthConstant^T*(X.maxWireWidth+1))) := by
  intro chain Q v a
  exact card_reader (Q.read v a) _ (selectedSite_length_le B f hf T h X z P L hL v a)

end
end OAI.Computability.MultitapeWeakETH.FactorizedCompression
