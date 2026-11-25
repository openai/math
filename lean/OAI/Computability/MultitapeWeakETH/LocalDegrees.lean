import OAI.Computability.MultitapeWeakETH.SparseExpansion
import OAI.Computability.VPVNP.ExpandedMonomialDegree
import OAI.Computability.VPVNP.CompressionDegreeAssembly

/-! # Template degree in a single terminal parser -/

namespace OAI.Computability.MultitapeWeakETH.FactorizedCompression

open VPVNP Compression PairSimulation.LocalHistory NetworkKernel CompressorRecords
open scoped Classical
noncomputable section

variable {R : Type} [Field R] {I : Type} [Fintype I] {f : I → R}

private def KernelDegrees {N Y : Network} : (c : TermChain R N Y) → ChainParsers f c → Prop
  | .done _, _ => True
  | .more _ rec tail, r =>
    (∀ v a b p, (∑ l, (r.1.witness v a b).exponents p l) ≤ ∑ j, (rec v).degree j) ∧
    KernelDegrees tail r.2

open private castParsers from OAI.Computability.VPVNP.PairSimulationAssemblyBounds

private theorem castDegrees {N Y Z : Network} (e : N = Y) (c : TermChain R N Z) (r : ChainParsers f c)
    (h : KernelDegrees c r) : KernelDegrees (e ▸ c) (castParsers e c r) := by
  cases e
  exact h

private theorem branchDegrees {a g b n : ℕ} {X : State a g} (E : StateExecution R b n X)
    (W : E.MapWitnesses f) (r : ExecutionReaders E W) (rec : E.Records)
    (hd : E.DegreeCovered W rec) (z : E.Choices) :
    KernelDegrees (E.termChain rec z) (branchParsers E W r rec z) := by
  induction E with
  | done => trivial
  | more p tail ih =>
    exact ⟨hd.1 z.1, castDegrees (p.output_eq z.1).symm _ _ (ih z.1 _ _ _ (hd.2 z.1) z.2)⟩

private theorem finalDegrees {N Y : Network} (c : TermChain R N Y) (r : ChainParsers f c)
    (cov : KernelDegrees c r) (P : SiteParsers f N) (count : N.Site → ℕ) (D : ℕ)
    (records : c.AllRecordsLe D)
    (leaves : ∀ u a p, (∑ i, (P.witnesses u a).exponents p i) ≤ count u * D) :
    ∀ v b p, (∑ i, ((finalParsers c r P).witnesses v b).exponents p i) ≤ c.occurrences count v * D := by
  induction c with
  | done => exact leaves
  | more t rec tail ih =>
    exact ih r.2 cov.2 (r.1.push P) (t.pushHistorySize rec count) records.2.2
      (t.pushWitness_degree_le P.factors P.witnesses r.1.witness rec count D leaves cov.1 records.2.1)

/-- Each candidate monomial at a terminal site uses at most this many fixed
number-field entries, uniformly over the shared assignments. -/
theorem selected_degree {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    (κ : B.Entry → R) (hf : B.IsSolution κ) {g : ℕ} (T : ℕ) (h : T*S.laneBits ≤ g)
    (X : State (S.degreeExponent 0) g) (z : (B.execute κ hf T h X).Choices)
    (P : SiteParsers κ X.network) (zero : ∀ v a p i, (P.witnesses v a).exponents p i = 0) :
    let E := B.execute κ hf T h X
    let Q := finalParsers (E.termChain (B.records κ hf T h X) z) (selectedParsers B κ hf T h X z) P
    ∀ v a c, (∑ i, (Q.witnesses v a).exponents c i) ≤
      B.growthConstant^T * (B.growthConstant^T * (X.maxWireWidth+1)) := by
  obtain ⟨_, _, _, counts, records, _⟩ := B.branch_bounds κ hf T h X z
  let chain := (B.execute κ hf T h X).termChain (B.records κ hf T h X) z
  have cov : KernelDegrees chain (selectedParsers B κ hf T h X z) :=
    branchDegrees _ _ _ _ (B.execute_degreeCovered κ hf T h X) z
  exact fun v a c => (finalDegrees chain _ cov P (fun _ => 1) _ records (by simp [zero]) v a c).trans
    (Nat.mul_le_mul_right _ (counts v))

end
end OAI.Computability.MultitapeWeakETH.FactorizedCompression
