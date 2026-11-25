import OAI.Computability.BorderVNP.ResidueEntryOutputEvaluation
import OAI.Computability.BorderVNP.ResidueEntryBudgetJoint
import OAI.Computability.BorderVNP.ResiduePinsBasis

/-! # The single advised matrix-entry circuit

At one scale, the shared binary verifier is selected before the substituted row, live
column, gadget multiplicities and parameter exponents. Summing its Boolean outputs over
all private guesses gives the actual prime-field matrix entry of §10.2. The gate budget
only charges binary lengths and the dimensions of the chart, field bases, and gadget list.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryVerifier

open ResiduePins ResidueFourier ResidueBox ResidueIndex ResidueEntryInput ResidueEntryBudget
open ResidueEntryOutput ResidueEntryVerifierCore ResidueEntryField
open VPVNP ExactQuantumFactoring
open scoped BigOperators Classical

variable {σ ι J E K : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Field E] [Field K] [Fintype K]
variable {p idx D d w m : ℕ} [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) K]

/-- Count the accepted tapes of any field DAG giving the true summand at a fixed query. -/
theorem counted_scalar (BE : Module.Basis (Fin D) (ZMod p) E) (BK : Module.Basis (Fin d) (ZMod p) K)
    (φ : E →ₐ[ZMod p] K) (π : Fin D → K →ₗ[ZMod p] ZMod p)
    (hπ : ∀ j, (π j).comp φ.toLinearMap = BE.coord j)
    (hp : p < 2^w) (q H width : ℕ) (hq : 0 < q) (g : ι → MvPolynomial (Option σ) E)
    (hwidth : (q-1) * ∑ t, (g t).totalDegree < Fintype.card Kˣ) (a : E)
    {gates : ℕ} (C : Circuit K (GadgetInput σ idx J m) gates) (i j : Index (Fin D) σ H)
    (μ : Exponent σ) (δ : J → ℕ)
    (hc : ∀ x : Option σ → Kˣ, C.eval id (Sum.elim
      (queryAssignment q H width idx x (ResidueIndex.encode idx H i.2.val μ j.2.val) 1 (φ (BE i.1)))
      (fun (l,b) => if (δ l).testBit b.val then 1 else 0)) =
        pathSummand φ q g a (BE i.1) i.2.val μ j.2.val x) :
    let b := Nat.clog 2 p
    let query := encodeQuery idx H m i.2.val μ j.2.val i.1 j.1 δ
    let F := build BK hp C (fieldNet (b := b) q H width BK (φ ∘ BE)) (valid p) yNet (project w BK π)
    (∑ guess : Guess σ d w b → Bool, if F.eval (number (Sum.elim query guess)) then
      (1 : ZMod p) else 0) = weights BE H q hq g (.id E) μ a i j := by
  intro b query F
  let R (x : Option σ → Kˣ) := π j.1 (pathSummand φ q g a (BE i.1) i.2.val μ j.2.val x)
  let S (z : Option σ → LimbWords d w) (y : Fin (2^b)) : ZMod p :=
    if y.val < (packedValue BK R z).val then 1 else 0
  let e := guessEquiv σ d w b
  have hb : b ≤ w := Nat.clog_le_of_le_pow hp.le
  have hbit (z : Option σ → LimbWords d w) (y : Fin (2^b)) :
      (if F.eval (number (Sum.elim query (e.symm (z,y)))) then (1 : ZMod p) else 0) = S z y := by
    let grid := fun s => (limbWords d w).symm (z s)
    let bits := ((bitsEquiv b).trans BitVec.equivFin.toEquiv).symm y
    have hv := build_eval_scalar hp hb BK φ.toRingHom BE π C q H width g a i.2.val μ j.2.val
      i.1 j.1 δ hc grid bits
    have hval : value bits = y.val := congrArg Fin.val
      (((bitsEquiv b).trans BitVec.equivFin.toEquiv).apply_symm_apply y)
    have he : F.eval (number (Sum.elim query (e.symm (z,y)))) = true ↔
        y.val < (packedValue BK R z).val := by
      rw [show e.symm (z,y) = encodeGuess grid bits from rfl]
      dsimp only [F, query, R]
      simp only [hval, grid, Equiv.apply_symm_apply] at hv
      exact hv
    exact if_congr he rfl rfl
  calc
    _ = ∑ zy : (Option σ → LimbWords d w) × Fin (2^b), S zy.1 zy.2 := by
      rw [← e.symm.sum_comp (fun guess =>
        if F.eval (number (Sum.elim query guess)) then (1 : ZMod p) else 0)]
      exact Finset.sum_congr rfl fun zy _ => hbit zy.1 zy.2
    _ = ∑ z, ∑ y, S z y := Fintype.sum_prod_type _
    _ = _ := (packed_entry_count BK hp.le φ (BE.coord j.1) (π j.1) (hπ j.1) q hq g
      a (BE i.1) i.2.val μ j.2.val hwidth).symm

/-- A single shared binary network for all pins, exponents and gadget products. Its accepting
path count, reduced in the prime field, is the specified entry of the matrix in (10.1). -/
theorem exists_reader_network (BE : Module.Basis (Fin D) (ZMod p) E) (BK : Module.Basis (Fin d) (ZMod p) K)
    (φ : E →ₐ[ZMod p] K) (hp : p < 2 ^ w) (q H width s : ℕ) (hq : 0 < q)
    (hidx : 2*H*q+3*H+q+width+1 < 2^idx) (g : ι → MvPolynomial (Option σ) E)
    (hdeg : width = (q-1) * ∑ t, (g t).totalDegree) (hfield : width < Fintype.card Kˣ)
    (hg : ∀ t, circuitSize (g t) ≤ s) (gadgets : J → E) :
    let h := Fintype.card (Option σ)
    let b := Nat.clog 2 p
    let dag := gadgetBudget (Fintype.card ι) h s (q-1).size (Fintype.card Kˣ-1).size
      idx (Fintype.card J) m
    ∃ N : BooleanNetwork (Fintype.card (Input σ idx D J m d w b)) 1,
      N.net.count ≤ jointBudget h idx D d w (Fintype.card J) m dag ∧
        ∀ (i j : Index (Fin D) σ H) (μ : Exponent σ), Fits H μ →
        ∀ δ : J → ℕ, (∀ l, δ l < 2^m) →
          (∑ guess : Guess σ d w b → Bool, if N.eval (number (Sum.elim
            (encodeQuery idx H m i.2.val μ j.2.val i.1 j.1 δ) guess)) 0 then
              (1 : ZMod p) else 0) =
          weights BE H q hq g (.id E) μ (∏ l, gadgets l ^ δ l) i j := by
  intro h b dag
  choose π hπ using fun j => exists_coordinate_extension p φ (BE.coord j)
  obtain ⟨k, hk, C, hC⟩ := exists_gadgetEntryCircuit φ.toRingHom q H width idx s m hq hidx g hdeg hg gadgets
  let N := verifier BK hp C (fieldNet (b := b) q H width BK (φ ∘ BE)) (valid p) yNet (project w BK π)
  refine ⟨N, (joint_count (b := b) q H width BK hp C (φ ∘ BE) π).trans
    (jointBudget_mono_dag h idx D d w (Fintype.card J) m hk), ?_⟩
  intro i j μ hm δ hδ
  have hs := counted_scalar BE BK φ π hπ hp q H width hq g (hdeg ▸ hfield) (∏ l, gadgets l ^ δ l) C i j μ δ
    (fun x => hC (BE i.1) i.2.val μ j.2.val (fits_of_inBox i.2.property) hm
      (fits_of_inBox j.2.property) x δ hδ)
  simpa only [build, Transcript.circuit_eval] using hs

/-- A single binary circuit for all pins, exponents and gadget products. Its accepting
path count, reduced in the prime field, is the specified entry of the matrix in (10.1). -/
theorem exists_reader (BE : Module.Basis (Fin D) (ZMod p) E) (BK : Module.Basis (Fin d) (ZMod p) K)
    (φ : E →ₐ[ZMod p] K) (hp : p < 2 ^ w) (q H width s : ℕ) (hq : 0 < q)
    (hidx : 2*H*q+3*H+q+width+1 < 2^idx) (g : ι → MvPolynomial (Option σ) E)
    (hdeg : width = (q-1) * ∑ t, (g t).totalDegree) (hfield : width < Fintype.card Kˣ)
    (hg : ∀ t, circuitSize (g t) ≤ s) (gadgets : J → E) :
    let h := Fintype.card (Option σ)
    let b := Nat.clog 2 p
    let dag := gadgetBudget (Fintype.card ι) h s (q-1).size (Fintype.card Kˣ-1).size
      idx (Fintype.card J) m
    ∃ gates ≤ jointBudget h idx D d w (Fintype.card J) m dag,
      ∃ c : BooleanTranscript.Circuit (Fin (Fintype.card (Input σ idx D J m d w b))) gates,
        ∀ (i j : Index (Fin D) σ H) (μ : Exponent σ), Fits H μ →
        ∀ δ : J → ℕ, (∀ l, δ l < 2^m) →
          (∑ guess : Guess σ d w b → Bool, if c.eval (number (Sum.elim
            (encodeQuery idx H m i.2.val μ j.2.val i.1 j.1 δ) guess)) then
              (1 : ZMod p) else 0) =
          weights BE H q hq g (.id E) μ (∏ l, gadgets l ^ δ l) i j := by
  intro h b dag
  obtain ⟨N, hN, hcount⟩ := exists_reader_network (idx := idx) (m := m) BE BK φ hp q H width s hq hidx
    g hdeg hfield hg gadgets
  refine ⟨N.net.count, hN, Transcript.circuit N 0, ?_⟩
  intro i j μ hm δ hδ
  simpa only [Transcript.circuit_eval] using hcount i j μ hm δ hδ

end ResidueEntryVerifier

end BorderVNP
end Computability
end OAI
