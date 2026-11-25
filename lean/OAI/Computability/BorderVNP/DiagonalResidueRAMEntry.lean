import OAI.Computability.BorderVNP.DiagonalResidueRAMTyped
import OAI.Computability.BorderVNP.ResidueEntryVerifier

/-! # The actual finite-opcode processor for the §10.2 residue matrix entry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM RoutingISA ResiduePins ResidueBox ResidueIndex ResidueFourier
open ResidueEntryInput ResidueEntryBudget
open scoped BigOperators Classical

variable {σ ι J E K : Type*} [Fintype σ] [Fintype ι] [Fintype J] [Field E] [Field K] [Fintype K]
variable {p idx D d w m : ℕ} [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) K]

set_option maxHeartbeats 2000000 in
/-- Once per chart, choose the Boolean advice for the finite opcode table.
For every queried pair of pins and every vector of parameter and gadget
multiplicities, the prime-field reduction of the actual number of native
accepting traces equals the specified residue matrix entry. -/
theorem exists_native_entry (BE : Module.Basis (Fin D) (ZMod p) E)
    (BK : Module.Basis (Fin d) (ZMod p) K) (φ : E →ₐ[ZMod p] K)
    (hp : p < 2 ^ w) (q H width s : ℕ) (hq : 0 < q)
    (hidx : 2*H*q+3*H+q+width+1 < 2^idx) (g : ι → MvPolynomial (Option σ) E)
    (hdeg : width = (q-1) * ∑ t, (g t).totalDegree) (hfield : width < Fintype.card Kˣ)
    (hg : ∀ t, circuitSize (g t) ≤ s) (gadgets : J → E) :
    let h := Fintype.card (Option σ)
    let b := Nat.clog 2 p
    let dag := gadgetBudget (Fintype.card ι) h s (q-1).size (Fintype.card Kˣ-1).size idx (Fintype.card J) m
    ∃ k ≤ jointBudget h idx D d w (Fintype.card J) m dag,
      ∃ C : BooleanTranscript.Circuit (Fin (Fintype.card (Input σ idx D J m d w b))) k,
        ∀ (wordWidth : ℕ) (pub : Arg → Word wordWidth) (mac : TeamOpcode.Macros wordWidth 8)
          (base advice : ℕ) (state : Bank wordWidth) (mem : Memory wordWidth),
        gateBase base (Fintype.card (Query σ idx D J m)) (Fintype.card (Guess σ d w b)) + k ≤ advice →
        advice + 3*k < 2^wordWidth →
        ∀ (i j : Index (Fin D) σ H) (μ : Exponent σ), Fits H μ →
        ∀ δ : J → ℕ, (∀ l, δ l < 2^m) →
          let query := encodeQuery idx H m i.2.val μ j.2.val i.1 j.1 δ
          (Nat.card (typedPaths (G := Guess σ d w b) pub mac base advice C query state mem) : ZMod p) =
            weights BE H q hq g (.id E) μ (∏ l, gadgets l ^ δ l) i j := by
  intro h b dag
  obtain ⟨k,hk,C,count⟩ := ResidueEntryVerifier.exists_reader (idx := idx) (m := m) BE BK φ hp q H width s
    hq hidx g hdeg hfield hg gadgets
  refine ⟨k,hk,C,?_⟩
  intro W pub mac base advice state mem hspace hlimit i j μ hm δ hδ query
  have hh := typed_count (Q := Query σ idx D J m) (G := Guess σ d w b)
    pub mac base advice C query state mem ⟨hspace,hlimit⟩
  have cast := congrArg (fun z : ℤ => (z : ZMod p)) hh
  push_cast at cast
  refine cast.trans (Eq.trans ?_ (count i j μ hm δ hδ))
  apply Finset.sum_congr (Finset.ext (fun _ => by simp)) (fun _ _ => rfl)

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
