import OAI.Computability.BorderVNP.DiagonalResidueRAMBoardNetwork
import OAI.Computability.BorderVNP.DiagonalResidueRAMEntry

/-!
# A fixed native reader for every padded residue matrix entry

The advised circuit takes exactly the received binary pins and the team's
unsigned multiplicities. It supplies its own validity tests, offset additions
and field arithmetic. Advice is chosen before any of these inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM RoutingISA ResiduePins ResidueBox ResidueIndex ResidueFourier
open ResidueEntryInput ResidueEntryBudget ResidueEntryField Diagonal ExactQuantumFactoring
open scoped BigOperators Classical

variable {h p idx D d w m pin tally : ℕ} {ι J E K : Type*} [Fintype ι] [Fintype J]
  [Field E] [Field K] [Fintype K] [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) K]

/-- Boolean gates for the padded-pin guards, exponent offset, bit wiring and
the shared field verifier together. All charged dimensions are word lengths
or field-basis ranks, never the cardinality of the matrix index set. -/
def boardBudget (h idx D m pin namedBits fieldGates : ℕ) : ℕ :=
  fieldGates + namedBits * (100*(idx+m+Nat.clog 2 D+1)) + 2*((h+3)*(100*pin+25)) + 2

set_option maxHeartbeats 2000000 in
/-- Count of the actual native accepting paths on two external pin strings and the
serialized natural-valued team subtotals. The right side vanishes for any rejected
pin. A single choice of the polynomial-size advised circuit covers all inputs,
initial scratch and admissible memory placements. -/
theorem exists_physical_entry (BE : Module.Basis (Fin D) (ZMod p) E)
    (BK : Module.Basis (Fin d) (ZMod p) K) (φ : E →ₐ[ZMod p] K)
    (hp : p < 2^w) (q H width s : ℕ) (hq : 0 < q) (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin)
    (hidx : 2*H*q+3*H+q+width+1 < 2^idx) (g : ι → MvPolynomial (Option (Fin h)) E)
    (hdeg : width = (q-1) * ∑ t, (g t).totalDegree) (hfield : width < Fintype.card Kˣ)
    (hg : ∀ t, circuitSize (g t) ≤ s) (gadgets : J → E) :
    let b := Nat.clog 2 p
    let G := Guess (Fin h) d w b
    let P := Board.Physical h pin tally J
    let I := Input (Fin h) idx D J m d w b
    let h' := Fintype.card (Option (Fin h))
    let dag := gadgetBudget (Fintype.card ι) h' s (q-1).size (Fintype.card Kˣ-1).size idx (Fintype.card J) m
    let T := jointBudget h' idx D d w (Fintype.card J) m dag
    ∃ k ≤ boardBudget h idx D m pin (Fintype.card I) T,
      ∃ C : BooleanTranscript.Circuit (Fin (Fintype.card (P ⊕ G))) k,
        ∀ (W : ℕ) (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8)
          (base advice : ℕ) (state : Bank W) (mem : Memory W),
        gateBase base (Fintype.card P) (Fintype.card G) + k ≤ advice → advice+3*k < 2^W →
        ∀ (row col : Fin ((h+2)*pin) → Bool) (μ : Fin h →₀ ℕ) (δ : J → ℕ),
          Fits H (parameterShift μ) → (∀ i, μ i < 2^tally) →
          (∀ l, δ l < 2^m) → (∀ l, δ l < 2^tally) →
          let codec := boxPinCodec h hβ hH
          let raw := Board.physicalInput (tally := tally) row col μ δ
          (Nat.card (typedPaths (G := G) pub mac base advice C raw state mem) : ZMod p) =
            (codec.decode row).elim 0 fun i => (codec.decode col).elim 0 fun j =>
              weights BE H q hq g (.id E) (parameterShift μ) (∏ l, gadgets l ^ δ l) i j := by
  intro b G P I h' dag T
  obtain ⟨N,hn,hcount⟩ := ResidueEntryVerifier.exists_reader_network (idx := idx) (m := m) BE BK φ hp q H width s
    hq hidx g hdeg hfield hg gadgets
  let A : BooleanNetwork (Fintype.card (P ⊕ G)) 1 := Board.guarded H N
  let C := Transcript.circuit A 0
  refine ⟨A.net.count,?_,C,?_⟩
  · have hb : N.net.count ≤ T := hn
    exact (Board.guarded_count H N).trans (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right hb _) _) _)
  intro W pub mac base advice state mem hspace hlim row col μ δ hm hu hd ht codec raw
  have hc := typed_count (Q := P) (G := G) pub mac base advice C raw state mem ⟨hspace,hlim⟩
  have cc := congrArg (fun z : ℤ => (z : ZMod p)) hc
  push_cast at cc
  refine cc.trans ?_
  simp only [C, Transcript.circuit_eval]
  have valueAt (y : G → Bool) := Board.guarded_eval hβ hH N row col μ δ hu ht y
  have val' (y : G → Bool) :
      A.eval (Sum.elim raw y ∘ (Fintype.equivFin (P ⊕ G)).symm) 0 =
      (codec.decode row).elim false fun i => (codec.decode col).elim false fun j =>
        N.eval (number (Sum.elim (encodeQuery idx H m i.2.val (parameterShift μ) j.2.val i.1 j.1 δ) y)) 0 := valueAt y
  simp_rw [val']
  cases er : codec.decode row with
  | none => simp
  | some i =>
    cases ec : codec.decode col with
    | none => simp
    | some j =>
      simp only [Option.elim_some]
      refine Eq.trans ?_ (hcount i j (parameterShift μ) hm δ hd)
      exact Finset.sum_congr (Finset.ext (fun _ => by simp)) (fun _ _ => rfl)

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
