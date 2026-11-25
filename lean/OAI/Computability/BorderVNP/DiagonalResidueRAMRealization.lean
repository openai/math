import OAI.Computability.BorderVNP.DiagonalResidueRAMSources
import OAI.Computability.BorderVNP.ResidueEntryReaderExtension

/-!
# The staged native residue-entry routine over the ground field

Choose an interpolation extension and its one bounded circuit before the pin
pair and all monomial multiplicities. The physical input then consists of
delivered literal bits, the two independent pin intervals and the unsigned
tally interval. No polynomial evaluator or shared-memory circuit frame is
assumed as a primitive.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM RoutingISA ResidueEntryInput ResiduePins ResidueBox ResidueIndex ResidueFourier
open ResidueEntryBudget Diagonal
open scoped BigOperators Classical

variable {w h pin tally p m D k : ℕ} {J Q G : Type*} [Fintype J] [Fintype Q] [Fintype G]

/-- For the same named query, packing the delivered literals and gathering
each input wire produces precisely the native cardinal obtained with the
already-initialized operands. -/
theorem staged_typed_card (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (mem : Memory w) (base start dense : ℕ) (src : Fin (Fintype.card Q) → ℕ)
    (C : BooleanTranscript.Circuit (Fin (Fintype.card (Q ⊕ G))) k) (x : Q → Bool)
    (L : Layout base start dense src (Fintype.card G) k w) (hpub : (pub 0).val+30 < 2^w)
    (hframe : packFrame pub mem dense start (6+3*k+Fintype.card Q))
    (hbits : DiagonalTallyBits.WordsAt mem dense
      ((payload w base start (typedCircuit Q G C) src).map BurstRAM.wordBits))
    (hsrc : ∀ i, mem (src i) = wordBit w (number x i)) :
    Nat.card (StagedPaths pub mac s mem) = Nat.card (typedPaths pub mac base (start+6) C x s mem) := by
  let T := typedCircuit Q G C
  let x' := number x
  have hv := L.valuation
  have hp := L.packed
  have fit : (frame base (start+6) T).fits w := ⟨hv.trans (Nat.le_add_right _ _),by
    change start+6+3*k < _; omega⟩
  have hw := staged_count pub mac s mem base start dense src T x' L hpub hframe hbits hsrc
  have hc := native_count pub mac base (start+6) T x'
    (initialBank s (frame base (start+6) T)) (initialMemory mem base (start+6) T x') fit
    (initialBank_loaded ..) (initialMemory_query _ _ _ _ _ (by unfold gateBase at hv; omega))
    (initialMemory_advice mem base (start+6) T x')
  exact_mod_cast hw.trans hc.symm

variable {E ι : Type*} [Fintype ι] [Field E] [Fact p.Prime] [Algebra (ZMod p) E]

/-- The actual native code, executed on physical sources, realizes one
padded matrix entry for all monomial indices and all initial scratch. -/
def StagedEntries (G : Type*) [Fintype G] (BE : Module.Basis (Fin D) (ZMod p) E)
    (q H : ℕ) (hq : 0 < q) (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin)
    (g : ι → MvPolynomial (Option (Fin h)) E) (gadgets : J → E) (m tally : ℕ)
    (C : BooleanTranscript.Circuit (Fin (Fintype.card (Board.Physical h pin tally J ⊕ G))) k) : Prop :=
  let P := Board.Physical h pin tally J
  let codec := boxPinCodec h hβ hH
  ∀ (W : ℕ) (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (s : Bank W) (mem : Memory W)
    (base start dense row col tallies : ℕ),
    let src : Fin (Fintype.card P) → ℕ := sourceAddress row col tallies ∘ (Fintype.equivFin P).symm
    Layout base start dense src (Fintype.card G) k W → (pub 0).val+30 < 2^W →
    packFrame pub mem dense start (6+3*k+Fintype.card P) →
    DiagonalTallyBits.WordsAt mem dense ((payload W base start (typedCircuit P G C) src).map BurstRAM.wordBits) →
    ∀ (r c : Fin ((h+2)*pin) → Bool) (μ : Fin h →₀ ℕ) (δ : J → ℕ),
      (∀ j, mem (row+j.val) = wordBit W (r j)) → (∀ j, mem (col+j.val) = wordBit W (c j)) →
      (∀ (i : Fin h) (j : Fin tally), mem (tallies+i.val*tally+j.val) = wordBit W ((μ i).testBit j.val)) →
      (∀ (l : J) (j : Fin tally), mem (tallies+(h+(Fintype.equivFin J l).val)*tally+j.val) =
        wordBit W ((δ l).testBit j.val)) →
      Fits H (parameterShift μ) → (∀ i, μ i < 2^tally) → (∀ l, δ l < 2^m) → (∀ l, δ l < 2^tally) →
      (Nat.card (StagedPaths pub mac s mem) : ZMod p) =
        (codec.decode r).elim 0 fun i => (codec.decode c).elim 0 fun j =>
          weights BE H q hq g (.id E) (parameterShift μ) (∏ l, gadgets l ^ δ l) i j

set_option maxHeartbeats 2000000 in
/-- Full §10.2–11 matrix-entry realization from the ground-field equations.
The interpolation extension is constructed, the exponents and basis bits are
bounded, and the emitted native reader handles all fields of its query. -/
theorem exists_staged_over_base [Fintype E] [CharP E p]
    (BE : Module.Basis (Fin D) (ZMod p) E) (q H s m tally : ℕ) (hq : 0 < q)
    (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin) (g : ι → MvPolynomial (Option (Fin h)) E)
    (hg : ∀ t, circuitSize (g t) ≤ s) (gadgets : J → E) :
    let width := (q-1) * ∑ t, (g t).totalDegree
    let idx := workWidth q H width
    let b := Nat.clog 2 p
    let w := b+1
    let h' := Fintype.card (Option (Fin h))
    ∃ N ≤ Fintype.card E * (width+1), width < N-1 ∧
      ∃ d, D ≤ Nat.clog 2 N ∧ d ≤ Nat.clog 2 N ∧ p ≤ N ∧
      ∃ k ≤ boardBudget h idx D m pin (Fintype.card (Input (Fin h) idx D J m d w b))
        (jointBudget h' idx D d w (Fintype.card J) m
          (gadgetBudget (Fintype.card ι) h' s (q-1).size (N-1-1).size idx (Fintype.card J) m)),
      ∃ C, StagedEntries (Guess (Fin h) d w b) BE q H hq hβ hH g gadgets m tally (k := k) C := by
  intro width idx b w h'
  obtain ⟨K,hK,hfin,hAlg,φ,d,BK,hfield,hcard,hD,hd,hpN⟩ := ResidueEntryVerifier.exists_bounded_grid_basis p BE width
  let N := Fintype.card K
  have hs : Fintype.card Kˣ = N-1 := Fintype.card_units K
  have hp : p < 2^w := (ResidueEntryField.dimensions_le BK (Nat.le_pow_clog Nat.one_lt_two N)).2.2
  obtain ⟨k,hk,C,native⟩ := exists_physical_entry (tally := tally) (m := m) (idx := idx) BE BK φ hp q H width s
    hq hβ hH (workWidth_fit q H width) g rfl hfield hg gadgets
  refine ⟨N,hcard,hs ▸ hfield,d,hD,hd,hpN,k,?_,C,?_⟩
  · rw [← hs]; exact hk
  intro W pub mac state mem base start dense row col tallies src L hpub hframe hbits r c μ δ hr hc hm hdg hμ hu hδ hδt
  let raw := Board.physicalInput (tally := tally) r c μ δ
  have hsrc := sourceAddress_value mem row col tallies r c μ δ hr hc hm hdg
  have cc := staged_typed_card pub mac state mem base start dense src C raw L hpub hframe hbits hsrc
  rw [cc]
  exact native W pub mac base (start+6) state mem (L.valuation.trans (Nat.le_add_right _ _))
    (by have := L.packed; omega) r c μ δ hμ hu hδ hδt

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
