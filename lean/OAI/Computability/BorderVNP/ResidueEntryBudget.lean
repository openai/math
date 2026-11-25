import OAI.Computability.BorderVNP.ResidueEntryInputWidths
import OAI.Computability.BorderVNP.ResidueEntryFieldBudget
import OAI.Computability.BorderVNP.DiagonalResidueRAMLoad

/-! # Polynomial resource bounds for the shared §10.2 matrix-entry checker

Count the fixed input wires, the Boolean expansion of the field DAG, grid range checks
and the selected basis functional. The advice is the gate description consumed by the
fixed word-RAM interpreter. Its word width suffices for the entire description and the
valuation array at the same time.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryBudget

open VPVNP ResidueFourier ResidueEntryField ResidueEntryInput

/-- Query bit count for the three exponents, two basis addresses and gadget multiplicities. -/
def queryWidth (h idx D labels m : ℕ) := 3*(h*idx) + 2*Nat.clog 2 D + labels*m

/-- Private grid and threshold guess width. -/
def guessWidth (h d w b : ℕ) := h*(d*w)+b

/-- Number of field inputs to the joint gadget DAG. -/
def fieldArity (h idx labels m : ℕ) := h + (h*idx+3) + labels*m

/-- Arity counts the exact number of live field input registers. -/
theorem gadget_card (σ J : Type*) [Fintype σ] [Fintype J] (idx m : ℕ) :
    Fintype.card (GadgetInput σ idx J m) = fieldArity (Fintype.card (Option σ)) idx (Fintype.card J) m := by
  simp only [GadgetInput,EntryInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,fieldArity]

/-- Number of gates in the shared field DAG including its input-controlled gadget product. -/
def gadgetBudget (charts h s qBits fieldBits idx labels m : ℕ) :=
  entryGateBudget charts h s qBits fieldBits idx + labels*(5*m+1)+1

/-- Boolean cost of verifying that each interpolation coordinate is nonzero and canonical. -/
def guardBudget (h d w : ℕ) := h*((d*(49*w+9)+d*(49*w+12)+3)+1)+1

/-- Boolean cost of selecting the addressed prime-field projection. -/
def projectBudget (D d w : ℕ) :=
  ResidueEntryBasis.lookupBudget D w (Nat.clog 2 D) (w+d*(w+limbCost w+limbCost w))

/-- Gate budget of the complete joint checker, with the Fourier/gadget arithmetic DAG
supplied at gate count `dag`. The result measures AND/NOT transcript gates. -/
def jointBudget (h idx D d w labels m dag : ℕ) :=
  fieldArity h idx labels m * (d*w) * ResidueEntryInput.budget h idx D d w +
    dag*stepCost d w + d*w*w + guardBudget h d w + projectBudget D d w + 49*w + 9

/-- A valid upper bound for the field DAG may replace its actual gate count. -/
theorem jointBudget_mono_dag (h idx D d w labels m : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    jointBudget h idx D d w labels m k ≤ jointBudget h idx D d w labels m k' := by
  unfold jointBudget
  gcongr

/-- A sufficient width for two disjoint banks starting at zero, including
all six header words and the two Boolean constants. -/
def ramWidth (u v g : ℕ) := Nat.clog 2 (u+v+4*g+16)

/-- The complete binary advice length for three addressed gate fields and six header words. -/
def adviceBits (u v g : ℕ) := DiagonalResidueRAM.adviceWords g * ramWidth u v g

/-- Placing the valuation bank immediately after the advice bank leaves all query,
guess and gate addresses representable in the chosen width. -/
theorem addresses_fit (u v g : ℕ) :
    DiagonalResidueRAM.adviceWords g + 2 + u + v + g < 2^ramWidth u v g := by
  apply lt_of_lt_of_le _ (Nat.le_pow_clog Nat.one_lt_two _)
  unfold DiagonalResidueRAM.adviceWords
  omega

/-- Neither address in any serialized gate record is truncated by the chosen RAM width. -/
theorem rows_fit {u v g : ℕ} (c : BooleanTranscript.Circuit (Fin u ⊕ Fin v) g) (i : Fin g) :
    let row := DiagonalResidueRAM.rows (DiagonalResidueRAM.adviceWords g) c.program i
    row.left < 2^ramWidth u v g ∧ row.right < 2^ramWidth u v g := by
  have ha := DiagonalResidueRAM.rows_addresses (DiagonalResidueRAM.adviceWords g) c.program i
  exact ⟨ha.1.trans (addresses_fit u v g),ha.2.trans (addresses_fit u v g)⟩

/-- The serialized gate records of any instantiated checker, including its header,
have precisely the charged binary length. -/
theorem advice_length {u v g : ℕ} (c : BooleanTranscript.Circuit (Fin u ⊕ Fin v) g) :
    ((DiagonalResidueRAM.adviceData (w := ramWidth u v g)
      (List.ofFn (DiagonalResidueRAM.rows (DiagonalResidueRAM.adviceWords g) c.program))).length + 6) *
        ramWidth u v g = adviceBits u v g := by
  rw [DiagonalResidueRAM.adviceData_length,List.length_ofFn]
  rfl

/-- Polynomial counts of coordinates, bits and labels give polynomial public input width. -/
theorem polynomiallyBounded_queryWidth {h idx D labels m : ℕ → ℕ}
    (hh : PolynomiallyBounded h) (hi : PolynomiallyBounded idx) (hD : PolynomiallyBounded D)
    (hL : PolynomiallyBounded labels) (hm : PolynomiallyBounded m) :
    PolynomiallyBounded fun n => queryWidth (h n) (idx n) (D n) (labels n) (m n) :=
  (((PolynomiallyBounded.const 3).mul (hh.mul hi)).add ((PolynomiallyBounded.const 2).mul hD.clog)).add (hL.mul hm)

/-- The full tuple of guesses has polynomial bit length. -/
theorem polynomiallyBounded_guessWidth {h d w b : ℕ → ℕ}
    (hh : PolynomiallyBounded h) (hd : PolynomiallyBounded d) (hw : PolynomiallyBounded w)
    (hb : PolynomiallyBounded b) :
    PolynomiallyBounded fun n => guessWidth (h n) (d n) (w n) (b n) :=
  (hh.mul (hd.mul hw)).add hb

/-- The arithmetic gate bound is polynomial in the chart gate count, dimensions and
binary widths of the extraction power, interpolation field and input multiplicities. -/
theorem polynomiallyBounded_gadgetBudget {charts h s qBits fieldBits idx labels m : ℕ → ℕ}
    (hc : PolynomiallyBounded charts) (hh : PolynomiallyBounded h) (hs : PolynomiallyBounded s)
    (hq : PolynomiallyBounded qBits) (hf : PolynomiallyBounded fieldBits) (hi : PolynomiallyBounded idx)
    (hL : PolynomiallyBounded labels) (hm : PolynomiallyBounded m) :
    PolynomiallyBounded fun n => gadgetBudget (charts n) (h n) (s n) (qBits n) (fieldBits n)
      (idx n) (labels n) (m n) :=
  ((polynomiallyBounded_entryGateBudget hc hh hs hq hf hi).add
    (hL.mul (((PolynomiallyBounded.const 5).mul hm).add (PolynomiallyBounded.const 1)))).add
    (PolynomiallyBounded.const 1)

/-- Polynomial Boolean cost of an extension-field step, including the multiplication table. -/
theorem polynomiallyBounded_stepCost {d w : ℕ → ℕ}
    (hd : PolynomiallyBounded d) (hw : PolynomiallyBounded w) :
    PolynomiallyBounded fun n => stepCost (d n) (w n) := by
  refine ((PolynomiallyBounded.const 20000).mul (((hd.add hw).add (.const 2)).pow 6)).of_le ?_
  intro n
  exact stepCost_le (Nat.le_add_right _ _) (by omega : w n ≤ d n + w n + 1)

/-- Polynomiality of the complete checker gate budget. -/
theorem polynomiallyBounded_jointBudget {h idx D d w labels m dag : ℕ → ℕ}
    (hh : PolynomiallyBounded h) (hi : PolynomiallyBounded idx) (hD : PolynomiallyBounded D)
    (hd : PolynomiallyBounded d) (hw : PolynomiallyBounded w) (hL : PolynomiallyBounded labels)
    (hm : PolynomiallyBounded m) (hg : PolynomiallyBounded dag) :
    PolynomiallyBounded fun n => jointBudget (h n) (idx n) (D n) (d n) (w n) (labels n) (m n) (dag n) := by
  let c := PolynomiallyBounded.const
  let ar := (hh.add ((hh.mul hi).add (c 3))).add (hL.mul hm)
  let dw := hd.mul hw
  let limb := (c 2000).mul ((hw.add (c 1)).pow 2)
  let sw := (c 49).mul hw
  let guard := (hh.mul ((((hd.mul (sw.add (c 9))).add (hd.mul (sw.add (c 12)))).add (c 3)).add (c 1))).add (c 1)
  let proj := ResidueEntryBasis.polynomiallyBounded_lookupBudget hD hw hD.clog
    (hw.add (hd.mul ((hw.add limb).add limb)))
  let ins := ResidueEntryInput.polynomiallyBounded_budget hh hi hD hd hw
  exact (((((((ar.mul dw).mul ins).add (hg.mul (polynomiallyBounded_stepCost hd hw))).add
    (dw.mul hw)).add guard).add proj).add sw).add (c 9)

/-- The full fixed description has polynomial bit length whenever the number of
public bits, private bits and shared gates is polynomially bounded. -/
theorem polynomiallyBounded_adviceBits {u v g : ℕ → ℕ}
    (hu : PolynomiallyBounded u) (hv : PolynomiallyBounded v) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded fun n => adviceBits (u n) (v n) (g n) :=
  let c := PolynomiallyBounded.const
  (((c 3).mul hg).add (c 6)).mul ((((hu.add hv).add ((c 4).mul hg)).add (c 16)).clog)

/-- Monotonicity of the advice-bit charge in the number of gates. -/
theorem adviceBits_mono (u v : ℕ) {g g' : ℕ} (h : g ≤ g') :
    adviceBits u v g ≤ adviceBits u v g' := by
  unfold adviceBits DiagonalResidueRAM.adviceWords ramWidth
  apply Nat.mul_le_mul
  · omega
  · exact Nat.clog_mono_right _ (by omega)

end ResidueEntryBudget

end BorderVNP
end Computability
end OAI
