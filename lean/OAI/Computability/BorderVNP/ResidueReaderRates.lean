import OAI.Computability.BorderVNP.ResidueEntryBudgetFamily
import OAI.Computability.BorderVNP.DiagonalResidueRAMPhysical

/-!
# A uniform resource bound for the residue reader

The input dimensions and logarithmic widths may vary with the branch, the
characteristic and the field. Maximizing over the finite box of such
parameters turns the individual polynomial estimates into one global
polynomial that serves all readers. The public board takes two padded pins
and unsigned parameter and gadget tallies.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueRates

open VPVNP ResidueEntryBudget ResidueIndex DiagonalResidueRAM

/-- Numerical inputs to the board reader. The nine small inputs are the chart
dimension, chart gate count, gadget count, multiplicity width, padded pin width,
tally width, two finite-field ranks, and native word width. The five possibly
large inputs are the characteristic, extraction power, radius, interpolation
interval and interpolation field cardinality. -/
structure ReaderSizes where
  /-- Number of affine branch coordinates and chart equations. -/
  h : ℕ
  /-- Gate bound for each cleared equation. -/
  chartSize : ℕ
  /-- Number of entries in the multiplicative coefficient table. -/
  labels : ℕ
  /-- Binary exponent width for a coefficient-table entry. -/
  multiplicity : ℕ
  /-- Bits in one field of a padded row or column address. -/
  pin : ℕ
  /-- Binary width of a received unsigned team tally. -/
  tally : ℕ
  /-- Prime-field dimension of the branch constants. -/
  groundRank : ℕ
  /-- Prime-field dimension of the interpolation extension. -/
  gridRank : ℕ
  /-- Word width of the native advice loader. -/
  word : ℕ
  /-- Prime characteristic of the finite fields. -/
  p : ℕ
  /-- Selected Cartier extraction power. -/
  q : ℕ
  /-- Radius of the signed Laurent test box. -/
  H : ℕ
  /-- Degree interval of the powered chart product. -/
  width : ℕ
  /-- Cardinality of the interpolation field. -/
  gridCard : ℕ

/-- Named query wires of the shared residue matrix verifier. -/
def ReaderSizes.namedBits (x : ReaderSizes) :=
  queryWidth (x.h+1) (workWidth x.q x.H x.width) x.groundRank x.labels x.multiplicity

/-- Independent binary guesses of the finite grid and threshold counter. -/
def ReaderSizes.guessBits (x : ReaderSizes) :=
  guessWidth (x.h+1) x.gridRank (Nat.clog 2 x.p+1) (Nat.clog 2 x.p)

/-- Actual board addresses for the two pins and the serialized tally words. -/
def ReaderSizes.publicBits (x : ReaderSizes) :=
  2*((x.h+2)*x.pin)+(x.h+x.labels)*x.tally

/-- Gate bound for the native board, including its input decoder. -/
def ReaderSizes.boardGates (x : ReaderSizes) :=
  let h := x.h+1
  let idx := workWidth x.q x.H x.width
  let dag := gadgetBudget x.h h x.chartSize (x.q-1).size (x.gridCard-1-1).size idx x.labels x.multiplicity
  let gates := jointBudget h idx x.groundRank x.gridRank (Nat.clog 2 x.p+1) x.labels x.multiplicity dag
  boardBudget x.h idx x.groundRank x.multiplicity x.pin (x.namedBits+x.guessBits) gates

/-- Public board inputs, private guesses, actual gates, packed literal bits
and native time, charged together for a circuit with k gates. -/
def ReaderSizes.stagedCharge (x : ReaderSizes) (k : ℕ) :=
  let advice := (6+3*k+x.publicBits)*x.word
  let time := 128*(x.publicBits+x.guessBits+k+x.word+1)^2
  x.namedBits+x.guessBits+k+x.publicBits+advice+time

/-- Full worst-case cost for a single physical matrix-entry program. -/
def readerCharge (x : ReaderSizes) := x.stagedCharge x.boardGates

theorem stagedCharge_le {x : ReaderSizes} {k : ℕ} (hk : k ≤ x.boardGates) :
    x.stagedCharge k ≤ readerCharge x := by
  dsimp only [readerCharge, ReaderSizes.stagedCharge]
  gcongr

private abbrev InputBox (M : ℕ) := (Fin 9 → Fin (M+1)) × (Fin 5 → Fin (2^M+1))

private def sizesOfBox {M : ℕ} (x : InputBox M) : ReaderSizes :=
  ⟨x.1 0,x.1 1,x.1 2,x.1 3,x.1 4,x.1 5,x.1 6,x.1 7,x.1 8,x.2 0,x.2 1,x.2 2,x.2 3,x.2 4⟩

private theorem pred_bits_le {n M : ℕ} (h : n ≤ 2^M) : (n-1).size ≤ M := by
  apply Nat.size_le.mpr
  have := pow_pos (by decide : 0 < 2) M
  omega

private theorem boxCharge_polynomial (f : ∀ n, InputBox n) :
    PolynomiallyBounded (fun n => readerCharge (sizesOfBox (f n))) := by
  let small (j : Fin 9) (n : ℕ) := ((f n).1 j).val
  let large (j : Fin 5) (n : ℕ) := ((f n).2 j).val
  have sm (j) : PolynomiallyBounded (small j) := PolynomiallyBounded.id.of_le
    (fun n => Nat.le_of_lt_succ ((f n).1 j).isLt)
  have big (j) (n) : large j n ≤ 2^n := Nat.le_of_lt_succ ((f n).2 j).isLt
  have lg (j) : PolynomiallyBounded (fun n => Nat.clog 2 (large j n)) :=
    PolynomiallyBounded.id.of_le fun n => Nat.clog_le_of_le_pow (big j n)
  let c := PolynomiallyBounded.const
  have h := (sm 0).add (c 1)
  have idx := polynomiallyBounded_workWidth (lg 1) (lg 2) (lg 3)
  have b := lg 0
  have w := b.add (c 1)
  have named := polynomiallyBounded_queryWidth h idx (sm 6) (sm 2) (sm 3)
  have guess := polynomiallyBounded_guessWidth h (sm 7) w b
  have qbits := PolynomiallyBounded.id.of_le (fun n => pred_bits_le (big 1 n))
  have gridbits := PolynomiallyBounded.id.of_le (fun n =>
    (Nat.size_le_size (Nat.sub_le (large 4 n-1) 1)).trans (pred_bits_le (big 4 n)))
  have dag := polynomiallyBounded_gadgetBudget (sm 0) h (sm 1) qbits gridbits idx (sm 2) (sm 3)
  have gates := polynomiallyBounded_jointBudget h idx (sm 6) (sm 7) w (sm 2) (sm 3) dag
  have routing := (named.add guess).mul ((c 100).mul (((idx.add (sm 3)).add (sm 6).clog).add (c 1)))
  have guard := (c 2).mul (((sm 0).add (c 3)).mul (((c 100).mul (sm 4)).add (c 25)))
  have board := ((gates.add routing).add guard).add (c 2)
  have publicBits := ((c 2).mul (((sm 0).add (c 2)).mul (sm 4))).add (((sm 0).add (sm 2)).mul (sm 5))
  have advice := (((c 6).add ((c 3).mul board)).add publicBits).mul (sm 8)
  have time := (c 128).mul (((((publicBits.add guess).add board).add (sm 8)).add (c 1)).pow 2)
  exact ((((named.add guess).add board).add publicBits).add advice).add time

/-- One absolute polynomial bounds all resource terms of every actual board
reader whose dimensions and logarithmic inputs lie under the stated ceiling. -/
theorem uniform_reader_charge :
    ∃ A C : ℕ, ∀ (x : ReaderSizes) (M : ℕ),
      x.h ≤ M → x.chartSize ≤ M → x.labels ≤ M → x.multiplicity ≤ M →
      x.pin ≤ M → x.tally ≤ M → x.groundRank ≤ M → x.gridRank ≤ M → x.word ≤ M →
      x.p ≤ 2^M → x.q ≤ 2^M → x.H ≤ 2^M → x.width ≤ 2^M → x.gridCard ≤ 2^M →
      readerCharge x ≤ A*(M+1)^C := by
  classical
  have best (M : ℕ) : ∃ a : InputBox M, ∀ b : InputBox M, readerCharge (sizesOfBox b) ≤
      readerCharge (sizesOfBox a) := by
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun a : InputBox M => readerCharge (sizesOfBox a))
      Finset.univ_nonempty
    exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩
  choose f hf using best
  obtain ⟨A,C,h⟩ := (boxCharge_polynomial f).exists_global_bound
  refine ⟨A,C,?_⟩
  intro x M hh hs hl hm hpin ht hD hd hW hp hq hH hw hN
  let i (n) (h : n ≤ M) : Fin (M+1) := ⟨n,Nat.lt_succ_of_le h⟩
  let j (n) (h : n ≤ 2^M) : Fin (2^M+1) := ⟨n,Nat.lt_succ_of_le h⟩
  let a : InputBox M := (![i _ hh,i _ hs,i _ hl,i _ hm,i _ hpin,i _ ht,i _ hD,i _ hd,i _ hW],
    ![j _ hp,j _ hq,j _ hH,j _ hw,j _ hN])
  exact (hf M a).trans (h M)

end ResidueRates

end BorderVNP
end Computability
end OAI
