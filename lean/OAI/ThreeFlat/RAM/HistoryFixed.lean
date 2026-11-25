import OAI.ThreeFlat.RAM.HistoryFactorMemory
import OAI.ThreeFlat.RAM.HistoryFactorPadding

namespace OAI
/-! # One weighted history interpreter for every selected slot of bounded size -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM BitLayout Contraction BitNetwork Diagonal.TraceCircuit

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}

/-- Number of addressable words, including constants, raw pins, work bits, expanded
cells, the multiplication table, compact source rows, and the shared library. -/
theorem compact_words (p H J tables : ℕ) :
    footprint (blankNetwork (F := F) p H J) + 4*J + 8*tables =
      2+p+H+15*J+Fintype.card F*Fintype.card F+8*tables := by
  simp only [footprint, blankNetwork, mulBase, cellsBase, hiddenBase]
  omega

private theorem value_size (N : BitNetwork F p) (L : Library N)
    (H J : ℕ) (hh : N.internal = H) (hj : N.cells = J)
    (fit : Fits (blankNetwork (F := F) p H J) w)
    (space : footprint (blankNetwork (F := F) p H J) + 4*J + 8*L.count ≤ 2^w)
    (pin : Fin p → Bool) (tail : Memory w) (state : Word w) (extra : ℕ) :
    let shape := blankNetwork (F := F) p H J
    let base := footprint shape
    value (codec shape fit) (interpreter p H J base (base+4*J) fit) (extra+13+5*H+550*J)
      state (compactInput N L (codec shape fit) pin tail) = N.eval pin := by
  subst H J
  exact value_compactInput N fit L space pin tail state extra

/-- A single machine for fixed pin, hidden and cell capacities evaluates every
smaller network that fits, in every field characteristic. Its compact input includes
the two reserved table IDs for unused bits and cell slots. -/
theorem value_fixed_capacity (N : BitNetwork F p) (L : Library N) (H J : ℕ)
    (hh : N.internal ≤ H) (hj : N.cells+(H-N.internal) ≤ J)
    (fit : Fits (blankNetwork (F := F) p H J) w)
    (space : footprint (blankNetwork (F := F) p H J) + 4*J + 8*(L.count+2) ≤ 2^w)
    (pin : Fin p → Bool) (tail : Memory w) (state : Word w) (extra : ℕ) :
    let shape := blankNetwork (F := F) p H J
    let base := footprint shape
    let b := H-N.internal
    let u := J-(N.cells+b)
    value (codec shape fit) (interpreter p H J base (base+4*J) fit) (extra+13+5*H+550*J)
      state (compactInput (addPadding N b u) (L.padded b u) (codec shape fit) pin tail) =
      N.eval pin := by
  let b := H-N.internal
  let u := J-(N.cells+b)
  obtain ⟨hb,hc⟩ := fixed_capacities N hh hj
  exact (value_size (addPadding N b u) (L.padded b u) H J hb hc fit space pin tail state extra).trans
    (addPadding_eval N b u pin)

end ThreeFlat.RAM.HistoryFactors

end OAI
