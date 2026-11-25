import OAI.Hierarchy.TaggedWireRoutedPackets
import OAI.Hierarchy.TaggedWireCoreMatrix

namespace OAI
/-! # Projection of the physical per-ball installations onto the two native banks -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open AdaptiveProbe ProtocolRAM RepairHistogram
open Computability.VPVNP.BurstRAM
open scoped BigOperators Classical

variable {S g p n w t : ℕ} {F : Type} [Field F]
variable (G : PortGraph (Fin S) (Fin g)) (P : PortGraph (Fin S) (Fin p)) (pad : Chord S)

theorem sum_widths (bit : Fin t→Fin (g+p)→ℕ) (stock : Fin g→ℕ) (paid : Fin p→ℕ)
    (stored : ∀i,∑j,bit j (stockRow i)=stock i)
    (printed : ∀e,∑j,bit j (paidRow e)=paid e)
    (stockLoop : ∀i,G.tail i=G.head i→stock i=0) (paidLoop : ∀i,P.tail i=P.head i→paid i=0) :
    (∑j,installedWidths (unionRows G P pad) (bit j))=G.chordWidths stock+P.chordWidths paid := by
  rw [←filled_width G pad stock stockLoop,←filled_width P pad paid paidLoop]
  unfold installedWidths
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_smul]
  rw [←finSumFinEquiv.sum_comp (fun i : Fin (g+p)=>(∑j,bit j i) • unitChord (unionRows G P pad i))]
  simp only [stockRow] at stored
  simp only [paidRow] at printed
  simp only [Fintype.sum_sum_type,unionRows,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,
    stored,printed]

variable {letters copies : Fin t→ℕ} (batch : ∀j,Row F S (letters j) (copies j))
variable (tender : ∀ j,RowRouting (batch j) (unionRows G P pad))

/-- The integer gains are the very same scatter coordinates used by
`RepairHistogram.raw`. The permanent rows count both paid radii and every
broadcast incidence before the post-repair cap redistributes surplus. -/
theorem target_shape (bank : Bank) (cols : Columns) (state : BallChoices letters copies→Memory w)
    (paid : BallChoices letters copies→Fin p→ℕ)
    (measured : ∀c i,(∑j,(tender j).install.load ((tender j).bits (c j)) (stockRow i)) =
      OuterBank.resourceBits (kind bank cols (state c)) (installedBits (n:=n) cols (state c)) i)
    (billed : ∀c e,(∑j,(tender j).install.load ((tender j).bits (c j)) (paidRow e))=paid c e)
    (stockDistinct : ∀i,G.tail i≠G.head i)
    (zero : ∀c e,P.tail e=P.head e→paid c e=0) (c : BallChoices letters copies) :
    (∑j,(tender j).post (c j))=
      G.chordWidths (OuterBank.resourceBits (kind bank cols (state c)) (installedBits (n:=n) cols (state c)))+
        P.chordWidths (paid c) :=
  sum_widths G P pad _ _ _ (measured c) (billed c) (fun i eq=>(stockDistinct i eq).elim) (zero c)

end Hierarchy.WireTelescope.ChosenPackets

end
end OAI
