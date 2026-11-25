import OAI.ThreeFlat.Diagonal.RefreshWidthRead
import OAI.ThreeFlat.Diagonal.RefreshTableStep

namespace OAI
/-! # The common refresh width writer reproduces the physical target shape -/

namespace ThreeFlat.Diagonal.RefreshDemandRows

open Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.MotifRows RefreshTies CompressorPacking.Native
open MotifIntegerChoice Expander MotifOuterTerms
open scoped Classical BigOperators
noncomputable section

variable {m h pad : ℕ} {V L : Type} [Fintype V] [Fintype L]

private theorem sparse_pos (s : Fin m) (i : Fin h) (out : Fin m → ℕ) (sp : Fin m → Fin h → ℕ) :
    numberedWidth s (1+i.val) out sp = sp s i := by
  have nz : 1+i.val≠0 := by omega
  have dec : 1+i.val-1 = i.val := by omega
  simp [numberedWidth,dec,i.isLt]

omit [Fintype V] [Fintype L] in
/-- Source-port-major layout of the actual balanced graph, including all
padding. The read only needs the absolute slot offset and the fixed arc ROM. -/
theorem numbered_width_eq (c : Fin m → Fin m → ℕ) (rows : ∀ i, ∑ j, c i j = h)
    (w : Address (V × L) m → ℕ) (sp : V × L → Arc c → ℕ) (e : LiveSlot V L m (1+h+pad)) :
    let u := (e.1.1.1,e.2)
    numberedWidth e.1.1.2 e.1.2.val (fun s => ∑ i, w (u,i,s))
      (fun p s => sp u ((numbering c rows).symm (p,s))) =
      freshWidth c rows (termWidth c w sp) pad e := by
  let cover := refreshSlots (V:=V) (L:=L) (numbering c rows) pad
  obtain ⟨d,rfl⟩ := cover.surjective e
  change _ = Sum.elim (termWidth c w sp) (fun _ => 0) (cover.symm (cover d))
  rw [cover.symm_apply_apply]
  rcases d with (⟨u,s⟩ | ⟨u,e⟩) | ⟨⟨⟨v,j⟩,s⟩,l⟩
  · rfl
  · change numberedWidth ((numbering c rows e).1) (1+(numbering c rows e).2.val) _
      (fun p s => sp u ((numbering c rows).symm (p,s))) = sp u e
    rw [sparse_pos,Prod.mk.eta,Equiv.symm_apply_apply]
  · change numberedWidth j ((1+h)+s.val) _ _ = 0
    simp [numberedWidth,show ¬((1+h)+s.val-1<h) by omega]

variable {a t v W n : ℕ} {F : Type} [Field F] {c : Fin (mPort a) → Fin (mPort a) → ℕ} {H : ℝ}
variable (G : LiftedSlots (Fin v) (mPort a) (BitWord a × BitWord t))
variable (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin n → ℕ)
local notation "V" => Formula.natural W data mem vs

/-- Number the finite tile outputs exactly once when generating the ROM. -/
def poolOf (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ i, ∑ j, c i j=h)
    (j : Fin (T.last+1)) (b : Fin (Fintype.card (T.block j).Alphabet)) (s : Fin (mPort a)) (i : Fin h) :=
  (T.block j).output ((Fintype.equivFin _).symm b) ((numbering c rows).symm (s,i))

/-- For every output address, this one native width formula agrees exactly
with the successor label in the histogram-indexed history rewrite. -/
theorem generate_physical (T : RefreshMotif.Table F c (1+h+pad) H) (rows : ∀ i, ∑ j, c i j=h)
    (C : Columns (Formula n)) (remaining idx counts : Formula n) (stride : ℕ)
    (w : Address' v a t → ℕ) (stored : Stored G (C.map V) mem w)
    (e : LiveSlot (Fin v) (BitWord t) (mPort a) (1+h+pad)) (hr : V remaining = 2^t) (hi : V idx = nextIndex e)
    (x : T.Branch G (tagOrdinal a).symm w)
    (hist : ∀ (u : Block v t) (i : Fin (Fintype.card (T.entry G (tagOrdinal a).symm w u).Alphabet)),
      mem (V counts+blockId u*stride+i.val) = ((x u).val ((Fintype.equivFin _).symm i)).val) :
    V (generateWidth C remaining idx counts pad stride T.base (fun j => Fintype.card (T.block j).Alphabet)
      (fun j => (T.block j).bits) (poolOf T rows)) =
      freshWidth c rows (termWidth c w (T.widths G (tagOrdinal a).symm w x)) pad e := by
  rw [generateWidth_value G data mem vs _ _ _ _ _ _ _ _ _ _ w stored e hr hi,← numbered_width_eq]
  congr 1
  funext p s
  let u := (e.1.1.1,e.2)
  let j := T.winner G (tagOrdinal a).symm w u
  let r := T.repeats G (tagOrdinal a).symm w u
  let arc := (numbering c rows).symm (p,s)
  change r*(T.block j).bits + (∑ i : Fin (Fintype.card (T.block j).Alphabet),
    mem (V counts+blockId u*stride+i.val)*(T.block j).output ((Fintype.equivFin _).symm i) arc) =
      histWidth (T.block j).output (x u) arc + r*(T.block j).bits
  rw [Nat.add_comm]
  congr 1
  simp only [hist u]
  exact (Fintype.equivFin (T.block j).Alphabet).symm.sum_comp
    (fun i => ((x u).val i).val*(T.block j).output i arc)

end
end ThreeFlat.Diagonal.RefreshDemandRows

end OAI
