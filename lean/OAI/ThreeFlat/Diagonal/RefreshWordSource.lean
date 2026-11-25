import OAI.ThreeFlat.Diagonal.RefreshHistogramStep
import OAI.ThreeFlat.Diagonal.HistogramBitAddresses

namespace OAI
/-! # Local bit addresses on the bundle and sparse wires of a physical refresh -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction Expander MotifBinaryPacking
open scoped Classical BigOperators
noncomputable section

variable {V C L : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] {m h p : ℕ}
    (G : LiftedSlots V m (C × L)) (c : Fin m → Fin m → ℕ) (sym : ∀ x y, c x y=c y x)
    (rows : ∀ x, ∑ y, c x y=h) (zero : ∀ x, c x x=0) (hm : 2 ≤ m) (pad : ℕ)

private abbrev ER := RawEdge (fun _ : V × L => Arc c) m
private abbrev RG := rawGraph (externalSite G) (fun _ => ports c)
private abbrev TG := actualPortGraph (outputGraph G c sym rows zero hm pad)

def actualHalf {v : (V × L) × Fin m} (a : (RG G c).Port v) : (TG G c sym rows zero hm pad).Port v :=
  ⟨(refreshSlots (numbering c rows) pad (.inl a.1.1),a.1.2),(refresh_ends G c sym rows zero hm pad a.1.1 a.1.2).trans a.property⟩

variable (b : ER (V:=V) (L:=L) c → ℕ)

omit [Fintype V] [Fintype L] [AddCommGroup C] in
private theorem actualHalf_width {v : (V×L)×Fin m} (a : (RG G c).Port v) :
    freshWidth c rows b pad (actualHalf G c sym rows zero hm pad a).1.1 = b a.1.1 := by simp [actualHalf,freshWidth]

def actualBit {v : (V×L)×Fin m}
    (addr : (a : (TG G c sym rows zero hm pad).Port v) → Fin (freshWidth c rows b pad a.1.1) → Fin p)
    (a : (RG G c).Port v) (t : Fin (b a.1.1)) : Fin p :=
  addr (actualHalf G c sym rows zero hm pad a) (Fin.cast (actualHalf_width G c sym rows zero hm pad b a).symm t)

omit [Fintype V] [Fintype L] [AddCommGroup C] in
theorem actualBit_read {v : (V×L)×Fin m} {A : ER (V:=V) (L:=L) c → Type} [∀ e, Fintype (A e)]
    (pack : ∀ e, A e ≃ Fin (2^b e))
    (addr : (a : (TG G c sym rows zero hm pad).Port v) → Fin (freshWidth c rows b pad a.1.1) → Fin p)
    (pin : Fin p → Bool) (ys : (TG G c sym rows zero hm pad).State (fun e => Fin (2^freshWidth c rows b pad e)) v)
    (read : ∀ a t, pin (addr a t) = (ys a).val.testBit t.val) (a : (RG G c).Port v) (t : Fin (b a.1.1)) :
    pin (actualBit G c sym rows zero hm pad b addr a t) = (pack a.1.1 ((physicalRefresh G c sym rows zero hm pad A b pack).read v ys a)).val.testBit t.val := by
  unfold actualBit
  rw [read]
  change _ = (pack a.1.1 ((pack a.1.1).symm _)).val.testBit _
  rw [(pack a.1.1).apply_symm_apply]
  rfl

/-- The source-port fields in a bundle use the same prefix-sum numbering as
all other variable-width history payloads. -/
theorem bundleWord_bit (width : Fin m → ℕ) (z : ∀ i, Fin (2^width i)) (i : Fin m) (j : Fin (width i)) :
    ((bundleWord width) z).val.testBit (finSigmaFinEquiv (n:=width) ⟨i,j⟩).val = (z i).val.testBit j.val := by
  have slice := bundleWord_slice width (bundleWord width z) i
  rw [(bundleWord width).symm_apply_apply] at slice
  rw [slice,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
  simp [j.isLt,Nat.add_comm]

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
