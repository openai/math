import OAI.ThreeFlat.Diagonal.PhysicalStageBinary
import OAI.ThreeFlat.Diagonal.CompressorChildOrder
import OAI.ThreeFlat.Diagonal.HistoryWork

namespace OAI
/-! # Child counts of the physical refresh and shrink moves -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage

open Computability.VPVNP.Compression CompressorPacking PhysicalShrink HistoryContraction
open scoped Classical

variable {F : Type} [Field F]

/-- The old sites assigned to a new site in any actual term of a move. -/
def Move.FiberSize {d l D L : ℕ} {A : State d l} (R : Move F A D L) (q : ℕ) : Prop :=
  ∀ t v, Nat.card {x // R.rules.owner t x = v} = q

theorem Move.FiberSize.count {d l D L : ℕ} {A : State d l} {R : Move F A D L} {q : ℕ}
    (card : R.FiberSize q) {t : Fin R.rules.count} {Pins : Type*}
    {V : Form A.shape Pins} {W : Form (R.rules.target t) Pins} (a : Stage R.rules t V W)
    (v : (R.rules.target t).Site) : a.count v = q := by
  simpa only [Nat.card_fin] using (Nat.card_congr (a.child v)).trans (card t v)

private def onlyChild {Y : Type} (v : Y) : {y : Y // id y = v} ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨v,rfl⟩
  left_inv y := Subtype.ext y.property.symm
  right_inv _ := Subsingleton.elim _ _

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem refreshMove_fiberSize {m lanes hbits rem h pad : ℕ} {c : Fin m → Fin m → ℕ}
    {C γ : ℝ} (T : RefreshMotif.Table F c (1+h+pad) C) (A : State m lanes)
    (u : BitWord lanes ≃+ BitWord hbits × BitWord rem) (port : Fin m ≃ BitWord hbits)
    (hm : 2≤ m) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i,∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ) :
    (refreshMove T A u port hm hh sym rows zero conn).FiberSize 1 := by
  intro t v
  let I := StageAddress.refreshInputIso A.graph A.chart u port A.width
  exact (Nat.card_congr ((I.fiber id v).trans (onlyChild v))).trans (Nat.card_fin 1)

theorem refreshBinary_fiberSize {s rem h pad : ℕ} {c : Fin (2^s) → Fin (2^s) → ℕ} {C γ : ℝ}
    (T : RefreshMotif.Table F c (1+h+pad) C) (A : State (2^s) (s+rem))
    (hm : 2≤2^s) (hh : 0<h) (sym : ∀ i j,c i j=c j i) (rows : ∀ i, ∑ j,c i j=h)
    (zero : ∀ i,c i i=0) (conn : Expander.Bound (Expander.transition c h) ℝ γ) :
    (refreshBinary T A hm hh sym rows zero conn).FiberSize 1 :=
  refreshMove_fiberSize T A _ _ hm hh sym rows zero conn

private theorem fiberSize_degree {d l D D' rem q : ℕ} {A : State d l} (h : D=D')
    (R : Move F A D rem) (H : R.FiberSize q) :
    (h ▸ R : Move F A D' rem).FiberSize q := by
  cases h
  exact H

private theorem fiberSize_lanes {d l l' D rem q : ℕ} (h : l=l') (A : State d l)
    (R : Move F (h ▸ A : State d l') D rem) (H : R.FiberSize q) :
    (Move.recastInputLanes h A R).FiberSize q := by
  cases h
  exact H

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem shrinkMove_fiberSize {d lanes rem hbits tags D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^tags) (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).FiberSize (d*2^(2*d+1)) := by
  unfold shrinkMove
  apply fiberSize_degree
  intro t v
  have hc : 2≤2*d+1 := by omega
  let I := StageAddress.shrinkInputIso A.graph A.chart u P agree A.width
  let terms := shrinkBranches T A u P hd code
  let opening : terms := (Fintype.equivFin terms).symm t
  let side := ShrinkMotif.chooseWidths (issued T P (oldWidth A u) code hc opening)
  exact (Nat.card_congr ((I.fiber (P.placement side) v).trans (Owner.childOrder P side v).symm)).trans
    (Nat.card_fin _)

theorem shrinkRaw_fiberSize (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)))) :
    (shrinkRaw T s D rem hD small A).FiberSize (2^s*2^(2*(2^s)+1)) := by
  unfold shrinkRaw
  apply shrinkMove_fiberSize

theorem shrinkBinary_fiberSize (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) :
    (shrinkBinary T s D rem hD small A).FiberSize (2^s*2^(2*(2^s)+1)) := by
  unfold shrinkBinary
  apply fiberSize_lanes
  exact shrinkRaw_fiberSize T s D rem hD small _

theorem shrink_children_le_charge (s : ℕ) : 2^s*2^(2*(2^s)+1) ≤ 2^(shrinkCharge s) := by
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  unfold shrinkCharge
  omega

end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
