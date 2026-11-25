import OAI.ThreeFlat.Diagonal.ShrinkTable
import OAI.ThreeFlat.Diagonal.ShrinkHistogramStep
import OAI.ThreeFlat.Diagonal.ShrinkEnergyBudget
import OAI.ThreeFlat.Diagonal.HistogramRegister

namespace OAI
/-! # One selected, admitted and regularized shrink on the physical graph -/

namespace ThreeFlat.Diagonal.CompressorPacking.PhysicalShrink

open Computability.VPVNP.Compression MotifIntegerChoice MotifOuterTerms HistoryContraction
open scoped BigOperators Classical
noncomputable section
variable {c d : ℕ} {V H Tag L F : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [Field F]
variable (T : ShrinkMotif.Table F) (P : PackingData V H Tag L d c)
variable (w : Arc V H Tag L d c → ℕ) (code : Arc V H Tag L d c ↪ ℕ) (hc : 2≤c)

abbrev b := demandWidth P w (motifNumbers P code hc)
def picked (m : P.Motif) := best (score (b P w code hc m) T.base) T.first T.more
def r (m : P.Motif) := score (b P w code hc m) T.base (picked T P w code hc m)
abbrev widths (m : P.Motif) := T.base (picked T P w code hc m)
abbrev tile (m : P.Motif) := T.block (picked T P w code hc m)
abbrev Hists := Histories P (widths T P w code hc) (r T P w code hc) (tile T P w code hc)
abbrev issued (x : Hists T P w code hc) := historyWidth P (widths T P w code hc) (r T P w code hc) (tile T P w code hc) x

theorem fits (m : P.Motif) (i : Fin 2) : b P w code hc m i ≤ widths T P w code hc m i*r T P w code hc m :=
  T.fits _ i

theorem energy (x : Hists T P w code hc) (m : P.Motif) :
    Computability.VPVNP.MotifGrid.widthNorm ShrinkMotif.supplyMass (fun e => (issued T P w code hc x m e : ℝ))^2 ≤
      (63/32 : ℝ)*Computability.VPVNP.MotifGrid.widthNorm ShrinkMotif.demandMass (fun e => (b P w code hc m e:ℝ))^2+T.error :=
  T.energy _ (x m)

abbrev count := 3*(2^c*d)/4

private theorem count_eq (hc : 2≤c) : count (c:=c) (d:=d) = 3*(2^(c-2)*d) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hc
  simp only [count,Nat.add_sub_cancel_left,pow_add]
  change 3*(4*2^k*d)/4= _
  rw [show 3*(4*2^k*d)=(3*(2^k*d))*4 by ring,Nat.mul_div_cancel _ (by decide : 0<4)]

private theorem count_pos (hd : 0<d) (hc : 2≤c) : 0<count (c:=c) (d:=d) := by rw [count_eq hc]; positivity

/-- Fix the floor counts before assigning any histogram. The padding fills the requested
next degree exactly; the floor choice depends just on the old and new degrees. -/
def parallel (c d D : ℕ) (i : Fin 4) := SlotEnergy.slotCount (((2^c*d*d:ℕ):ℝ)/(D:ℝ)) i

theorem capacity (hc : 2≤c) (hd : 0<d) {D : ℕ} (hD : 0<D) : usedDegree (parallel c d D) c d ≤ D := by
  apply SlotEnergy.slotCount_capacity (K:=2^c*d) (Q:=count (c:=c) (d:=d)) (by positivity) hd hD
  rw [count_eq hc]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hc
  simp only [pow_add,Nat.add_sub_cancel_left]
  ring

def padding (c d D : ℕ) := D-usedDegree (parallel c d D) c d

theorem degree_eq (hc : 2≤c) (hd : 0<d) {D : ℕ} (hD : 0<D) : usedDegree (parallel c d D) c d + padding c d D=D := by
  unfold padding
  have := capacity hc hd hD
  omega

variable {D : ℕ} (hd : 0<d) (hD : 0<D) (small : ((2^c*d*d:ℕ):ℝ)/D ≤ 1/1024)
  (hn : ∀ a : Tag, -a=a) (good : TagConditions P.slots (shift P) P.offset)
  (order : ShrinkEdge P (parallel c d D) ↪ ℕ) (tag : Tag) (nonzero : tag ≠ 0)

/-- The actual finite tensor rewrite on the layout chosen from these histograms. -/
def step {N : ℕ} (enum : Fin N ≃ Hists T P w code hc) : Rewrite (oldShape P w) F := by
  apply histogramStep P w code (count_pos hd hc) (motifNumbers P code hc) (motifNumbers_bundle P code hc)
    (widths T P w code hc) (r T P w code hc) (tile T P w code hc) (fits T P w code hc) enum hn good
    (parallel c d D) (fun i => (SlotEnergy.slotCount_mass (by positivity : 0<((2^c*d*d:ℕ):ℝ)/D) small i).1)
    order hc (padding c d D) (tagPadding tag nonzero _)

include hd hD small in
/-- Energy of precisely the numbered wire words of each term returned by `step`. -/
theorem bound (hs : 0<Fintype.card (Site V Tag L)) (x : Hists T P w code hc)
    [Nonempty (Numbered V Tag L (usedDegree (parallel c d D) c d+padding c d D))] :
    let n := parallel c d D
    let pad := padding c d D
    let width := issued T P w code hc x
    let layout := ShrinkMotif.chooseWidths width
    let ns := fun e : CrossEdge P layout => n (typeIndex P hn good layout e)
    let bs := fun e : CrossEdge P layout => width e.1 e.2
    let cover := allPieceSlots P hn good layout n order hc pad
    let Z : ℝ := Fintype.card (Numbered V Tag L (usedDegree n c d+pad))
    let old : ℝ := Fintype.card (Position V H Tag L c)
    (∑ a, (SlotRefinement.actualWidth ns bs cover a : ℝ)^2/(1/Z)) ≤
      (126/127)*(∑ e, (w e : ℝ)^2/(1/(old*d))) +
      ((64/127)*((63/32)*(d:ℝ)^2*(3/4)*count (c:=c) (d:=d)+(d:ℝ)^2*count (c:=c) (d:=d)*T.error)+(D:ℝ)^2/4)*old^2 := by
  have he := degree_eq (D:=D) hc hd hD
  have h := physical_shrink_bound P w (count_pos hd hc) hd (count_eq hc) (motifNumbers P code hc)
    hn good (issued T P w code hc x) (parallel c d D) order hc (padding c d D) hs (by simpa only [he] using hD)
    (by simpa only [he] using small) (fun i => by rw [he]; rfl) T.error_nonneg (energy T P w code hc x)
  simpa only [← Nat.cast_add, he] using h

end
end ThreeFlat.Diagonal.CompressorPacking.PhysicalShrink

end OAI
