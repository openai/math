import OAI.Hierarchy.TraceRetainedRoom
import OAI.Hierarchy.TraceShrinkWordConstants
import OAI.ThreeFlat.Diagonal.PhysicalShrinkOutputBounds

namespace OAI
/-! # Word-width bounds for the native shrinking records -/

namespace Hierarchy.TraceShrinkRetained

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical Fin.NatCast BigOperators
noncomputable section

private theorem table_parts (slots colors tags bundles degree pieces keys tiles mult base factor q : ℕ)
    (fit : 80+slots+colors+tags+bundles+degree+pieces+keys+tiles+1+mult+base+factor≤q) :
    colors≤q ∧ slots≤q ∧ tags≤q ∧ bundles≤q ∧ degree≤q ∧ pieces≤q ∧
      keys≤q ∧ tiles+1≤q ∧ mult≤q ∧ base≤q ∧ factor≤q := by
  omega

private theorem heap_parts (layout : Dimensions) (q : ℕ)
    (fit : (Stage.shrink layout).heapWords≤q) : layout.motifs≤q ∧ layout.oldBase≤q := by
  simp only [Stage.heapWords] at fit
  omega

variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
variable (A : State (2^s) (shrinkCharge s+rem))

set_option quotPrecheck false
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "N" => Fintype.card (shrinkRecordState s rem A).Base
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "S" => shrinkStage s D
local notation "t" => tagBits d
local notation "x" => dims S N t rem
local notation "top" => shrinkMotifWidthFactor T k d*(1+A.maxWidth)

theorem scalar_room {q W : ℕ} (r : TraceRetainedRoom.Room q W)
    (fixed : fixedWords T s D ≤ q) (arena : (Stage.shrink x).heapWords ≤ q)
    (wire : A.maxWidth+1 ≤ q^4) :
    ShrinkOldCaps s rem W ∧ ShrinkOutputCaps s D N W ∧ T.more.length+1≤2^W ∧
      1+2*(widthMultiplicity k d*A.maxWidth)+shrinkBaseBound T<2^W ∧ top<2^W ∧
      80*(Q).motifs*top^2<2^W := by
  obtain ⟨colors,slots,tags,bundles,deg,pieces,keys,tiles,mult,base,weight⟩ :=
    table_parts d (2^k) (2^t) (3*(2^k*d)/4) D (S).pieceRadix (keyBound S 1 t)
      T.more.length (widthMultiplicity k d) (shrinkBaseBound T) (shrinkMotifWidthFactor T k d) q fixed
  obtain ⟨rows,siteCap⟩:=heap_parts x q arena
  have sites : N≤q:=siteCap
  have residual : 2^rem ≤ (x).motifs := by
    have nz : 0<N := Fintype.card_pos
    change 2^rem ≤ N*d*(2^rem)*2^t*d*(3*2^(k-2))
    calc
      2^rem ≤ N*d*(2^rem) := Nat.le_mul_of_pos_left _ (by positivity)
      _ ≤ _ := (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos t)).trans
        ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos s)).trans (Nat.le_mul_of_pos_right _ (by positivity)))
  have keyScale : keyBound S N t=N*keyBound S 1 t := by unfold keyBound; ring
  have eight : 8<2^W := by have := r.table; have := r.single; omega
  refine ⟨⟨eight,colors.trans_lt r.single,slots.trans_lt r.single,tags.trans_lt r.single,
    (residual.trans rows).trans_lt r.single,bundles.trans_lt r.single⟩,
    ⟨?_,(Nat.mul_le_mul sites tags).trans r.square.le,deg.trans_lt r.single,pieces.trans_lt r.single⟩,
    tiles.trans r.single.le,?_⟩
  · rw [keyScale]
    exact (Nat.mul_le_mul sites keys).trans_lt r.square
  · exact r.measured rows weight mult base wire


end
end Hierarchy.TraceShrinkRetained

end OAI
