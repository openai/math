import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly
import OAI.ThreeFlat.Diagonal.PhysicalStageBinary
import OAI.ThreeFlat.Diagonal.ShrinkAssemblyOrder
import OAI.ThreeFlat.Diagonal.ShrinkStageAssembly
import OAI.ThreeFlat.Diagonal.CompressorChildOrder

namespace OAI
/-! # The actual packed-site assembly for each term of physical shrinking -/

noncomputable section
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.Compression CompressorPacking CompressorPacking.PhysicalShrink HistoryContraction
open scoped Classical BigOperators
open private count_pos from OAI.ThreeFlat.Diagonal.PhysicalShrink

variable {F Pins : Type} [Field F]

theorem shrinkHalf_value {V Tag : Type} {d l : ℕ}
    (G : LiftedSlots (V×Tag) d (BitWord l)) (z : Site V Tag (BitWord l)) (j : Fin (2*d)) :
    (HalfOrder.order G z j).val.1=Native.ShrinkStage.Halves.sourceHalf G ((z.1,z.2.1),z.2.2) j := by
  let e:=(finCongr (two_mul d)).trans finSumFinEquiv.symm
  obtain ⟨a,rfl⟩:=e.symm.surjective j
  cases a with
  | inl i=>
    change (HalfOrder.order G z (HalfOrder.outOrdinal i)).val.1 =
      Native.ShrinkStage.Halves.sourceHalf G ((z.1,z.2.1),z.2.2) (HalfOrder.outOrdinal i)
    rw [HalfOrder.order_out]
    have slot : Native.ShrinkStage.Halves.halfSlot (HalfOrder.outOrdinal i)=i :=
      Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simp [Native.ShrinkStage.Halves.sourceHalf,slot,HalfOrder.outgoing,HalfOrder.atSlot,i.isLt]
  | inr i=>
    change (HalfOrder.order G z (HalfOrder.inOrdinal i)).val.1 =
      Native.ShrinkStage.Halves.sourceHalf G ((z.1,z.2.1),z.2.2) (HalfOrder.inOrdinal i)
    rw [HalfOrder.order_in]
    have slot : Native.ShrinkStage.Halves.halfSlot (HalfOrder.inOrdinal i)=i := by
      apply Fin.ext
      change (d+i.val)%d=i.val
      rw [Nat.add_mod_left,Nat.mod_eq_of_lt i.isLt]
    have bound : ¬d+i.val<d := by omega
    simp [Native.ShrinkStage.Halves.sourceHalf,slot,HalfOrder.incoming,HalfOrder.atSlot,bound]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
def shrinkMove_assembler {d lanes rem hbits tags D : ℕ} (T : ShrinkMotif.Table F) (A : State d lanes)
    (u : BitWord lanes ≃+ BitWord (2*d+1) × BitWord hbits × BitWord tags × BitWord rem)
    (P : PackingData A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1))
    (agree : StageAddress.packedGraph P=changeLanes A.graph u)
    (good : TagConditions P.slots (shift P) P.offset)
    (hd : 0<d) (hD : 0<D) (small : ((2^(2*d+1)*d*d:ℕ):ℝ)/D ≤ 1/1024)
    (tagSize : 1<2^tags) (code : Arc A.Base (BitWord hbits) (BitWord tags) (BitWord rem) d (2*d+1) ↪ ℕ)
    (order : ShrinkEdge P (parallel (2*d+1) d D) ↪ ℕ) :
    (shrinkMove T A u P agree good hd hD small tagSize code order).Assembler Pins := by
  unfold shrinkMove
  apply Move.castAssembler
  intro layout idx
  let c := 2*d+1
  have hc : 2≤c := by dsimp [c]; omega
  let old := oldWidth A u
  let I := StageAddress.shrinkInputIso A.graph A.chart u P agree A.width
  let packed := I.pushWord layout
  let n := parallel c d D
  let pad := padding c d D
  let tag := Native.adjacentMask tagSize
  have nz := Native.adjacent_ne tagSize
  let base := widths T P old code hc
  let repeats := r T P old code hc
  let tiles := tile T P old code hc
  let hist := (Fintype.equivFin (shrinkBranches T A u P hd code)).symm
  let lay := ShrinkMotif.chooseWidths (issued T P old code hc (hist idx))
  let fresh := shrinkWordLayout (Pins:=Pins) P base repeats tiles hist binary_neg good n order hc pad (tagPadding tag nz pad) idx
  let counts := fun _ : Site A.Base (BitWord tags) (BitWord rem) => d*2^c
  let child := fun v => Owner.childOrder P lay v
  let target := packed.inherited fresh (P.placement lay) counts child
  let origin (z : _) (j : Fin (target.ext z)) :=
    let piece : (i : Fin (counts z)) × Fin (packed.ext (child z i).val) := finSigmaFinEquiv.symm j
    let x := (child z piece.1).val
    (⟨⟨I.site.symm x,by
      exact (congrArg (P.placement lay) (I.site.apply_symm_apply x)).trans
        (child z piece.1).property⟩,piece.2⟩ :
        Σ u : {u // (P.placement lay) (I.site u)=z},Fin (layout.ext u.val))
  refine ⟨target,?_,⟨fun _=>rfl,(fun z j=>shrinkHalf_value _ z j)⟩,origin,fun _ _ _=>rfl,?_⟩
  · change Stage (I.rewrite (PhysicalShrink.step T P old code hc hd hD small binary_neg good order tag nz hist))
      idx layout.ports.form target.ports.form
    apply I.onStage layout
    · exact shrinkAssembly P old code (count_pos hd hc) (motifNumbers P code hc) (motifNumbers_bundle P code hc)
        base repeats tiles (fits T P old code hc) hist binary_neg good n
        (fun i => (SlotEnergy.slotCount_mass (by positivity : 0<((2^c*d*d:ℕ):ℝ)/D) small i).1)
        order hc pad (tagPadding tag nz pad) idx packed counts child (Local.assemblyCount P lay) (Local.assemblyOrder P lay)
    · intro e
      exact (congrArg A.width ((StageAddress.splitEdge u).symm_apply_apply e)).symm
    · intro e z
      rfl
  · intro v
    exact ⟨rfl,fun _=>rfl⟩

def shrinkRaw_assembler (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) ((2*(2^s)+1)+(s+(CompressorPacking.tagBits (2^s)+rem)))) :
    (shrinkRaw T s D rem hD small A).Assembler Pins := by
  unfold shrinkRaw
  apply shrinkMove_assembler

def shrinkBinary_assembler (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D ≤ 1/1024)
    (A : State (2^s) (shrinkCharge s+rem)) :
    (shrinkBinary T s D rem hD small A).Assembler Pins := by
  unfold shrinkBinary
  apply Move.inputAssembler
  exact shrinkRaw_assembler T s D rem hD small _


/-- For an installed assembler, each root reads all the previous and successor incident bits. -/
private def rootArity {d l D m : ℕ} {A : State d l} {R : Move F A D m} (J : R.Assembler Pins) : Prop :=
  ∀ (L : A.Words Pins) (b : Fin R.rules.count) (z : (R.rules.target b).Site),
    let step:=J L b
    let next:=((R.target_eq b).symm ▸ step.words.ports : PortLayout (R.rules.target b) Pins)
    step.stage.rootWidth z=(∑ i,L.ports.halfBits (step.stage.child z i).val)+next.halfBits z

private theorem rootArity_degree {d l D D' m : ℕ} {A : State d l} (e : D=D') (R : Move F A D m)
    (J : R.Assembler Pins) (h : rootArity J) : rootArity (Move.castAssembler e R J) := by cases e; exact h

private theorem rootArity_lane {d l l' D m : ℕ} (e : l=l') (A : State d l)
    (R : Move F (e ▸ A : State d l') D m) (J : R.Assembler Pins) (h : rootArity J) :
    rootArity (Move.inputAssembler e A R J) := by cases e; exact h

set_option maxRecDepth 11000 in
set_option maxHeartbeats 2000000 in
/-- The old chart transports each child's own ordered incident width. Every archived new half
contributes once to the other summand of the same literal root. -/
theorem shrinkBinary_assembler_arity (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
    (L : A.Words Pins) (b : Fin (shrinkBinary T s D rem hD small A).rules.count)
    (z : ((shrinkBinary T s D rem hD small A).rules.target b).Site) :
    let M:=shrinkBinary T s D rem hD small A
    let step:=shrinkBinary_assembler T s D rem hD small A L b
    let next:=((M.target_eq b).symm ▸ step.words.ports : PortLayout (M.rules.target b) Pins)
    step.stage.rootWidth z=(∑ i,L.ports.halfBits (step.stage.child z i).val)+next.halfBits z := by
  suffices all : rootArity (Pins:=Pins) (shrinkBinary_assembler T s D rem hD small A) from all L b z
  unfold shrinkBinary_assembler
  apply rootArity_lane
  unfold shrinkRaw_assembler shrinkMove_assembler
  apply rootArity_degree
  intro incoming term site
  dsimp only
  apply congrArg₂ Nat.add _ rfl
  apply Finset.sum_congr rfl
  intro i _
  apply HistoryRelabel.Iso.pushWord_halfBits_at
  intro e
  have pullback {α β : Type} (f : α → ℕ) (chart : α ≃ β) (a : α) :
      f a = (f ∘ chart.symm) (chart a) := (congrArg f (chart.symm_apply_apply a)).symm
  exact pullback _ (StageAddress.splitEdge (laneSplit (2*(2^s)+1) s (tagBits (2^s)) rem)) e

end ThreeFlat.Diagonal.PhysicalStage

end
end OAI
