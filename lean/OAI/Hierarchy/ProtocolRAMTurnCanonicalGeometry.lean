import OAI.Hierarchy.ProtocolRAMTurnEdges
import OAI.Hierarchy.ProtocolRAMTurnInstalled

namespace OAI
/-! # The raw boundary chart enumerates every boundary of the settled walk -/

noncomputable section
namespace Hierarchy.ProtocolRAMPaidTurnPlacement.Canonical
open AdaptiveProbe ProbeStage CoreBoard WordSeats WireTelescope SettledMatrix
open ProtocolRAM.Calendar CoreRoute ProtocolRAMTurnOrder ProtocolRAMTurnChart
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K)
local notation "L" => B.matrixLayout inj pad
local notation "Sources" => ProtocolRAMTurnGeometry.Source edges h d k
local notation "names" => Equiv.symm (ProtocolRAMTurnGeometry.sourceOrder edges h d k)
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names
local notation "direction" => ProtocolRAMTurnStepOrder.reverse B inj pad

/-- A decreasing raw route counts its boundary from the other end. -/
def phase (src : Sources) :
    Fin (ProtocolRAMTurnGeometry.length src+1) ≃ Fin (((L).steps src).length+1) :=
  (boundary (ProtocolRAMTurnGeometry.length src) (direction src)).trans
    (finCongr (congrArg (·+1) (ProtocolRAMTurnEdges.canonical_length B inj pad src).symm))

theorem phase_val (src : Sources) (j : Fin (ProtocolRAMTurnGeometry.length src+1)) :
    (phase B inj pad src j).val = if direction src then ProtocolRAMTurnGeometry.length src-j.val else j.val :=
  by simpa only [phase,Equiv.trans_apply,finCongr_apply,Fin.val_cast] using
       boundary_val (ProtocolRAMTurnGeometry.length src) (direction src) j

/-- Every raw boundary has one canonical boundary, including dormant rows. -/
def posn : Fin (turns len) ≃ (Σ i, Fin (((L).routes i).length+1)) :=
  (encode (width len)).symm.trans (Equiv.sigmaCongrRight (fun i => phase B inj pad (names i)))

theorem posn_fst (q : Fin (turns len)) : (posn B inj pad q).1 = (raw len q).1 := rfl

def spines (i) : Spine (rowGraph (L).edge) ((L).family i).1.1 ((L).routes i) ((L).family i).1.2 :=
  (Spine.exists_of_walk ((L).paths (names i))).some

/-- The canonical spine visits the very site visited by the physical raw
walk at its original ordinal, even after reversing a commodity or reserve. -/
theorem phase_site (src : Sources) (j : Fin (ProtocolRAMTurnGeometry.length src+1))
    (sp : Spine (rowGraph (L).edge) ((L).original src).1.1 ((L).steps src) ((L).original src).1.2) :
    (sp.visit (phase B inj pad src j)).val = ProtocolRAMTurnEdges.visit B inj pad src j.val := by
  rcases src with e | i | c
  · rw [visit_fixed B inj pad e sp, phase_val]
    change (if j.val=0 then ((L).edge e).1.1 else ((L).edge e).1.2).val =
      (if j.val=0 then ((L).edge e).1.1.val else ((L).edge e).1.2.val)
    by_cases z : j.val=0 <;> simp [z]
  · rw [visit_commodity B inj pad i sp,phase_val]
    have n := ProtocolRAMTurnGeometry.length_ordinary B i
    have bound : j.val ≤ (B.ordinary i).length := (Nat.le_of_lt_succ j.isLt).trans_eq n.symm
    have phaseBack : forwardBoundary ((L).goods.tail i) ((L).goods.head i) (B.ordinary i).length
        (if direction (.inr (.inl i)) then ProtocolRAMTurnGeometry.length (edges:=edges) (.inr (.inl i))-j.val else j.val) = j.val := by
      by_cases low : (L).goods.tail i < (L).goods.head i
      · simp [forwardBoundary,ProtocolRAMTurnStepOrder.reverse,low]
      · simp [forwardBoundary,ProtocolRAMTurnStepOrder.reverse,low]; omega
    rw [phaseBack]
    rfl
  · rw [visit_reserve B inj pad c sp,phase_val]
    have n := ProtocolRAMTurnGeometry.length_center B c
    have bound : j.val ≤ (B.centers c).length := (Nat.le_of_lt_succ j.isLt).trans_eq n.symm
    have phaseBack : forwardBoundary ((L).reserve.tail c) ((L).reserve.head c) (B.centers c).length
        (if direction (.inr (.inr c)) then ProtocolRAMTurnGeometry.length (edges:=edges) (.inr (.inr c))-j.val else j.val) = j.val := by
      by_cases low : (L).reserve.tail c < (L).reserve.head c
      · simp [forwardBoundary,ProtocolRAMTurnStepOrder.reverse,low]
      · simp [forwardBoundary,ProtocolRAMTurnStepOrder.reverse,low]; omega
    rw [phaseBack]
    rfl

local notation "visit" => ProtocolRAMVisitAdjacency.vertex len
  (fun a => ProtocolRAMTurnEdges.visit B inj pad (names a))

theorem visit_at (q : Fin (turns len)) :
    ((spines B inj pad (posn B inj pad q).1).visit (posn B inj pad q).2).val = visit q :=
  phase_site B inj pad (names (raw len q).1) (raw len q).2 _

variable (o : Orders h d k) (base : ℕ) (v : Words)
local notation "t" => record (ProtocolRAMTurnGeometry.header o base names) v visit

/-- All original widths, even a zero one whose endpoint table is arbitrary. -/
theorem widths (values : ProtocolRAMTurnItinerary.Values) (count : Fin (Fintype.card Sources) → ℕ)
    (widthAt : ∀ i : Fin (Fintype.card Sources), v.width i.val = count i) (q : Fin (turns len)) :
    ProtocolRAMTurnInstalled.columns t values q 4 = count (posn B inj pad q).1 := by
  let r := raw len q
  have item : (ProtocolRAMTurnGeometry.header o base names q).item = r.1.val :=
    congrArg Fin.val ((ProtocolRAMTurnGeometry.sourceOrder edges h d k).apply_symm_apply r.1)
  have bound := ProtocolRAMTurnGeometry.within o base names q
  change (if (t q).length < (t q).position then 0 else (t q).width) = _
  have valid : (t q).position ≤ (t q).length := by
    let head := ProtocolRAMTurnGeometry.header o base names q
    change (if rev v head.item then head.length-head.raw else head.raw) ≤ head.length
    split <;> first | exact Nat.sub_le _ _ | exact bound
  rw [ite_eq_right (not_lt.mpr valid)]
  exact (congrArg v.width item).trans (widthAt r.1)

/-- These are precisely the six geometric equalities consumed by the native
role and start readbacks. Direction is observed only on positive-width rows. -/
theorem fields (q : Fin (turns len))
    (reverseAt : rev v (posn B inj pad q).1.val = direction (names (posn B inj pad q).1)) :
    let i := (posn B inj pad q).1
    let j := (posn B inj pad q).2
    (t q).item = i.val ∧ (t q).origin = ProtocolRAMTurnGeometry.origin o (names i) ∧
    (t q).length = ProtocolRAMTurnGeometry.length (names i) ∧ (t q).reverse = direction (names i) ∧
    (t q).position = j.val ∧ (t q).site = ((spines B inj pad i).visit j).val := by
  let r := raw len q
  have item : (ProtocolRAMTurnGeometry.header o base names q).item = r.1.val :=
    congrArg Fin.val ((ProtocolRAMTurnGeometry.sourceOrder edges h d k).apply_symm_apply r.1)
  refine ⟨item,rfl,rfl,?_,?_,(visit_at B inj pad q).symm⟩
  · exact (congrArg (rev v) item).trans reverseAt
  · change (if rev v ((ProtocolRAMTurnGeometry.header o base names q).item) then
        ProtocolRAMTurnGeometry.length (names r.1)-r.2.val else r.2.val) =
      (phase B inj pad (names r.1) r.2).val
    rw [item,phase_val]
    exact congrArg (fun b : Bool => if b then ProtocolRAMTurnGeometry.length (names r.1)-r.2.val else r.2.val) reverseAt


end Hierarchy.ProtocolRAMPaidTurnPlacement.Canonical

end
end OAI
