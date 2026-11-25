import OAI.Hierarchy.ProtocolRAMCalendarGlobalCalibration
import OAI.Hierarchy.ProtocolRAMCalendarGlobalRoom
import OAI.Hierarchy.ProtocolRAMCalendarGlobalHeader
import OAI.Hierarchy.ProtocolRAMCalendarMount

namespace OAI
/-! # Reading the shared score ROM at an actual live native trial -/

namespace Hierarchy.ProtocolRAM.Calendar.GlobalTests
open Computability.VPVNP.BurstRAM PrivateRAM
open AdaptiveProbe AdaptiveProbe.OuterBank AttemptGate
open scoped Classical
noncomputable section
variable {w z N k q d : ℕ}

/-- A protected immutable header survives every whole and partial physical phase,
from the initial startup image to the current attempt. -/
theorem Resident.trial {l : Layout} {s : PhasePrice} {initial : Memory w}
    (R : Resident l z N k s initial) (C : Chart w q d) (p a : ℕ)
    (mounted : Calendar.mounted C (events C.mesh) initial) (hp : p<C.mesh.inject+C.mesh.cool) (ha : a≤C.mesh.outerFuel)
    (fixed : ∀e∈events C.mesh,∀u,l.base≤u→u<stop l z N k→protected C u e) :
    Resident l z N k s (trialState C initial p a) := by
  apply R.transport
  intro u lo hi
  have phases (i) (h : i≤C.mesh.inject+C.mesh.cool) : phaseState C initial i u=initial u := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [phase_block]
      exact (run_frame C _ _ _ (phase_mounted mounted (by omega))
        (fun e he=>fixed e (List.mem_flatMap.mpr ⟨i,List.mem_range.mpr (by omega),he⟩) u lo hi)).trans
        (ih (by omega))
  have trial (i) (h : i≤C.mesh.outerFuel) : trialState C initial p i u=phaseState C initial p u := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have head := trial_mounted mounted hp (show i<C.mesh.outerFuel by omega)
      have move : trialState C initial p (i+1)=run C (trialBlock C.mesh p i) (trialState C initial p i) := by
        simp only [trial_succ,trialBlock,run]
        rfl
      rw [move]
      apply (run_frame C _ _ _ head ?_).trans (ih (by omega))
      intro e he
      apply fixed e _ u lo hi
      apply List.mem_flatMap.mpr
      refine ⟨p,List.mem_range.mpr hp,List.mem_append_left _ ?_⟩
      exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr (by omega),he⟩
  exact (trial a ha).trans (phases p hp.le)

/-- Numeric startup and the true live coordinate of each commodity suffice for
all score-word readback obligations. Every entry fits uniformly for all possible
stocks by the public lane bounds. -/
theorem ReadStock.at_trial (A : AccountColumns (Goods z N k)) (C : Chart w q d)
    (initial : Memory w) (l : Layout) (stocks : Bank) (s : PhasePrice) (p a : ℕ)
    (start : Resident l z N k s initial) (whole : Calendar.mounted C (events C.mesh) initial)
    (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel)
    (fixed : ∀e∈events C.mesh,∀u,l.base≤u→u<stop l z N k→protected C u e)
    (stockAt : ∀i,A.stockAt (.outer p a) i=stocks.base+PurchaseInventory.slot i)
    (rowsFit : rows z N k<2^w) (indices : rows z N k≤2^l.indexBits) (stockCap : rows z N k≤ stocks.size)
    (spanFit : span l N k<2^w) (tableCap : span l N k≤2^l.indexBits)
    (limit : ∀i,(A.trial C initial p a).bits i<l.stride) (unitFits : unitBound l N k s<2^w)
    (aPos : 0<s.a) (bPos : ∀i<kinds N k,0≤ s.bonus i) (mPos : 0≤ s.M)
    (tPos : 0<s.time) (cPos : ∀i<kinds N k,0≤ s.cap i) :
    ReadStock A (A.trial C initial p a) l stocks s (trialState C initial p a) := by
  let E := PurchaseInventory.slotEquiv z N k
  have bits (j : Fin (rows z N k)) :
      ((trialState C initial p a) (stocks.base+j.val)).val=(A.trial C initial p a).bits (E.symm j) := by
    change _=((trialState C initial p a) (A.stockAt (.outer p a) (E.symm j))).val
    rw [stockAt]
    have key := congrArg Fin.val (E.apply_symm_apply j)
    change PurchaseInventory.slot (E.symm j)=j.val at key
    rw [key]
  refine ⟨start.trial C p a whole hp ha.le fixed,rowsFit,indices,stockCap,spanFit,tableCap,
    fun i=>by rw [bits i];exact limit _,?_,bits⟩
  intro b i
  exact (valueWord_le l s b (kind i) _ aPos (bPos _ (kind i).isLt) mPos tPos (cPos _ (kind i).isLt)).trans_lt unitFits

end
end Hierarchy.ProtocolRAM.Calendar.GlobalTests

end OAI
