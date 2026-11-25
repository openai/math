import OAI.Hierarchy.TaggedWideFrozenSlots
import OAI.Hierarchy.TaggedWideFrozenSeries
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # Executing a frozen window from its original injective socket directory -/

noncomputable section
namespace Hierarchy.ProtocolRAMFrozenWindow
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAMReportedPorts ProtocolRAMPackedPlacement Tagged.WideStack
open scoped Classical Fin.CommRing

variable {W : ℕ} (s : Format) (ports lanes : ℕ)
variable (a : Inputs) (old : Fin (s.withSlots ports lanes).N → ProtocolRAMEmit.Row) (before : Memory W)
    (fit : (s.withSlots ports lanes).Limits W old)
variable (port : Bool → Fin (s.withSlots ports lanes).N → Fin ports)
    (anchor : Live old (s.withSlots ports lanes).w × Bool ↪ Fin (s.withSlots ports lanes).groups × Fin ports)
    (owner : ∀j b,(anchor (j,b)).1.val=(old j.val).group)
    (pin : ∀j b,(anchor (j,b)).2=port b j.val)
    (lanesFit : ∀j,pieces old (s.withSlots ports lanes).w j ≤ lanes)
    (groupRead : ∀(j : Fin (s.withSlots ports lanes).N),0 < pieces old (s.withSlots ports lanes).w j →
      ((s.withSlots ports lanes).rows a before old j).group=(old j).group)
    (slotRead : ∀b (j : Live old (s.withSlots ports lanes).w),(s.withSlots ports lanes).starts a before b j.val=(port b j.val).val*lanes)

include port anchor owner pin lanesFit groupRead slotRead in
/-- Distinct original endpoints and the bound on the number of pieces per
endpoint place every live rank within this group's physical slot bank. These
properties hold before pricing the collection of groups. -/
def Format.unpricedAnchor : (s.withSlots ports lanes).Anchored a before old fit := by
  let fmt := s.withSlots ports lanes
  let records := fmt.rows a before old
  let live := Live old fmt.w
  let inj (g : Fin fmt.groups) (b : Bool) : PortDistinct records fmt.w fmt.menu fmt.γ g.val (port b) :=
    portDistinct_of_grouped records fmt.w fmt.menu fmt.γ (port b)
      ((Function.Embedding.sectL _ b).trans anchor)
      (fun j => (owner j b).trans (groupRead j.val j.property).symm) (fun j => pin j b) g
  let pl (g : Fin fmt.groups) (b : Bool) :=
    (common records fmt.w fmt.menu fmt.γ g.val fit.order.injective).symm.toEmbedding.trans
      (staticUnit records g port (inj g) lanesFit (Nat.le_refl (ports*lanes)) b)
  refine ⟨?_,?_,pl,?_⟩
  · intro j hj
    let v : live := ⟨j,hj⟩
    rw [groupRead j hj]
    exact (owner v false) ▸ (anchor (v,false)).1.isLt
  · exact fun g => static_capacity records fit.order.injective g port (inj g) lanesFit (Nat.le_refl (ports*lanes))
  · intro b g u
    change ((staticUnit records g port (inj g) lanesFit (Nat.le_refl (ports*lanes)) b)
      ((common records fmt.w fmt.menu fmt.γ g.val fit.order.injective).symm
        (common records fmt.w fmt.menu fmt.γ g.val fit.order.injective u))).val=_
    rw [Equiv.symm_apply_apply]
    rcases u with ⟨i,j⟩
    let v : live := ⟨i.val,Nat.zero_lt_of_lt j.isLt⟩
    change j.val+lanes*(port b v.val).val=fmt.starts a before b v.val+j.val
    rw [slotRead b v]
    ac_rfl

include fit port anchor owner pin lanesFit groupRead slotRead in
/-- Every such physical format has the original exact clock and preserves its
prefix for all initial memories agreeing on the immutable input. -/
theorem Format.phase_exec_frame {r floor : ℕ} (resident : (s.withSlots ports lanes).Resident W floor a)
    (ready : (s.withSlots ports lanes).Ready W r a) (data : (s.withSlots ports lanes).InputWords r a old before)
    (current : Memory W) (retain : ∀j<floor,current j=before j) :
    ∃out,((s.withSlots ports lanes).phase W r a).Exec current out ((s.withSlots ports lanes).clock r a) ∧ ∀j< r,out j=current j := by
  let anchored := Format.unpricedAnchor (s := s) (ports := ports) (lanes := lanes)
    (a := a) (old := old) (before := before) (fit := fit) (port := port) (anchor := anchor)
    (owner := owner) (pin := pin) (lanesFit := lanesFit) (groupRead := groupRead) (slotRead := slotRead)
  obtain ⟨out,ran,_,frame⟩ := anchored.run resident retain old ready data fit
  exact ⟨out,ran,frame⟩

end Hierarchy.ProtocolRAMFrozenWindow
end

end OAI
