import OAI.Hierarchy.ProtocolRAMCalendarNext
import OAI.Hierarchy.TaggedWireGoodsCursor
import OAI.Hierarchy.ProtocolRAMCalendarHeld
import OAI.Hierarchy.ProbeCommodityBounds

namespace OAI
/-! # Original injection and held purchases across adjacent physical calendar dates -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedGoods
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open scoped Fin.CommRing
variable {z N k W : ℕ}
local notation "Good" => Commodity (Fin (2^z)) N k
variable (c : Mesh) (bs : StockBound.Banks) (mode : Attempt→ℕ) (width : ℕ)

def original (p : ℕ) (i : Good) := held c.inject width p*payloadUnit i

def purchased (p a j : ℕ) (m : Memory W) (i : Good) : ℕ :=
  if m (mode (.outer p a))=3 then held c.reserveSteps (PurchaseInventory.stock (bs.saved (.outer p a)) m i) j else 0

def pending (ev : Option Event) (m : Memory W) (i : Good) : ℕ :=
  original c width (phase c ev) i+
    (if bought mode ev m then held c.reserveSteps (PurchaseInventory.stock (stash bs ev) m i) (releases ev) else 0)

def entering : Event→Memory W→Good→ℕ
  | .attempt (.outer p _),_,i | .feed (.outer p),_,i => original c width p i
  | .attempt (.inner p a j _),m,i | .feed (.inner p a j),m,i =>
    original c width p i+purchased c bs mode p a j m i

def leaving : Event→Memory W→Good→ℕ
  | .attempt (.outer p a),m,i =>
    original c width p i+(if 0<c.reserveSteps then purchased c bs mode p a 0 m i else 0)
  | .attempt (.inner p a j _),m,i => original c width p i+purchased c bs mode p a j m i
  | .feed (.inner p a j),m,i => original c width p i+purchased c bs mode p a (j+1) m i
  | .feed (.outer p),_,i => original c width (p+1) i

private theorem present (e : Event) (m : Memory W) (i : Good) :
    pending c bs mode width (some e) m i=entering c bs mode width e m i := by
  rcases e with a|b
  · rcases a with ⟨p,a⟩|⟨p,a,j,t⟩ <;>
      simp [pending,entering,purchased,phase,releases,bought,stash,parent,StockBound.parent]
  · rcases b with ⟨p⟩|⟨p,a,j⟩ <;>
      simp [pending,entering,purchased,phase,releases,bought,stash,parent,StockBound.parent]

private theorem trial_start (p a : ℕ) (m : Memory W) (i : Good) :
    entering c bs mode width (nextTrialStart c p a) m i=original c width p i := by
  unfold nextTrialStart
  split <;> rfl

private theorem slice_start (p a j : ℕ) (m : Memory W) (i : Good) :
    entering c bs mode width (nextSliceStart c p a j) m i=
      original c width p i+(if j<c.reserveSteps then purchased c bs mode p a j m i else 0) := by
  by_cases hj : j<c.reserveSteps
  · by_cases fuel : 0<c.innerFuel <;> simp [nextSliceStart,hj,fuel,entering]
  · simp [nextSliceStart,hj,trial_start]

/-- At the terminal inner discharge the remaining amount is exactly zero,
including when the originally saved register was nonzero. -/
theorem pending_next (e : Event) (valid : eventInRange c e) (m : Memory W) (i : Good) :
    pending c bs mode width (nextEvent c e) m i=leaving c bs mode width e m i := by
  cases e with
  | attempt a =>
    cases a with
    | outer p a => simp only [nextEvent,present,slice_start,leaving]
    | inner p a j b =>
      by_cases following : b+1<c.innerFuel <;>
        simp [nextEvent,following,present,entering,leaving]
  | feed b =>
    cases b with
    | inner p a j =>
      have sl : j<c.reserveSteps := valid.2.2
      simp only [nextEvent,present,slice_start,leaving]
      by_cases next : j+1<c.reserveSteps
      · rw [ite_eq_left next]
      · have finalSlice : j+1=c.reserveSteps := by omega
        simp [purchased,finalSlice,held_finish _ _ (by omega : 0<c.reserveSteps)]
    | outer p =>
      change p<c.inject+c.cool at valid
      by_cases more : p+1<c.inject+c.cool
      · simp only [nextEvent,ite_eq_left more,present,trial_start,leaving]
      · have finalPhase : p+1=c.inject+c.cool := by omega
        simp [nextEvent,leaving,pending,phase,bought,parent,finalPhase]

/-- These two equations use the actual previous published bank and the
actual active/saved pair, even for the last physical event. -/
theorem at_date (u : ℕ) (on : u<(events c).length) (m : Memory W) (i : Good) :
    let e:=(events c)[u]
    PurchaseInventory.stock (previous c bs u) m i+pending c bs mode width ((events c)[u]?) m i =
      PurchaseInventory.stock (bs.previous c e) m i+entering c bs mode width e m i := by
  dsimp only
  rw [List.getElem?_eq_getElem on,present]
  simp [StockBound.Banks.previous,previousStock,previous,position_at]

theorem after_date (u : ℕ) (on : u<(events c).length) (m : Memory W) (i : Good) :
    let e:=(events c)[u]
    PurchaseInventory.stock (previous c bs (u+1)) m i+pending c bs mode width ((events c)[u+1]?) m i =
      PurchaseInventory.stock (bs.active e) m i+leaving c bs mode width e m i := by
  dsimp only
  rw [next_at c u on,pending_next c bs mode width _ ((eventInRange_iff c _).mpr (List.getElem_mem on))]
  have ok : 0<u+1 ∧ u+1≤(events c).length := by omega
  simp [previous,ok]

end Hierarchy.ProtocolRAM.Calendar.DatedGoods
end

end OAI
