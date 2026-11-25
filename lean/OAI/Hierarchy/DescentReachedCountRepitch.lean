import OAI.Hierarchy.DescentReachedCountRepackSpace
import OAI.Hierarchy.DescentReachedCountRepackBill
import OAI.Hierarchy.DescentReachedCountActual
import OAI.Hierarchy.DescentVenueExprTariff
import OAI.Hierarchy.DescentStageVenueWireRoom

namespace OAI
/-! Copy the original paid blocks to the pitch used by the ordinary actor gather. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch
open DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSixParty.Chronology DescentOrdinaryRasterReturn DescentSharedCableNames ProtocolRAM ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable (H G old M k paths b : ℕ)
local notation "S" => shape H G old M k b
local notation "L" base => count H G old M k paths b base
def pages (base j : ℕ) : Expr := .lookup (DescentVenueSlabs.page (S) base j) .row
def phase (base w : ℕ) (P : Ports paths) (atom : ℕ→Expr) : NativePhase w :=
  (DescentVenueSlabs.ExprInputs.phase (S) (fun j=>atom j.val) base w).seq
    ⟨(L base).program w P (pages H G old M k b base), (L base).ticks P (pages H G old M k b base),
    (L base).output P (pages H G old M k b base),
    cheap_seq (cheap_seq (@ProtocolRAM.program_cheap _ _) (ROM.cheap _ _ _ _)) (@scan_cheap _ _ _ _)⟩

theorem intervals (base : ℕ) : base≤(L base).base ∧ (L base).base≤(L base).roof := by
  refine ⟨?_,?_⟩
  · change base≤DescentVenueSlabs.endAddress (S) base
    rw [DescentVenueSlabs.translates];omega
  · change _≤(((_+_)+_)+_)
    omega

private theorem available {w} (base : ℕ) (room : (L base).roof<2^w) :
    ∀j<2^k,(pages H G old M k b base j).Fits w (L base).base :=
  fun j hj=>⟨(DescentVenueSlabs.page_room (S) base w ⟨j,hj⟩
    ((intervals H G old M k paths b base).2.trans_lt room)).1,trivial⟩

theorem any {w : ℕ} (base : ℕ) (P : Ports paths) (witness : Bank) (atom : ℕ→Expr) (m : Memory w)
    (early : ∀j<2^k,(atom j).Fits w base) (acc : Accessible P witness H G M w base)
    (room : (L base).roof<2^w) :
    let p:=phase H G old M k paths b base w P atom
    p.Runs m ∧ ∀a,a < base ∨ (L base).roof ≤ a→p.image m a=m a := by
  intro p
  obtain ⟨before,top⟩:=intervals H G old M k paths b base
  let front:=DescentVenueSlabs.ExprInputs.phase (S) (fun j=>atom j.val) base w
  obtain ⟨cpu,same⟩:=DescentVenueSlabs.ExprInputs.any (S) (fun j=>atom j.val) base m
    (fun j=>early _ j.isLt) (top.trans_lt room)
  obtain ⟨tail_,_,stay⟩:=(L base).any P witness _ (front.image m)
    (available H G old M k paths b base room) (RoleControl.Layout.accessible_after acc before) room
  refine ⟨NativePhase.seq_runs front _ m cpu tail_,?_⟩
  intro a ha
  rcases ha with lo|hi
  · exact (stay a (.inl (lo.trans_le before))).trans (same a (.inl lo))
  · exact (stay a (.inr hi)).trans (same a (.inr (top.trans hi)))

theorem run {w : ℕ} (base : ℕ) (P : Ports paths) (witness : Bank) (atom : ℕ→Expr) (m : Memory w)
    (walks : Fin H→Fin paths→Option (Fin H)) (prior : Fin (2^k)→Fin H→Fin G→Cell b)
    (early : ∀j<2^k,(atom j).Fits w base) (reads : ∀x : Fin (2^k),Source (atom x.val) (prior x) old m)
    (oldPos : 0 < old) (acc : Accessible P witness H G M w base)
    (mounted : Mounted P (DescentSortedRoster.indexed walks) m G M)
    (room : (L base).roof<2^w) :
    let p:=phase H G old M k paths b base w P atom
    p.Runs m ∧ Source (L base).expr (fun h g=>encode b (paths*2^k) (priorValue walks prior h g)) M (p.image m) ∧
    ∀a,a < base ∨ (L base).roof ≤ a→p.image m a=m a := by
  intro p
  let front:=DescentVenueSlabs.ExprInputs.phase (S) (fun j=>atom j.val) base w
  obtain ⟨before,top⟩:=intervals H G old M k paths b base
  obtain ⟨cpu,issued,frame_⟩:=DescentVenueSlabs.ExprInputs.issued (S) (fun j=>atom j.val) base m prior
    (fun j=>early _ j.isLt) reads oldPos (top.trans_lt room)
  have src (x : Fin (2^k)) : Source (pages H G old M k b base x.val) (prior x) M (front.image m) := by
    obtain ⟨fit,cap⟩:=DescentVenueSlabs.page_room (S) base w x (top.trans_lt room)
    exact source_column _ _ fit _ _ cap (issued x)
  have tail_:=(L base).run P witness _ (front.image m) walks prior (available H G old M k paths b base room)
    src (RoleControl.Layout.accessible_after acc before)
    (RoleControl.Layout.previous_mounted acc _ (fun a ha=>frame_ a (.inl ha)) mounted) room
  exact ⟨NativePhase.seq_runs front _ m cpu tail_.1,tail_.2.2.1,
    (any H G old M k paths b base P witness atom m early acc room).2⟩

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch

end OAI
