import OAI.Hierarchy.DescentPackedMatchStageCounts
import OAI.Hierarchy.DescentPackedMatchRoster
import OAI.Hierarchy.DescentPackedMatchReceived
import OAI.Hierarchy.DescentPackedMatchWindowRoom

namespace OAI
/-! # Profiles of the normalized branch at their actual native matched seats -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup DescentPackedProfileWindow
open DescentTerminalEpochDecoder DescentKernelHistory.BitDescription DescentTerminalEpochFlags
open Computability.VPVNP.BurstRAM DescentSixParty.StarKeys Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε) (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "keyCount" => 2^(k+1)
local notation "N" => (keyCount*H)*chunks G M
local notation "C" => ScanColonies he A.stage
local notation "panel" => terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank)
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "ord" => slot he A groups hosts hm
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (profile : ℕ)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "real" => spread groups hosts panel
local notation "descriptors" => Gather.flat (Gather.descriptorInputs (K:=keyCount) s A.cap real)
local notation "ks" => topologyWords (M:=M) s descriptors

include coord named fit winner df in
theorem measured :
    Chronology.Counts ord (countIn he A) (fun i=>laneCounts s M (ks i)) :=
  all_counts A native S ready (cableNames k rank) win (rotor A rank) he groups hosts hm rank coord named fit winner
    (rotor_sorted A rank) (rotor_routes A native S ready rank) df profile

include coord named fit winner df in
theorem original_digit (choice : (A.stage.result he).Choice) (stream : ℕ→Cell (s).digit)
    (pins : ∀q,(stream q).val=profileAt (inputNumber he A groups hosts) ((scannedRows he A.stage).profile choice) q)
    (base : ℕ) (o : Memory w) (posted : ∀i : Fin N,∀a : Fin M,∀j : Fin (s).pairs,
      digit (s).digit (finProdFinEquiv (a,j)).val (o (base+i.val)).val =
        if j.val<(laneCounts s M (ks i) a).val then
          (stream (PackedProfileCursor.total (ProfileTable.quota s ks) i.val+
            localPrefix (laneCounts s M (ks i)) a+j.val)).val else 0)
    (c : C) (e : Matched T A.cap (thinList home color c) (thickList home color c)) :
    let j:=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val
    ∃u : Fin (s).pairs,u.val=j ∧ digit (s).digit (finProdFinEquiv ((ord c).2,u)).val (o (base+(ord c).1.val)).val =
      DescentTerminalEpochFlags.encode ((scannedRows he A.stage).profile choice ⟨c,e⟩) := by
  let counts:=measured A native S ready rank win he groups hosts hm coord named fit winner df profile
  let j:=pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e
  have counted:=counts.live c
  have alive : j.val<(laneCounts s M (ks (ord c).1) (ord c).2).val := counted.symm ▸ j.isLt
  let u : Fin (s).pairs:=⟨j.val,alive.trans_le (Nat.le_of_lt_succ (laneCounts s M _ _).isLt)⟩
  refine ⟨u,rfl,?_⟩
  have start:=Chronology.address ord (countIn he A) _ counts c
  let name:=(sourceChart he A groups hosts).trans Fin.valEmbedding
  have order (a b : C) : Chronology.rank ord a<Chronology.rank ord b ↔ name a<name b := by
    rw [Chronology.rank_val,Chronology.rank_val]
    exact seatOf_order k (nativeAddress he A.stage) (nativeAddress_legal he A.stage) groups hosts hm a b
  have loc : PackedProfileCursor.total (ProfileTable.quota s ks) (ord c).1.val+
      localPrefix (laneCounts s M (ks (ord c).1)) (ord c).2=beforeSource he A groups hosts c :=
    start.trans (before_padded (Chronology.rank ord) name (countIn he A) order c)
  rw [posted,ite_eq_left alive,loc,pins]
  exact consumes he A groups hosts choice c e

include coord named fit winner df in
theorem raw_room {R : ℕ} (bank : ProtocolRAM.Bank) (seats : ℕ)
    (cap : Fintype.card (NativePair W.graph W.core home color A.cap)≤ seats) (room : seats/R+2≤bank.size) :
    ∀i : Fin N,PackedProfileCursor.total (ProfileTable.quota s ks) i.val/R+1<bank.size := by
  by_cases lanes : 0 < M
  · have sums : (∑c : C,countIn he A c)=Fintype.card (NativePair W.graph W.core home color A.cap) := Fintype.card_sigma.symm
    exact ProfileTable.window_room s ks (slot he A groups hosts lanes) (countIn he A)
      (measured A native S ready rank win he groups hosts lanes coord named fit winner df profile)
      seats (sums.le.trans cap) bank room
  · intro i
    have hi := i.isLt
    simp [show M = 0 by omega, chunks, ThreeFlat.Routing.poolBatchCount] at hi

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
