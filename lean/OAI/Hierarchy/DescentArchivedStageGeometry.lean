import OAI.Hierarchy.DescentDatedOrdinaryAny
import OAI.Hierarchy.DescentPackedOrdinaryFromRows

namespace OAI
/-! # The numbered ordinary chooser fits its public allocation on the original roster -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentCompiler DescentSIMDLookup DescentPackedColony DescentColonies ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k G L ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (hosts : V≃Fin L) (hv : L≤2^ℓ)
    (b payload unit profile seats : ℕ) (input : Dated.Operands) (floor : ℕ)
local notation "H" => 2^ℓ
local notation "a" => (⟨H,G,k,b,A.degree,A.cap,payload,unit,profile,seats⟩ : Dated.Ordinary)
local notation "C" => (a).chooser input.roster floor
local notation "M" => lanes payload unit
local notation "P" => (a).matcher input.roster floor
local notation "rom" => (a).prepareAt input.roster floor
local notation "start" => (a).phaseAt floor
local notation "first" => Phase.Arena.first (C).chart A.degree k b (a).phaseWidth
local notation "rows" => H*chunks G M

theorem chooser_addresses (safe : (a).Space input w floor) :
    floor≤(C).origin ∧ floor≤ start ∧ (a).weightsAt floor≤ start ∧
    (a).weightsAt floor≤rom ∧ first≤(P).raw.base ∧ (P).endAddr<2^w ∧
    Chooser.Apart (G:=G) (ℓ:=ℓ) A C b (2*A.cap) payload unit floor :=by
  obtain ⟨s,c,w₁,m,p⟩:=(a).origin_order floor
  have firstWin : first≤(a).winnerEnd input.roster floor:=by
    repeat first | rfl | apply Nat.le_add_right_of_le
  have win : (a).winnerEnd input.roster floor≤rom:=Nat.le_add_right ..
  have startWin:=(a).phase_before_winners input.roster floor
  have printed : rom≤(a).sorterAt input.roster floor:=by
    repeat first | rfl | apply Nat.le_add_right_of_le
  have sort : (a).sorterAt input.roster floor≤(a).matcherAt input.roster floor:=
    (Nat.le_add_right _ (Prepare.rosterBank _ H A.degree).size).trans (le_max_right ..)
  have source : (a).matcherAt input.roster floor≤(P).raw.base:=by
    repeat first | rfl | apply Nat.le_add_right_of_le
  have roof:=((a).packed_last input.roster floor).2
  have end_:=(a).flag_at input.roster floor
  have pad : (a).batch≤2^Nat.clog 2 (a).batch:=Nat.le_pow_clog (by decide) _
  have raw : (P).endAddr≤(a).flagEnd input.roster floor:=by omega
  have bound : (a).flagEnd input.roster floor≤(a).rotationEnd input.roster floor:=
    (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have had : input.roster.base+H*A.degree≤floor:=
    (Nat.add_le_add_left safe.accessible.rosterRoom _).trans safe.accessible.roster.2.2
  have phaseOld : (a).weightsAt floor≤ start:=by omega
  exact ⟨show floor≤(a).censusAt floor by omega,by omega,phaseOld,phaseOld.trans (startWin.trans win),
    firstWin.trans (win.trans (printed.trans (sort.trans source))),raw.trans_lt (bound.trans_lt safe.endAddress),
    ⟨Or.inr c,Or.inr (c.trans (w₁.trans phaseOld)),Or.inl had⟩⟩

set_option maxHeartbeats 1000000 in
theorem roster_geometry (ratio : ℕ) (rs : DynamicSplit.Roster ℓ A.degree)
    (safe : (a).Space input w floor) (hardware : w≤ratio*payload)
    (near : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v u : V,i=(hosts v).castLE hv ∧ j=(hosts u).castLE hv ∧ v∈A.near u)
    (mass : A.wire*(A.z*gadget.b)*A.cap<2^b) (positions : G*H*2^k<2^w) (core : W.core.card<2^w) :
    Chooser.Geometry (G:=G) (w:=w) A hosts hv C b (2*A.cap) payload unit ratio rs :=by
  have bound:=chooser_addresses (G:=G) (ℓ:=ℓ) A b payload unit profile seats input floor safe
  obtain ⟨s,c,w₁,m,p⟩:=(a).origin_order floor
  have rawEnd : (P).raw.base≤(P).endAddr:=by
    repeat first | rfl | apply Nat.le_add_right_of_le
  have room : first<2^w:=bound.2.2.2.2.1.trans_lt (rawEnd.trans_lt bound.2.2.2.2.2.1)
  have startCap : start<2^w:=by
    have layout:=(a).phase_room input w floor A.fieldBits safe
    have order : start≤first :=
      (show start≤Phase.Arena.menu (C).chart A.degree k from Nat.le_add_right ..).trans
      ((show Phase.Arena.menu (C).chart A.degree k≤Phase.Arena.names (C).chart A.degree k (a).phaseWidth
        from Nat.le_add_right ..).trans (Nat.le_add_right ..))
    exact order.trans_lt room
  have page : (a).page<2^w := (Nat.le_add_left (a).page ((a).markedAt floor)).trans_lt startCap
  have «prefix» : floor≤(a).weightsAt floor:=by omega
  refine ⟨safe.chooserWidth,safe.laneWidth,hardware,safe.embed,near,(a).phase_room input w floor A.fieldBits safe,
    mass,positions,core,⟨Nat.two_pow_pos _,page,?_⟩,(a).rows_fit,le_refl _,p.trans_lt startCap,m,
    safe.accessible.roster.2.2.trans «prefix»⟩
  change (a).censusAt floor≤(a).weightsAt floor
  exact w₁

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
