import OAI.Hierarchy.DescentPrimitiveProfileField
import OAI.Hierarchy.DescentOrdinaryAtomFieldRAM
import OAI.Hierarchy.DescentPackedMatchDonorRead
import OAI.Hierarchy.DescentPackedOrdinaryBirths
import OAI.Hierarchy.DescentFreshRoleFields
import OAI.Hierarchy.DescentEpochTagKeys

namespace OAI
/-! # Primitive fields at the actual accepted thick donor's normalized occurrence -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
def freshArity {F : Type} [Field F] (g : PoweredGadget F) (width cut : ℕ) := profileField width (DescentFreshRoleFields.arity g cut)
def freshWidth {F : Type} [Field F] (g : PoweredGadget F) (width operand : ℕ) := profileField width (fun z p q=>
  if valid : operand<Fintype.card (DescentKernelHistory.RolePort q) then DescentFreshRoleFields.widths g z p q ⟨operand,valid⟩ else 0)


variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "p" => 2*A.cap
local notation "names" => cableNames k rank
local notation "peers" => rotor A rank
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "C" => ScanColonies he A.stage
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real)
local notation "seat" => slot he A groups hosts hm
variable (b : ℕ) (m : Memory w) (sumSize : (shape (2^k) A.degree (2*A.cap) profile).outputBits*M≤w)
    (stored : ∀i : Fin ((2^(k+1)*H)*chunks G M),
      m (b+i.val)=((topologyWords (M:=M) (shape (2^k) A.degree (2*A.cap) profile)
        (Gather.flat (Gather.descriptorInputs («K»:=2^(k+1)) (shape (2^k) A.degree (2*A.cap) profile) A.cap
          (spread groups hosts (terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank))))) i).val:Word w))
variable (c : ScanColonies he A.stage)
local notation "num" => pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)
local notation "x" => inputs s A.cap (heap (addr c).2) (panel (addr c).1) (fun _=>0)


include coord named fit winner df edgeOrder sumSize stored in
theorem actual_birth {width : ℕ} (f : ℕ→ℕ→Fin 6→Cell width) (z prof : ℕ) (e : Pair) (role : Fin 6)
    (issued : Cell (SixBirths.width s M))
    (six : ∃j : Fin (s).pairs,j.val=(num e).val ∧ let at_:=(SixBirths.slot (seat c).2 j role).val
      SixBirths.atom z (digit ((s).digit+1) at_ issued.val) at_=some (z,prof,role.val)) :
    let prior:=topologyWords (M:=M) s fieldsAt (seat c).1
    let code:=word (s).digit (rawTriple A native S ready names he c true (picked A he c e true) 0)
    digit width (seat c).2.val (bornField s M z f code role prior issued).val=(f z prof role).val := by
  intro prior code
  let v:=picked A he c e true
  obtain ⟨j,rank_,emitted⟩:=six
  have natural : code.val=rawTriple A native S ready names he c true v 0:=raw_val A native S ready names he profile c true v 0
  have limit : prior.val<2^w:=prior.isLt.trans_le (Nat.pow_le_pow_right (by decide) sumSize)
  let record:=decodeOutput s ((encode (s).outputBits M).symm prior (seat c).2)
  have old (q : Fin (s).pairs) (field : Fin 12) : (record.row q field).val=donorWord s m b (seat c) q field := by
    change ((decodeOutput s ((encode (s).outputBits M).symm prior (seat c).2)).row q field).val=_
    rw [decoded_digit,unpack_digit,donorWord,stored,Fin.val_cast_of_lt limit]
  apply born_at s M z f code role prior issued (seat c).2 j prof _ emitted
  apply reverse_of_unique
  intro q
  have marked:=chosen_thick_iff A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder profile b m sumSize stored c q v
  change decide ((record.row q 0).val=1 ∧ record.row q 8=code)=true ↔ q=j
  rw [decide_eq_true_eq]
  have readId : record.row q 8=code ↔ donorWord s m b (seat c) q 8=rawTriple A native S ready names he c true v 0 := by
    rw [Fin.ext_iff,old,natural]
  rw [old,readId,marked]
  have same (e' : Pair) (eqn : (picked A he c e' true).val=v.val) : e'=e := by
    change (picked A he c e' true).val=(picked A he c e true).val at eqn
    rw [picked_old,picked_old] at eqn
    have pair := congrArg Prod.fst ((colorPick W.graph W.core home color A.cap).injective eqn)
    exact eq_of_heq (Sigma.mk.inj pair).2
  constructor
  · rintro ⟨e',⟨val,wire⟩,_⟩;rw [same e' wire] at val;exact Fin.ext (val.symm.trans rank_.symm)
  · rintro rfl;exact ⟨e,⟨rank_.symm,rfl⟩,fun other h=>same other h.2⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
