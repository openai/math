import OAI.Hierarchy.DescentPackedOwnerWord
import OAI.Hierarchy.DescentPackedActorPack
import OAI.Hierarchy.DescentPackedTypedHead

namespace OAI
/-! # The resolved relative venue of each original tape site -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM PackedLocalMatch
open scoped Classical BigOperators
noncomputable section

theorem thick_self {r D p b : ℕ} (u : Panel r D p b) (x : Fin r) :
    thickAddress u false x.val=(0,leaf (u.winner x).val,0) := by
  simp [thickAddress,Nat.mod_eq_of_lt x.isLt,x.isLt]

theorem thick_peer {r D p b : ℕ} (u : Panel r D p b) (v : Fin D) (x : Fin r) :
    thickAddress u true (v.val*r+x.val)=(v.val+1,leaf (u.peerWinner v x).val,0) := by
  have hi : (v.val*r+x.val)/r=v.val := by
    rw [Nat.mul_comm v.val r,Nat.mul_add_div x.pos,Nat.div_eq_of_lt x.isLt,Nat.add_zero]
  have lo : (v.val*r+x.val)%r=x.val := by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt x.isLt]
  simp [thickAddress,hi,lo,x.isLt,v.isLt]

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "T" => nativeTraffic N W.core home
local notation "n" => binCount (2^k) A.degree
variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 +
        (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
    (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f) (profile : ℕ) (c : ScanColonies he A.stage)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "pk" => slabPacking T A.cap (thinList home color c) (thickList home color c)
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)


include fit winner in
theorem winner_leaf (u : (N).Site) :
    leaf ((panel (A.pos u)).winner (A.block u)).val=heap (addr (home u)).2 := by
  rw [real_winner A native S ready names win next u (fit u),winner u]
  cases color u <;> simp [leaf]; omega

include fit winner route in
theorem thick_location (e : Pair) (l : Bool) :
    let ac:=picked A he c e true
    let q:=thickAddress (panel (addr c).1) l (rawTriple A native S ready names he c true ac (if l then 2 else 1))
    let receiving:=if l then (N).dst ac.val else (N).src ac.val
    location next (addr c).1 q=some (A.pos receiving) ∧ q.2=(heap (addr (home receiving)).2,0) := by
  let ac:=picked A he c e true
  let v:=target A native S ready names ((addr c).1,A.block ((N).src ac.val)) (event A he c true ac).2
  have source : A.pos ((N).src ac.val)=(addr c).1 := by rw [←source_host A he ((N).src ac.val),ac.property.2.1]
  have target := route (addr c).1 (A.block ((N).src ac.val)) (event A he c true ac).2
  change next (addr c).1 v=some (A.pos ((N).dst ac.val)) at target
  have same:=A.same ac.val
  have incoming : (panel (addr c).1).peerWinner v (A.block ((N).src ac.val))=(panel (A.pos ((N).dst ac.val))).winner (A.block ((N).dst ac.val)) := by
    change ((next (addr c).1 v).elim 0 fun h'=>gated _ _ (win h' _))=_
    rw [target,same]
    rfl
  cases l with
  | false=>
    let q := thickAddress (panel (addr c).1) false (A.block ((N).src ac.val)).val
    change location next (addr c).1 q=some (A.pos ((N).src ac.val)) ∧
      q.2=(heap (addr (home ((N).src ac.val))).2,0)
    dsimp only [q]
    rw [thick_self]
    exact ⟨by simpa [location] using congrArg some source.symm,
      Prod.ext (by rw [←source]; exact winner_leaf A native S ready names win next he fit winner _) rfl⟩
  | true=>
    let q := thickAddress (panel (addr c).1) true (v.val*2^k+(A.block ((N).src ac.val)).val)
    change location next (addr c).1 q=some (A.pos ((N).dst ac.val)) ∧
      q.2=(heap (addr (home ((N).dst ac.val))).2,0)
    dsimp only [q]
    rw [thick_peer]
    exact ⟨by simpa [location,v.isLt] using target,
      Prod.ext (by rw [incoming]; exact winner_leaf A native S ready names win next he fit winner _) rfl⟩

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
