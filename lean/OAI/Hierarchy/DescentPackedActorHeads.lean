import OAI.Hierarchy.DescentDonorNumericHeads
import OAI.Hierarchy.DescentPackedActorOwnerRAM
import OAI.Hierarchy.DescentRawCableRoles

namespace OAI
/-! # An old actor and six optional born-party owners from its signed donor window -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM PackedLocalMatch
open scoped Classical BigOperators
noncomputable section

def walkSite {Z : Type} {D : ℕ} (next : Z→Fin D→Option Z) (root : Z) (w : Walk) : Option Z :=
  (location next root (w.1,0,0)).bind (fun atSite=>location next atSite w.2)
def walked {Z : Type} {D : ℕ} (next : Z→Fin D→Option Z) (root : Z) (w : Walk) (truth : DescentHostDirectory.Key Z) : Prop :=
  walkSite next root w=some truth.1 ∧ w.2.2=(heap truth.2.1,truth.2.2)

theorem destination_unpack {r D : ℕ} (v : Fin D) (b : Fin r) :
    ((v.val*r+b.val)/r+1,(v.val*r+b.val)%r)=(v.val+1,b.val) := by
  have hi : (v.val*r+b.val)/r=v.val := by
    rw [Nat.mul_comm v.val r,Nat.mul_add_div b.pos,Nat.div_eq_of_lt b.isLt,Nat.add_zero]
  rw [hi,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt b.isLt]

private theorem walked_self {Z : Type} {r D : ℕ} (next : Z→Fin D→Option Z) (root : Z)
    (own : Fin r→Address) (peer : Fin D→Fin r→Address) (x : Fin r)
    (key : DescentHostDirectory.Key Z) (found : located next root (own x) key) :
    walked next root (look own peer (0,x.val)) key := by
  simpa [walked,walkSite,look,location,located,x.isLt] using found

private theorem walked_peer {Z : Type} {r D : ℕ} (next : Z→Fin D→Option Z) (root toSite : Z)
    (own : Z→Fin r→Address) (v : Fin D) (x : Fin r) (key : DescentHostDirectory.Key Z)
    (found : located next toSite (own toSite x) key) (link : next root v=some toSite) :
    walked next root (look (own root) (fun i b=>(next root i).elim (0,0,0) (fun z=>own z b)) (v.val+1,x.val)) key := by
  simpa [walked,walkSite,look,location,located,x.isLt,v.isLt,link] using found

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


variable (same : ∀e∈W.core, scanColorAt he A.stage (W.graph.src e) = scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "P" => coloredPack N W.core home color A.cap
local notation "pick" => colorPick N W.core home color A.cap
local notation "venue" => newSite N pick lay P
local notation "key" => nativeKey N W.core home color A.cap addr same lay
local notation "raw" => packAddress N W.core home color A.cap addr
local notation "owner" => resolve (chosenSlot N W.core home color A.cap) (chosenCenter N W.core home color A.cap lay)


local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "peers" => fun h v x=>Option.elim (next h v) (0,0,0) (fun other=>here other x)
local notation "program" => fun h x i=>actorHeads A.cap profile (panel h) lay (here h) (peers h) x i

include rank coord named fit winner sorted route df edgeOrder in
theorem prior_head (u : (N).Site) (i : Fin (2*A.cap)) :
    walked next (A.pos u) ((program (A.pos u) (A.block u) i).old) (key (venue (.inl u))) := by
  have v:=old_location A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile same lay u
  exact walked_self next (A.pos u) (here (A.pos u)) (peers (A.pos u)) (A.block u) _ v

include rank coord named fit winner sorted route df edgeOrder in
theorem endpoint_walk (e : Pair) (side : Bool) (target_ : Bool) :
    let cable:=picked A he c e side
    let x:=A.block ((N).src cable.val)
    let peer:=target A native S ready names ((addr c).1,x) (event A he c side cable).2
    let enter:=(if target_ then peer.val+1 else 0,x.val)
    let receive:=if target_ then (N).dst cable.val else (N).src cable.val
    walked next (addr c).1 (look (here (addr c).1) (peers (addr c).1) enter) (key (venue (.inl receive))) := by
  let cable:=picked A he c e side
  let x:=A.block ((N).src cable.val)
  let v:=target A native S ready names ((addr c).1,x) (event A he c side cable).2
  have root : A.pos ((N).src cable.val)=(addr c).1 := by rw [←source_host A he ((N).src cable.val),cable.property.2.1]
  have link:=route (addr c).1 x (event A he c side cable).2
  change next (addr c).1 v=some (A.pos ((N).dst cable.val)) at link
  cases target_ with
  | false=>
    have old:=old_location A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile same lay ((N).src cable.val)
    rw [root] at old
    exact walked_self next (addr c).1 _ _ x _ old
  | true=>
    have old:=old_location A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile same lay ((N).dst cable.val)
    have blockEq : x=A.block ((N).dst cable.val):=A.same cable.val
    exact walked_peer next (addr c).1 (A.pos ((N).dst cable.val)) here v x _
      (by rw [blockEq]; exact old) link

include rank coord named fit winner sorted route df edgeOrder in
theorem born_walk (e : Pair) (row : Fin 12→Cell (s).digit)
    (fields : ∀b : Bool,∀f : Fin 3,
      (row ⟨(if b then 8 else 5)+f.val,by have hf:=f.isLt; split <;> omega⟩).val=
        rawTriple A native S ready names he c b (picked A he c e b) f) (t : Fin 6) :
    walked next (addr c).1 (look (here (addr c).1) (peers (addr c).1) (@bornRoot (s) row lay t (2^k)))
      (key (venue (.inr (⟨c,e⟩,t)))) := by
  let wire (side : Bool):=picked A he c e side
  let x (side : Bool):=A.block ((N).src (wire side).val)
  let v (side : Bool):=target A native S ready names ((addr c).1,x side) (event A he c side (wire side)).2
  have root : (row 9).val=(x true).val := fields true 1
  have targetField (side : Bool) : (row (if side then 10 else 7)).val=(v side).val*2^k+(x side).val := by
    cases side with
    | false => exact fields false 2
    | true => exact fields true 2
  have src := endpoint_walk A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c same lay e true false
  have dst (side : Bool):=endpoint_walk A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c same lay e side true
  have anchored : venue (.inr (⟨c,e⟩,t)) =
      venue (.inl (StarKeys.endpoint N pick ⟨c,e⟩ (cluster lay t))) :=
    DescentRawCablePanel.anchored N pick lay P _ t
  rw [anchored]
  have thickPick : (picked A he c e true).val = pick (⟨c,e⟩,0) := picked_old A he c e true
  have thinPick : (picked A he c e false).val = pick (⟨c,e⟩,1) := picked_old A he c e false
  unfold bornRoot
  generalize val : cluster lay t=j
  fin_cases j
  · change walked next (addr c).1 (look (here (addr c).1) (peers (addr c).1) (0,(row 9).val)) (key (venue (.inl ((N).src (pick (⟨c,e⟩,0))))))
    rw [root]
    rw [←thickPick]
    exact src
  · change walked next (addr c).1 (look (here (addr c).1) (peers (addr c).1) ((row 10).val/(2^k)+1,(row 10).val%(2^k))) (key (venue (.inl ((N).dst (pick (⟨c,e⟩,0))))))
    rw [show (row 10).val=_ from targetField true,destination_unpack (v true) (x true)]
    rw [←thickPick]
    exact dst true
  · change walked next (addr c).1 (look (here (addr c).1) (peers (addr c).1) ((row 7).val/(2^k)+1,(row 7).val%(2^k))) (key (venue (.inl ((N).dst (pick (⟨c,e⟩,1))))))
    rw [show (row 7).val=_ from targetField false,destination_unpack (v false) (x false)]
    rw [←thinPick]
    exact dst false

set_option maxHeartbeats 400000 in
include rank coord named fit winner sorted route df edgeOrder in
theorem issued_heads (u : (N).Site) (slot : Fin (2*A.cap)) :
    let c:=home u
    let old:=program (A.pos u) (A.block u) slot
    let mark:=(A.block u).val*(2*A.cap)+slot.val
    (old.born=none ↔ ¬∃e : Matched T A.cap (thinList home color c) (thickList home color c),
      rawTriple A native S ready names he c true (picked A he c e true) 0=mark) ∧
    ∀birth,old.born=some birth→∃e : Matched T A.cap (thinList home color c) (thickList home color c),
      rawTriple A native S ready names he c true (picked A he c e true) 0=mark ∧
      ∀t,walked next (A.pos u) (birth t) (key (venue (.inr (⟨c,e⟩,t)))) := by
  dsimp only
  let c:=home u
  let f:=fun _ : Fin (s).pairs=>(0:Cell (s).digit)
  let input:=panel (addr c).1
  let bx:=A.block u
  let number:=bx.val*(2*A.cap)+slot.val
  let code:=word (s).digit number
  let x:=inputs s A.cap (heap (addr c).2) input f
  let data:=decodeOutput s (lookupCell s (encodeInput x))
  have fitN : number<2^(s).digit := by
    have h : number<(bx.val+1)*(2*A.cap) := by dsimp [number];rw [Nat.add_mul,Nat.one_mul];omega
    have room:=(Nat.mul_le_mul_right (2*A.cap) bx.isLt)
    have tariff:=(shape_width (2^k) A.degree (2*A.cap) profile).2.2.1
    exact ((h.trans_le room).trans_le (Nat.le_add_left _ _)).trans tariff
  have unit : code.val=number:=Nat.mod_eq_of_lt fitN
  have side := source_host A he u
  have leafAt:=winner_leaf A native S ready names win next he fit winner u
  dsimp only [actorHeads]
  rw [leafAt,←side]
  change ((reverse data true code).map _=none ↔ _) ∧ ∀birth,(reverse data true code).map _=some birth→_
  constructor
  · rw [Option.map_eq_none_iff,reverse_absent A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c f true code,unit]
  · intro rows hit
    obtain ⟨j,found,encoded⟩:=Option.map_eq_some_iff.mp hit
    obtain ⟨e,_,used,fields,_⟩:=reverse_typed A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c f true code j found
    exact ⟨e,used.trans unit,fun t=>by rw [←encoded];exact born_walk A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c same lay e (data.row j) fields t⟩

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
