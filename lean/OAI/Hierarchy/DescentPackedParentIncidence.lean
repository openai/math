import OAI.Hierarchy.DescentPackedPhysicalWalk
import OAI.Hierarchy.DescentPackedActorPath
import OAI.Hierarchy.DescentOrdinaryDonorRows

namespace OAI
/-! # The two actual venue walks issued in each of the eleven raw parent lanes -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentCableDonorNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

namespace ParentIncidence
/-- Original, two demand arms, and eight supply roles share one old donor. -/
def issue (chosen : Bool) (left right : Walk) (born : Option (Fin 6→Walk)) : Fin 11→Option (Walk×Walk) :=
  fun i => Fin.cases (motive := fun _ => Option (Walk × Walk)) (if chosen then none else some (left,right))
    (fun j => Fin.addCases (motive := fun _ => Option (Walk × Walk)) (fun _ : Fin 2=>none)
      (fun s : Fin 8=>born.map (fun f=>(f (supplySrc s),f (supplyDst s)))) j) i

@[simp] theorem original (chosen : Bool) (l r : Walk) (b : Option (Fin 6→Walk)) :
    issue chosen l r b 0=(if chosen then none else some (l,r)) := rfl
@[simp] theorem arm (chosen : Bool) (l r : Walk) (b : Option (Fin 6→Walk)) (j : Fin 2) :
    issue chosen l r b (Fin.succ (Fin.castAdd 8 j))=none := by simp [issue]
@[simp] theorem supply (chosen : Bool) (l r : Walk) (b : Option (Fin 6→Walk)) (j : Fin 8) :
    issue chosen l r b (Fin.succ (Fin.natAdd 2 j))=b.map (fun f=>(f (supplySrc j),f (supplyDst j))) := by simp [issue]

structure Actual {Z : Type} {D : ℕ} (next : Z→Fin D→Option Z) (root : Z) (ports : Walk×Walk) (x y : DescentHostDirectory.Key Z) : Prop where
  src : walked next root ports.1 x
  dst : walked next root ports.2 y

theorem received {Z : Type} {D H : ℕ} {next : Z→Fin D→Option Z} {z} {p : Walk×Walk} {x y}
    (raw : Actual next z p x y) (name : Z→Fin H) (R : Fin H→Fin D→Option (Fin H))
    (real : ∀u i v,next u i=some v→R (name u) i=some (name v)) (symm : ∀v u i,R v i=some u→∃j,R u j=some v) :
    ∀side : Bool,let w:=if side then p.2 else p.1;let addr:=if side then y else x
      DescentHaloWalkRAM.walk R (name z) (DescentHaloWalkRAM.path (DescentHaloWalkRAM.ActorPath.index D w)) 4=some (name (addr).1) ∧
      (∃!j,DescentHaloWalkRAM.Gather.select (DescentHaloWalkRAM.Gather.reaching R) (name (addr).1) j=some (name z)) ∧ w.2.2=(heap (addr).2.1,(addr).2.2) := by
  intro side
  have walk_ : walked next z (if side then p.2 else p.1) (if side then y else x) := by cases side <;> first | exact raw.src | exact raw.dst
  exact ⟨DescentHaloWalkRAM.ActorPath.emitted next name R real _ _ _ walk_,DescentHaloWalkRAM.ActorPath.received_once next name R real symm _ _ _ walk_,walk_.2⟩
end ParentIncidence

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
local notation "names" => cableNames k rank
local notation "next" => rotor A rank
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
local notation "traffic" => nativeTraffic N W.core home
local notation "Positive" => DescentSharedCableNames.Stage.Positive A
local notation "out" => DescentSharedCableNames.Stage.outgoing A native S ready
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "pick" => colorPick N W.core home color A.cap
local notation "Packs" => coloredPack N W.core home color A.cap
local notation "venue" => newSite N pick lay Packs
local notation "key" => nativeKey N W.core home color A.cap addr same lay
local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "peers" => fun h v x=>(next h v).elim (0,0,0) (fun other=>here other x)
local notation "positiveOf" => fun e : Positive=>(A.block ((N).src e.val)).val*(2*A.cap)+(out e).val
local notation "zeroes" => fun _ : Fin (s).pairs=>(0:Cell (s).digit)

def headSlot (e : Positive) : Fin (2*A.cap) := (out e).castLE (Nat.le_mul_of_pos_left _ (by decide))

def parentHeads (e : Positive) :=
  let v:=(N).src e.val;let h:=A.pos v;let x:=A.block v
  actorHeads A.cap profile (panel h) lay (here h) (peers h) x (headSlot A native S ready e)

def parentHit (e : Positive) (side : Bool) :=
  let v:=(N).src e.val;let u:=panel (A.pos v);let f:=inputs s A.cap (leaf (u.winner (A.block v)).val) u zeroes
  reverse (decodeOutput s (lookupCell s (encodeInput f))) side (word (s).digit (positiveOf e))

include coord in
private theorem same_handle (e : Positive) {c : ScanColonies he A.stage} {side : Bool} (v : Active A he c side)
    (host : (addr c).1=A.pos ((N).src e.val)) :
    rawTriple A native S ready names he c side v 0=positiveOf e ↔ v.val=e.val := by
  let q:=event A he c side v
  let t : Positive:=⟨v.val,A.quantum_positive _ v.property.1⟩
  have tick:=source_wire A native S ready ((addr c).1,q.1) q.2
  change (address A native S ready ((addr c).1,q.1) q.2).val=(out t).val at tick
  change q.1.val*(2*A.cap)+(address A native S ready ((addr c).1,q.1) q.2).val=_ ↔ _
  rw [tick]
  have loc : A.pos ((N).src v.val)=(addr c).1:=by rw [←source_host A he ((N).src v.val),v.property.2.1]
  constructor
  · intro eqn
    have addressEq : finProdFinEquiv (q.1,headSlot A native S ready t)=finProdFinEquiv (A.block ((N).src e.val),headSlot A native S ready e) := by
      apply Fin.ext
      change (out t).val + (2*A.cap)*q.1.val = (out e).val + (2*A.cap)*(A.block ((N).src e.val)).val
      rw [Nat.mul_comm (2*A.cap) q.1.val, Nat.add_comm (out t).val,
        Nat.mul_comm (2*A.cap) (A.block ((N).src e.val)).val, Nat.add_comm (out e).val]
      exact eqn
    have parts:=finProdFinEquiv.injective addressEq
    have site : (N).src v.val=(N).src e.val:=coord (Prod.ext (loc.trans host) (congrArg Prod.fst parts))
    exact congrArg Subtype.val (DescentSharedCableNames.Stage.outgoing_identify A native S ready t e site (Fin.ext (congrArg (fun p=>p.2.val) parts)))
  · intro eqn
    have eq' : t=e:=Subtype.ext eqn
    change (A.block ((N).src v.val)).val*(2*A.cap)+(out t).val=_
    rw [eqn,eq']

include coord named fit winner df edgeOrder in
theorem parent_hit (e : Positive) (side : Bool) :
    parentHit (short:=short) A native S ready rank win profile e side=none ↔
      ¬∃p : NativePair N W.core home color A.cap,pick (p,if side then 0 else 1)=e.val := by
  let v:=(N).src e.val;let c:=home v;let num:=positiveOf e;let token:=word (s).digit num
  have root : (addr c).1=A.pos v:=source_host A he v
  have limited : num<2^(s).digit := by
    have fit_ : num<((A.block v).val+1)*(2*A.cap) := by
      rw [Nat.add_mul,Nat.one_mul]
      exact Nat.add_lt_add_left (headSlot A native S ready e).isLt _
    exact ((fit_.trans_le (Nat.mul_le_mul_right _ (A.block v).isLt)).trans_le (Nat.le_add_left _ _)).trans (shape_width (2^k) A.degree (2*A.cap) profile).2.2.1
  have cut:=winner_leaf A native S ready names win next he fit winner v
  dsimp only [parentHit];rw [cut,←root]
  rw [reverse_absent A native S ready names win next he rank coord named fit winner (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile c zeroes side token]
  apply not_congr
  constructor
  · rintro ⟨p,held⟩
    have at_ : (picked A he c p side).val=e.val:=(same_handle A native S ready rank he coord e _ root).1 (held.trans (Nat.mod_eq_of_lt limited))
    exact ⟨⟨c,p⟩,(picked_old A he c p side).symm.trans at_⟩
  · rintro ⟨⟨z,p⟩,held⟩
    have id : (picked A he z p side).val=e.val:=(picked_old A he z p side).trans held
    have source := (picked A he z p side).property.2.1
    rw [id] at source
    change c=z at source;subst z
    exact ⟨p,((same_handle A native S ready rank he coord e _ root).2 id).trans (Nat.mod_eq_of_lt limited).symm⟩

def parentChosen (e : Positive) :=
  (parentHit (short:=short) A native S ready rank win profile e true).isSome || (parentHit (short:=short) A native S ready rank win profile e false).isSome

include coord named fit winner df edgeOrder in
theorem parent_chosen (e : Positive) : parentChosen (short:=short) A native S ready rank win profile e=(GadgetNetwork.selected N pick e.val).isSome := by
  let test:=parentHit (short:=short) A native S ready rank win profile e
  have hit (side : Bool) :=parent_hit A native S ready rank win he coord named fit winner df edgeOrder profile e side
  by_cases used : ∃p : NativePair N W.core home color A.cap,∃j : Fin 2,pick (p,j)=e.val
  · obtain ⟨p,j,q⟩:=used
    have full : (GadgetNetwork.selected N pick e.val).isSome=true:=by rw [←q,GadgetNetwork.selected_pick];rfl
    rw [full];unfold parentChosen
    fin_cases j
    · have yes : test true≠none:=fun miss=>(hit true).mp miss ⟨p,q⟩
      change ((test true).isSome || (test false).isSome) = true
      exact Bool.or_eq_true_iff.mpr (.inl (Option.isSome_iff_ne_none.mpr yes))
    · have yes : test false≠none:=fun miss=>(hit false).mp miss ⟨p,q⟩
      change ((test true).isSome || (test false).isSome) = true
      exact Bool.or_eq_true_iff.mpr (.inr (Option.isSome_iff_ne_none.mpr yes))
  · have no (side : Bool) : test side=none:=(hit side).2 (fun ⟨p,h⟩=>used ⟨p,_,h⟩)
    have none_ : GadgetNetwork.selected N pick e.val=none := by
      cases h : GadgetNetwork.selected N pick e.val with
      | none=>rfl
      | some z=>exact False.elim (used ⟨z.1,z.2,GadgetNetwork.selected_spec N pick h⟩)
    change ((test true).isSome || (test false).isSome)=_
    rw [no,no,none_];rfl

local notation "heads" => parentHeads (short:=short) A native S ready rank win profile lay
local notation "MatchedI" => NativePair N W.core home color A.cap

include coord named fit winner df edgeOrder in
theorem parent_born (e : Positive) (p : MatchedI) (at_ : pick (p,0)=e.val) :
    ∃f,(heads e).born=some f ∧ ∀j,walked next (A.pos ((N).src e.val)) (f j) (key (venue (.inr (p,j)))) := by
  let v:=(N).src e.val;let c:=home v
  have root : (addr c).1=A.pos v:=source_host A he v
  have src := issued_heads A native S ready names win next he rank coord named fit winner (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay v (headSlot A native S ready e)
  rcases p with ⟨z,p⟩
  have targetId : (picked A he z p true).val=e.val:=(picked_old A he z p true).trans at_
  have srcName:=(picked A he z p true).property.2.1
  rw [targetId] at srcName;change c=z at srcName;subst z
  have exists_:=((same_handle A native S ready rank he coord e _ root).2 targetId)
  cases fAt : (heads e).born with
  | none=>exact False.elim ((src.1.mp fAt) ⟨p,exists_⟩)
  | some f=>
    obtain ⟨chosen,mark,trace⟩:=src.2 f fAt
    have cable : (picked A he c chosen true).val=e.val:=(same_handle A native S ready rank he coord e _ root).1 mark
    have id : (⟨c,chosen⟩ : MatchedI)=⟨c,p⟩:=congrArg Prod.fst ((pick).injective (((picked_old A he c chosen true).symm.trans cable).trans at_.symm))
    exact ⟨f,rfl,fun j=>id ▸ trace j⟩

include coord named fit winner df edgeOrder same in
theorem parent_no_born (e : Positive) (miss : ¬∃p : MatchedI,pick (p,0)=e.val) : (heads e).born=none := by
  let v:=(N).src e.val;let c:=home v
  have src:=issued_heads A native S ready names win next he rank coord named fit winner (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay v (headSlot A native S ready e)
  apply src.1.mpr
  rintro ⟨p,held⟩
  have old:=(same_handle A native S ready rank he coord e _ (source_host A he v)).1 held
  exact miss ⟨⟨c,p⟩,(picked_old A he c p true).symm.trans old⟩

/-- The ordinary receiver uses the old first-grain slot as its fixed root,
and the true cable's signed peer field for the old remote endpoint. -/
def parentRows (e : Positive) : Fin 11→Option (Walk×Walk) :=
  let v:=(N).src e.val;let h:=A.pos v;let x:=A.block v
  let dest:=look (here h) (peers h) ((sourceHandle A native S ready rank e).neighbor.val+1,x.val)
  ParentIncidence.issue (parentChosen (short:=short) A native S ready rank win profile e) (heads e).old dest (heads e).born

local notation "rows" => parentRows (short:=short) A native S ready rank win profile lay

include coord named fit winner df edgeOrder in
theorem parent_actual (edge : DescentRawCablePanel.Live A pick) :
    let donor : Positive:=⟨anchor pick edge.val,edge.property⟩
    let parent:=rows donor (role edge.val)
    let x:=venue (GadgetNetwork.source N edge.val);let y:=venue (GadgetNetwork.target N pick edge.val)
    (parent=none→x=y) ∧ ∀p,parent=some p→ParentIncidence.Actual next (A.pos ((N).src donor.val)) p (key x) (key y) := by
  obtain ⟨e,pos⟩:=edge
  rcases e with e|⟨p,j⟩|⟨p,j⟩
  · let z : Positive:=⟨e,pos⟩
    let h:=A.pos ((N).src e)
    let x:=A.block ((N).src e)
    let w:=look (here h) (peers h) ((sourceHandle A native S ready rank z).neighbor.val+1,x.val)
    have chosen:=parent_chosen A native S ready rank win he coord named fit winner df edgeOrder profile z
    have row : rows z 0 = (if parentChosen (short:=short) A native S ready rank win profile z
      then none else some ((heads z).old,w)) := rfl
    cases selected : GadgetNetwork.selected N pick e with
    | none =>
      have no := chosen.trans (congrArg Option.isSome selected)
      change parentChosen (short:=short) A native S ready rank win profile z=false at no
      rw [no] at row
      change rows z 0=some ((heads z).old,w) at row
      constructor
      · intro held
        exact False.elim (Option.some_ne_none _ (row.symm.trans held))
      · intro ports issued
        have eqn := Option.some.inj (row.symm.trans issued)
        subst ports
        have src:=prior_head A native S ready names win next he rank coord named fit winner
          (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay
          ((N).src e) (headSlot A native S ready z)
        have dst:=physical_walk A native S ready rank win he coord named fit winner df edgeOrder profile same lay z true
        refine ⟨src,?_⟩
        have endpoint : GadgetNetwork.target N pick (.inl e)=.inl ((N).dst e) := by
          simp only [GadgetNetwork.target,selected]
        change walked next h w (key (venue (GadgetNetwork.target N pick (.inl e))))
        rw [endpoint]
        exact dst
    | some i =>
      have yes := chosen.trans (congrArg Option.isSome selected)
      change parentChosen (short:=short) A native S ready rank win profile z=true at yes
      rw [yes] at row
      change rows z 0=none at row
      constructor
      · intro _
        let collapsed (v : (N).Edge) :=
          venue (GadgetNetwork.source N (.inl v))=venue (GadgetNetwork.target N pick (.inl v))
        have old : collapsed (pick i) := DescentRawCablePanel.picked_old N pick lay Packs i.1 i.2
        exact (congrArg collapsed (GadgetNetwork.selected_spec N pick selected)).mp old
      · intro ports held
        exact False.elim (Option.some_ne_none _ (held.symm.trans row))
  · let z : Positive:=⟨pick (p,0),pos⟩
    let idx := role (.inr (.inl (p,j)) : Raw (N).Edge MatchedI)
    have index_eq : idx=Fin.succ (Fin.castAdd 8 j) := Fin.ext (by simp [idx,role];omega)
    have row : rows z idx=none := by
      rw [index_eq]
      exact ParentIncidence.arm _ _ _ _ _
    constructor
    · exact fun _=>DescentRawCablePanel.picked_arm N pick lay Packs p j
    · intro ports issued
      exact False.elim (Option.some_ne_none _ (issued.symm.trans row))
  · let z : Positive:=⟨pick (p,0),pos⟩
    obtain ⟨f,hf,live⟩:=parent_born A native S ready rank win he coord named fit winner df edgeOrder profile same lay z p rfl
    let idx := role (.inr (.inr (p,j)) : Raw (N).Edge MatchedI)
    have index_eq : idx=Fin.succ (Fin.natAdd 2 j) := Fin.ext (by simp [idx,role];omega)
    have row : rows z idx=some (f (supplySrc j),f (supplyDst j)) := by
      rw [index_eq]
      change ParentIncidence.issue _ _ _ (heads z).born _=_
      rw [ParentIncidence.supply,hf]
      rfl
    constructor
    · intro held
      exact False.elim (Option.some_ne_none _ (row.symm.trans held))
    · intro ports issued
      have eqn := Option.some.inj (row.symm.trans issued)
      subst ports
      exact ⟨live (supplySrc j),live (supplyDst j)⟩

include coord named fit winner df edgeOrder same in
/-- Every nonempty role in the physical donor window names a unique true
raw parent. A padding role cannot generate either an endpoint or a peer. -/
theorem parent_image (e : Positive) (j : Fin 11) (ports : Walk×Walk) (hit : rows e j=some ports) :
    ∃!q : DescentRawCablePanel.Live A pick,anchor pick q.val=e.val ∧ role q.val=j := by
  let RawE:=DescentRawCablePanel.Live A pick
  have unique (q q' : RawE) (a : anchor pick q.val=e.val ∧ role q.val=j)
      (b : anchor pick q'.val=e.val ∧ role q'.val=j) : q'=q :=
    Subtype.ext (identify pick (b.1.trans a.1.symm) (b.2.trans a.2.symm))
  suffices ex : ∃q : RawE,anchor pick q.val=e.val ∧ role q.val=j by
    obtain ⟨q,hq⟩:=ex;exact ⟨q,hq,fun q' hq'=>unique q q' hq hq'⟩
  revert hit
  refine Fin.cases (motive := fun j => rows e j = some ports → ∃ q : RawE, anchor pick q.val = e.val ∧ role q.val = j) (fun _=>⟨⟨.inl e.val,e.property⟩,rfl,rfl⟩) (fun t=>?_) j
  refine Fin.addCases (motive := fun r => rows e r.succ = some ports → ∃ q : RawE, anchor pick q.val = e.val ∧ role q.val = r.succ) (fun a : Fin 2 => ?_) (fun b : Fin 8 => ?_) t
  all_goals intro hit
  · simp [parentRows,ParentIncidence.arm] at hit
  · by_cases used : ∃p : MatchedI,pick (p,0)=e.val
    · obtain ⟨p,hp⟩:=used
      refine ⟨⟨.inr (.inr (p,b)),by
        change 0 < A.grainCount (pick (p,0))
        rw [hp]
        exact e.property⟩,hp,Fin.ext (by simp [role];omega)⟩
    · have off := parent_no_born A native S ready rank win he coord named fit winner df edgeOrder profile same lay e used
      simp [parentRows,ParentIncidence.supply,off] at hit

/-- Numeric address in the same padded chart that receives the old signed
cables, for each surviving actual parent and conversely for each nonempty lane. -/
theorem parent_address {H R : ℕ} (hosts : V↪Fin H) (groups : J≃Fin R) (q : DescentRawCablePanel.Live A pick) :
    let e : Positive:=⟨anchor pick q.val,q.property⟩
    let root:=DescentRawCablePanel.oldSlot A S ready native hosts groups e
    DescentRawCablePanel.slot A S ready native hosts groups pick q=(root.1,finProdFinEquiv (root.2,role q.val)) :=
  DescentRawCablePanel.split_slot A S ready native hosts groups pick q

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
