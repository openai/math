import OAI.Hierarchy.DescentPackedMatchIssuedRow
import OAI.Hierarchy.DescentPackedVenueHead

namespace OAI
/-! # The original typed pair at a physically issued redirect head -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup DescentOldOccurrenceRAM PackedLocalMatch
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 1600000
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
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank) (route : Routes A native S ready names next) (df : A.degree<2^short)
    (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f) (profile : ℕ) (c : ScanColonies he A.stage)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "pk" => slabPacking T A.cap (thinList home color c) (thickList home color c)
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)

variable (pf : Fin (shape (2^k) A.degree (2*A.cap) profile).pairs → Cell (shape (2^k) A.degree (2*A.cap) profile).digit)
local notation "X" => inputs s A.cap (heap (Prod.snd (addr c))) (panel (Prod.fst (addr c))) pf
local notation "table" => decodeOutput s (lookupCell s (encodeInput X))
include rank coord named fit winner sorted route df

omit sorted in
theorem native_offset (q : Fin (pk).decisions.length) :
    ∃t : Fin (s).packs,t.val=q.val ∧ ProtocolRAMPortRanks.«prefix» (PackedMatch.need X) Fin.val t=
        PairRAM.rawOffset N W.core home color A.cap c q ∧
      PackedMatch.need X t=DescentPacking.amount (live T) ((pk).decisions.get q).1 := by
  let xs:=thinPacks (live T) A.cap (thinList home color c)
  obtain ⟨space,counts⟩:=measured_inputs (short:=short) A native S ready names win next he rank coord named fit winner route df profile c pf
  have lengthEq : (pk).decisions.length=xs.length := by simpa using congrArg List.length (pk).order
  have bound := lengthEq.le.trans space
  have row (i : Fin (pk).decisions.length) :
      PackedMatch.need X (i.castLE bound)=DescentPacking.amount (live T) ((pk).decisions.get i).1 := by
    rw [counts]
    have hi : i.val<xs.length := i.isLt.trans_eq lengthEq
    have stored : xs[i.val]=((pk).decisions.get i).1 := by
      have old:=congrArg (fun l=>l[i.val]?) (pk).order
      change ((pk).decisions.map Prod.fst)[i.val]? = xs[i.val]? at old
      simpa only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem hi,Option.map_some,
        Option.some.injEq,List.get_eq_getElem] using old.symm
    change (xs[i.val]?.map (DescentPacking.amount (live T))).getD 0 = _
    simpa only [List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some] using congrArg (DescentPacking.amount (live T)) stored
  refine ⟨q.castLE bound,rfl,?_,row q⟩
  unfold PairRAM.rawOffset ProtocolRAMPortRanks.«prefix»
  simp only [Finset.sum_filter,Fin.val_castLE]
  exact prefix_sum (q.isLt.trans_le bound).le q.isLt.le _ _ (fun i=>row ⟨i.val,i.isLt.trans q.isLt⟩)

include edgeOrder in
theorem typed_row (e : Pair) :
    ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (pk).decisions e).val ∧
      ((table).row j 0).val=1 ∧ ((table).row j 3).val=oldOffset A he c e false ∧
      ∀l : Bool,centerAt l table j=word (s).digit (rawTriple A native S ready names he c true (picked A he c e true) (if l then 2 else 1)) := by
  obtain ⟨j,jval,b,_,issued⟩ := issued_row (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c e pf
  have small := lt_trans ((picked_wire (short:=short) A native S ready names win next he c rank coord named fit winner sorted route df edgeOrder e false).1.trans_le
    (stream_size (panel (addr c).1) (heap (addr c).2) false)) (shape_width (2^k) A.degree (2*A.cap) profile).1
  have one : 1<2^(s).digit := by
    have h := (shape_width (2^k) A.degree (2*A.cap) profile).2.2.1
    have hh : 1≤(A.degree+1)*2^k := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
    exact (hh.trans (Nat.le_add_right _ _)).trans_lt h
  refine ⟨j,jval,?_,?_,?_⟩
  · rw [issued];exact short_val one
  · rw [issued];exact short_val small
  · intro l
    rw [centerAt,issued]
    cases l <;> rfl

include edgeOrder in
theorem typed_redirect (t : Fin (s).packs) (e : Pair) :
    ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (pk).decisions e).val ∧
     (redirects X table t j=true ↔ e.2.1.val.val=t.val) ∧
     ∀l : Bool,centerAt l table j=word (s).digit (rawTriple A native S ready names he c true (picked A he c e true) (if l then 2 else 1)) := by
  obtain ⟨j,number,one,thin,thick⟩:=typed_row (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf e
  obtain ⟨v,ve,lo,len⟩:=native_offset (short:=short) A native S ready names win next he rank coord named fit winner route df profile c pf e.2.1.val
  have here : interval (PackedMatch.need X) v (oldOffset A he c e false) := by
    change _≤PairRAM.rawOffset N W.core home color A.cap c e.2.1.val+e.2.2.val ∧
        PairRAM.rawOffset N W.core home color A.cap c e.2.1.val+e.2.2.val<_
    rw [lo,len]
    exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left e.2.2.isLt _⟩
  refine ⟨j,number,?_,thick⟩
  simp only [redirects,decide_eq_true_eq,one,thin,eq_self,true_and]
  constructor
  · intro hit
    exact ve.symm.trans (congrArg Fin.val (interval_unique _ here.1 here.2 hit.1 hit.2))
  · intro eqn
    have same : v=t:=Fin.ext (ve.trans eqn)
    exact same ▸ here

include edgeOrder in
theorem head_issued (t : Fin (s).packs) (j : Fin (s).pairs) (hit : headRow X table t=some j) :
    ∃e : Pair,e.2.1.val.val=t.val ∧ j.val=(pairNumber (DescentPacking.amount (live T)) (pk).decisions e).val ∧
      ∀l : Bool,centerAt l table j=word (s).digit (rawTriple A native S ready names he c true (picked A he c e true) (if l then 2 else 1)) := by
  have active := List.find?_some hit
  change redirects X table t j=true at active
  have bound:=shape_bounded profile A.cap (heap (addr c).2) (panel (addr c).1) pf
  have room : j.val<PackedMatch.amount X := by
    by_contra! late
    simp only [redirects,empty_row X bound j late,Fin.val_zero,Nat.zero_ne_one,false_and,decide_false] at active
    cases active
  rw [live_amount (short:=short) A native S ready names win next he rank coord named fit winner sorted route df profile c pf] at room
  let sequence:=pairNumber (DescentPacking.amount (live T)) (pk).decisions
  let e:=sequence.symm ⟨j.val,room⟩
  have number : (sequence e).val=j.val := congrArg Fin.val (sequence.apply_symm_apply _)
  obtain ⟨v,which,owner,thick⟩:=typed_redirect (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf t e
  have eqn : v=j := Fin.ext (which.trans number)
  subst v
  exact ⟨e,owner.mp active,number.symm,thick⟩

include edgeOrder in
theorem head_miss (t : Fin (s).packs) :
    headRow X table t=none ↔ ¬∃e : Pair,e.2.1.val.val=t.val := by
  constructor
  · rintro miss ⟨e,held⟩
    obtain ⟨j,_,test,_⟩:=typed_redirect (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf t e
    exact List.find?_eq_none.mp miss j (List.mem_finRange j) (test.mpr held)
  · intro absent
    cases found : headRow X table t with
    | none=>rfl
    | some j=>
      obtain ⟨e,held,_⟩:=head_issued (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf t j found
      exact (absent ⟨e,held⟩).elim

include edgeOrder in
/-- The reverse lookup scans physical first-grain handles in a single source.
A missing match means that no original pair used this cable on that side. -/
theorem typed_handle (e : Pair) (side : Bool) :
    ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (pk).decisions e).val ∧
      ((table).row j 0).val=1 ∧ (table).row j (handleField side)=
        word (s).digit (rawTriple A native S ready names he c side (picked A he c e side) 0) ∧
      (∀b : Bool,∀f : Fin 3,((table).row j ⟨(if b then 8 else 5)+f.val,by have hf := f.isLt; split <;> omega⟩).val=
        rawTriple A native S ready names he c b (picked A he c e b) f) ∧ (table).row j 11=pf j := by
  obtain ⟨j,jval,b,_,issued⟩:=issued_row (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c e pf
  obtain ⟨w,wn,one,_,_⟩:=typed_row (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf e
  have same : w=j:=Fin.ext (wn.trans jval.symm)
  subst w
  refine ⟨j,jval,one,?_,?_,?_⟩
  · rw [issued];cases side <;> rfl
  · intro b' f
    rw [issued]
    have eqn:=raw_val A native S ready names he profile c b' (picked A he c e b') f
    cases b' <;> fin_cases f <;> exact eqn
  · rw [issued];rfl

include edgeOrder in
theorem reverse_typed (side : Bool) (code : Cell (s).digit) (j : Fin (s).pairs) (hit : reverse table side code=some j) :
    ∃e : Pair,j.val=(pairNumber (DescentPacking.amount (live T)) (pk).decisions e).val ∧
      rawTriple A native S ready names he c side (picked A he c e side) 0=code.val ∧
      (∀b : Bool,∀f : Fin 3,((table).row j ⟨(if b then 8 else 5)+f.val,by have hf := f.isLt; split <;> omega⟩).val=
        rawTriple A native S ready names he c b (picked A he c e b) f) ∧ (table).row j 11=pf j := by
  have chk : acceptedAt table side code j = true := List.find?_some hit
  have active : ((table).row j 0).val=1 ∧ (table).row j (handleField side)=code := of_decide_eq_true chk
  have bound:=shape_bounded profile A.cap (heap (addr c).2) (panel (addr c).1) pf
  have room : j.val<PackedMatch.amount X := by
    by_contra! late
    have alive:=active.1
    simp only [empty_row X bound j late,Fin.val_zero,Nat.zero_ne_one] at alive
  rw [live_amount (short:=short) A native S ready names win next he rank coord named fit winner sorted route df profile c pf] at room
  let sequence:=pairNumber (DescentPacking.amount (live T)) (pk).decisions
  let e:=sequence.symm ⟨j.val,room⟩
  have number : (sequence e).val=j.val :=
    congrArg (fun i : Fin (countIn he A c) => i.val) (sequence.apply_symm_apply ⟨j.val,room⟩)
  obtain ⟨w,wn,_,handle,fields,profileEq⟩:=typed_handle (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf e side
  have eqn : w=j:=Fin.ext (wn.trans number)
  subst w
  have hd:=congrArg Fin.val (handle.symm.trans active.2)
  rw [raw_val A native S ready names he profile c side (picked A he c e side) 0] at hd
  exact ⟨e,number.symm,hd,fields,profileEq⟩

include edgeOrder in
theorem reverse_absent (side : Bool) (code : Cell (s).digit) :
    reverse table side code=none ↔ ¬∃e : Pair,rawTriple A native S ready names he c side (picked A he c e side) 0=code.val := by
  constructor
  · rintro miss ⟨e,held⟩
    obtain ⟨j,_,one,handle,_,_⟩:=typed_handle (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf e side
    have value : (table).row j (handleField side)=code := by
      rw [handle]
      exact Fin.ext ((raw_val A native S ready names he profile c side (picked A he c e side) 0).trans held)
    exact List.find?_eq_none.mp miss j (List.mem_finRange j) (decide_eq_true (And.intro one value))
  · intro none
    cases hit : reverse table side code with
    | none=>rfl
    | some j=>
      obtain ⟨e,_,eqn,_⟩:=reverse_typed (short:=short) A native S ready names win next he rank coord named fit winner sorted route df edgeOrder profile c pf side code j hit
      exact (none ⟨e,eqn⟩).elim

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
