import OAI.Hierarchy.DescentPackedMatchOrdinary
import OAI.Hierarchy.DescentPackedMatchIssuedRow

namespace OAI
/-! # Bounded searches over actual old donor handles in the packed result -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000

/-- One of the twelve short cells in a selected source lane's row. -/
def donorWord {w n M : ℕ} (s : Shape) (m : Memory w) (top : ℕ)
    (seat : Fin n×Fin M) (j : Fin s.pairs) (f : Fin 12) :=
  digit s.digit (1+(finProdFinEquiv (j,f)).val)
    (digit s.outputBits seat.2.val (m (top+seat.1.val)).val)

private theorem get_digit {H G M w : ℕ} (s : Shape) (x : Fin H→Fin G→Inputs s) (hm : 0<M)
    (b : ℕ) (m : Memory w) (sumSize : s.outputBits*M≤w)
    (stored : ∀i,m (b+i.val)=((topologyWords (M:=M) s x i).val:Word w))
    (h : Fin H) (g : Fin G) (j : Fin s.pairs) (f : Fin 12) :
    donorWord s m b (row H G M (position h g hm),lane g hm) j f=((transform (x h g)).row j f).val := by
  let p:=position h g hm
  let a:=lane g hm
  have coord : p.2.val*M+a.val=g.val := Nat.div_add_mod' ..
  have sel : (⟨p.2.val*M+a.val,coord.trans_lt g.isLt⟩:Fin G)=g:=Fin.ext coord
  let k:=topologyWords s x (row H G M p)
  have enough : k.val<2^w := k.isLt.trans_le (Nat.pow_le_pow_right (by decide) sumSize)
  have read:=active_read (lookupCell s) (fun h g=>encodeInput (x h g)) p a (coord.trans_lt g.isLt)
  rw [topology_key,sel] at read
  change digit s.digit _ (digit s.outputBits a.val (m (b+(row H G M p).val)).val)=_
  rw [stored,Fin.val_cast_of_lt enough,read]
  rw [show p.1=h from rfl]
  simpa only [lookupCell,decode_encode] using row_digit (transform (x h g)) j f

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

include sumSize stored in
theorem observed_field (j : Fin (s).pairs) (f : Fin 12) :
    donorWord s m b (seat c) j f=((transform x).row j f).val := by
  rw [slot_eq]
  have rd:=get_digit s fieldsAt hm b m sumSize stored (sourceIndex he A groups hosts c).1 (sourceIndex he A groups hosts c).2 j f
  have cell : fieldsAt (sourceIndex he A groups hosts c).1 (sourceIndex he A groups hosts c).2 = x := by
    rw [sourceIndex_eq]
    simp only [Gather.flat,Equiv.symm_apply_apply,Gather.descriptorInputs]
    exact congrArg (fun v => inputs s A.cap (heap (addr c).2) v (fun _ => 0))
      (spread_hit groups hosts panel (addr c).1)
  exact rd.trans (congrArg (fun input : Inputs s => ((transform input).row j f).val) cell)

include coord named fit winner df edgeOrder sumSize stored in
theorem donor_record (e : Pair) :
    ∃j : Fin (s).pairs,j.val=(num e).val ∧ donorWord s m b (seat c) j 0=1 ∧
      donorWord s m b (seat c) j 8=rawTriple A native S ready names he c true (picked A he c e true) 0 ∧
      donorWord s m b (seat c) j 5=rawTriple A native S ready names he c false (picked A he c e false) 0 := by
  obtain ⟨j,at_,z,_,h⟩:=issued_row A native S ready names win peers he rank coord named fit winner
    (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile c e (fun _=>0)
  simp only [lookupCell,decode_encode,output_inverse] at h
  have field_ := observed_field A native S ready rank win he groups hosts hm profile b m sumSize stored c j
  have width:=shape_width r A.degree p profile
  have digit_ : 1<2^(s).digit := by
    have gr : 0<(2:ℕ)^k := Nat.two_pow_pos _
    have big := width.2.2.1
    have bins : 1≤(A.degree+1)*r := Nat.mul_pos (Nat.zero_lt_succ _) gr
    exact (bins.trans (Nat.le_add_right _ _)).trans_lt big
  refine ⟨j,at_,?_,?_,?_⟩
  · rw [field_,h]
    exact short_val digit_
  · rw [field_,h]
    exact raw_val A native S ready names he profile c true (picked A he c e true) 0
  · rw [field_,h]
    exact raw_val A native S ready names he profile c false (picked A he c e false) 0

include coord named fit winner df edgeOrder sumSize stored in
theorem valid_iff (j : Fin (s).pairs) :
    donorWord s m b (seat c) j 0=1 ↔ ∃!e : Pair,(num e).val=j.val := by
  constructor
  · intro live
    have lt : j.val<countIn he A c := by
      by_contra! past
      have count:=live_amount A native S ready names win peers he rank coord named fit winner (rotor_sorted A rank)
        (rotor_routes A native S ready rank) df profile c (fun _=>0)
      have zero:=empty_row x (shape_bounded profile A.cap _ _ _) j (count.le.trans past)
      simp only [lookupCell,decode_encode,output_inverse] at zero
      rw [observed_field A native S ready rank win he groups hosts hm profile b m sumSize stored c,zero] at live
      exact Nat.zero_ne_one live
    let z : Fin (Fintype.card Pair):=⟨j.val,lt⟩
    refine ⟨(num).symm z,congrArg Fin.val ((num).apply_symm_apply z),?_⟩
    intro e eqn
    apply (num).injective
    rw [Equiv.apply_symm_apply]
    exact Fin.ext eqn
  · rintro ⟨e,at_,_⟩
    obtain ⟨j',n,h,_⟩:=donor_record A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder
      profile b m sumSize stored c e
    exact (Fin.ext (n.trans at_) : j'=j) ▸ h

private theorem events_eq {h h' : J×V} (same : h=h') (v : Events A h) (v' : Events A h')
    (addrEq : finProdFinEquiv (seats A native S ready h v)=finProdFinEquiv (seats A native S ready h' v')) :
    v.2.val=v'.2.val := by
  subst h'
  exact congrArg (fun z : Events A h=>z.2.val) ((seats A native S ready h).injective (finProdFinEquiv.injective addrEq))

theorem edge_handle (c' : C) (side shade : Bool) (v : Active A he c side) (v' : Active A he c' shade)
    (host : (addr c).1=(addr c').1)
    (key : rawTriple A native S ready names he c side v 0=rawTriple A native S ready names he c' shade v' 0) :
    v.val=v'.val := by
  let u:=event A he c side v
  let z:=event A he c' shade v'
  let a:=seats A native S ready (addr c).1 u
  let b:=seats A native S ready (addr c').1 z
  change a.1.val*(2*A.cap)+a.2.val=b.1.val*(2*A.cap)+b.2.val at key
  apply events_eq A native S ready host u z
  apply Fin.ext
  change a.2.val+(2*A.cap)*a.1.val=b.2.val+(2*A.cap)*b.1.val
  rw [Nat.mul_comm (2*A.cap) a.1.val,Nat.mul_comm (2*A.cap) b.1.val,Nat.add_comm a.2.val,Nat.add_comm b.2.val]
  exact key

theorem donor_unique (c' : C) (e : Pair)
    (f : Matched T A.cap (thinList home color c') (thickList home color c'))
    (host : (addr c).1=(addr c').1)
    (key : rawTriple A native S ready names he c true (picked A he c e true) 0=
      rawTriple A native S ready names he c' true (picked A he c' f true) 0) :
    (⟨c,e⟩ : NativePair W.graph W.core home color A.cap)=⟨c',f⟩ := by
  have same:=edge_handle A native S ready rank he c c' true true _ _ host key
  rw [picked_old,picked_old] at same
  exact congrArg Prod.fst ((colorPick W.graph W.core home color A.cap).injective same)

include coord named fit winner df edgeOrder sumSize stored in
theorem chosen_thick_iff (j : Fin (s).pairs) (v : Active A he c true) :
    (donorWord s m b (seat c) j 0=1 ∧ donorWord s m b (seat c) j 8=rawTriple A native S ready names he c true v 0) ↔
      ∃!e : Pair,(num e).val=j.val ∧ (picked A he c e true).val=v.val := by
  let active:=valid_iff A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder profile b m sumSize stored c j
  have record_ (e : Pair) (idEq : (num e).val=j.val) :
      donorWord s m b (seat c) j 0=1 ∧ donorWord s m b (seat c) j 8=rawTriple A native S ready names he c true (picked A he c e true) 0 := by
    obtain ⟨a,ha,alive,raw,_⟩:=donor_record A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder profile b m sumSize stored c e
    cases (Fin.ext (ha.trans idEq) : a=j)
    exact ⟨alive,raw⟩
  constructor
  · rintro ⟨ok,eqn⟩
    obtain ⟨e,numEq,unique⟩:=active.mp ok
    refine ⟨e,⟨numEq,edge_handle A native S ready rank he c c true true _ _ rfl ((record_ e numEq).2.symm.trans eqn)⟩,
      fun _ h=>unique _ h.1⟩
  · rintro ⟨e,⟨numEq,edgeEq⟩,_⟩
    have rd:=record_ e numEq
    rw [show picked A he c e true=v from Subtype.ext edgeEq] at rd
    exact rd

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
