import OAI.Hierarchy.DescentResetPublicParentRead
import OAI.Hierarchy.DescentResetCompactSourceTicket
import OAI.Hierarchy.DescentPrivateCandidateShelf
import OAI.Hierarchy.DescentResetOriginalPosted
import OAI.Hierarchy.DescentUniformSlotOperands

namespace OAI
/-! # Original chronology of the private wire at a rooted candidate -/
namespace Hierarchy.DescentResetPublicParentWord
open DescentResetLocalRoster DescentResetCompactParent DescentResetParentCodec DescentSIMDLookup
open scoped Classical
noncomputable section

/-- The private shelf already numbers the sign, immutable root ticket and private wire.
The only remaining inputs are its live bit, the coarse-zero flag and the receiver's self-rank. -/
def privateWord (s : Shape) (live baseAddr host slot : ℕ) : ℕ :=
  if live=0 then 0 else if good : host<s.halo then
    if old : ∃p : Bool×Root s.depth s.ports×Fin s.program,
        (localPrivateId s.depth s.ports s.program p).val=slot then
      let p:=old.choose
      number (decide (baseAddr≠0)) (show Parent s from .inr (.inr (.inr
        (finTwoEquiv.symm p.1,attach s ⟨host,good⟩ p.2.1,p.2.2))))
    else 0
  else 0

theorem private_dead (s : Shape) (z h j : ℕ) : privateWord s 0 z h j=0 := by simp [privateWord]

theorem private_read (s : Shape) (z : Bool) (h : Fin s.halo)
    (p : Bool×Root s.depth s.ports×Fin s.program) :
    privateWord s 1 z.toNat h.val (localPrivateId _ _ _ p).val=
      number z (show Parent s from .inr (.inr (.inr (finTwoEquiv.symm p.1,attach s h p.2.1,p.2.2)))) := by
  have has : ∃q : Bool×Root s.depth s.ports×Fin s.program,
      (localPrivateId _ _ _ q).val=(localPrivateId _ _ _ p).val := ⟨p,rfl⟩
  have eqn : has.choose=p := (localPrivateId _ _ _).injective (Fin.ext has.choose_spec)
  cases z <;> simp [privateWord,h.isLt,has,eqn]

end
end Hierarchy.DescentResetPublicParentWord

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentCompiler DescentColonies DescentResetLocalRoster DescentResetCompactParent DescentResetParentCodec
open DescentResetPublicParentWord DescentSIMDLookup DescentResetFieldAssembler DescentResetMixedWordRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "shape" => publicShape B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

def privateOrdinal (p : PrivateOccurrence B) : Fin (privateCount B) :=localPrivateId _ _ _ (privateTicket B p)

theorem private_word (u : Host) (p : PrivateOccurrence B)
    (selected : receiverRoot B u=(B.reset.rootVertex B.terminals p.1.2,B.reset.rootBlock B.terminals p.1.2)) :
    privateWord shape 1 (zeroCoarse B u).toNat (haloNumber B u (receiverRoot B u).1)
      (privateOrdinal B p).val=wordNumber B u (privateWire B p) := by
  have self := congrArg Prod.fst selected
  change (receiverRoot B u).1=B.reset.rootVertex B.terminals p.1.2 at self
  rw [self]
  change privateWord shape 1 (zeroCoarse B u).toNat
    (haloDigit B u (B.reset.rootVertex B.terminals p.1.2)).val
    (localPrivateId _ _ _ (privateTicket B p)).val=_
  apply (private_read shape (zeroCoarse B u) (haloDigit B u (B.reset.rootVertex B.terminals p.1.2)) (privateTicket B p)).trans
  have root := site_from_ticket B u p.1.2
  change attach shape _ (privateTicket B p).2.1=siteWord B u p.1.2 at root
  rw [root]
  change _=number (zeroCoarse B u) (namedWord B u (motherNames B (privateWire B p)))
  rw [←private_parent B p,Equiv.apply_symm_apply]
  rfl

/-- This is the value installed at the exact private shelf index, at both
positive wires and dormant candidates. -/
theorem private_origin_word (u : Host) (p : PrivateOccurrence B)
    (selected : receiverRoot B u=(B.reset.rootVertex B.terminals p.1.2,B.reset.rootBlock B.terminals p.1.2)) :
    let found:=localOrigin B u (privateShelfIndex B (privateOrdinal B p))
    privateWord shape found.isSome.toNat (zeroCoarse B u).toNat
      (haloNumber B u (receiverRoot B u).1) (privateOrdinal B p).val=
        found.elim 0 (fun e=>wordNumber B u e.val) := by
  intro found
  have eqn:=private_selected_origin B u p selected
  change found=_ at eqn
  by_cases live : active (blocks B) u (privateWire B p)
  · rw [dite_eq_left live] at eqn
    simpa only [eqn,Option.isSome_some,Bool.toNat_true,Option.elim_some] using private_word B u p selected
  · rw [dite_eq_right live] at eqn
    simp [eqn,private_dead]

/-- The physical private slot number suffices at every receiver, including gaps in
the immutable root-ticket enumeration. -/
theorem private_slot_word (u : Host) (j : Fin (privateCount B)) :
    let x:=localOrigin B u (privateShelfIndex B j)
    privateWord shape x.isSome.toNat (zeroCoarse B u).toNat
      (haloNumber B u (receiverRoot B u).1) j.val=x.elim 0 (fun e=>wordNumber B u e.val) := by
  intro x
  change privateWord shape (localOrigin B u (privateShelfIndex B j)).isSome.toNat _ _ _=_
  cases hit:localOrigin B u (privateShelfIndex B j) with
  | none => simp [x,hit,private_dead]
  | some e =>
    obtain ⟨p,edge,slot⟩:=(private_shelf_iff B u j e).1 hit
    have touched:=e.property.2
    rw [edge] at touched
    have canonical:=private_word B u p (private_owner B u p touched)
    change privateOrdinal B p=j at slot
    simpa [x,hit,edge,slot] using canonical

theorem private_origin_small (u : Host) (j : Fin (privateCount B)) :
    ((localOrigin B u (privateShelfIndex B j)).elim 0 (fun e=>wordNumber B u e.val))<
        2^(DescentSharedCableNames.Packed.bits (publicShape B).count) := by
  cases found : localOrigin B u (privateShelfIndex B j) with
  | none => exact Nat.two_pow_pos _
  | some e => exact public_word_room B e.val

open DescentPackedZip DescentResetMixedWordRAM.OriginalDate
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM

def privateShelf : Fin (privateCount B)↪Fin (totalLocal B) where
  toFun:=privateShelfIndex B
  inj':=fun a b eqn=>by
    apply Fin.ext
    have h:=congrArg Fin.val eqn
    change stemsCount B+1+contactCount B+a.val=stemsCount B+1+contactCount B+b.val at h
    omega

/-- All private slots use one decoder and one shared masked literal dictionary.
Only their existing physical metadata, zero and old self-halo expressions vary. -/
def privateOriginalDate (X H Gs M metaBits zeroBits haloBits argBits argBase header original : ℕ)
    («meta» : Fin X→Fin (privateCount B)→Expr) (zero selfHalo : Fin X→Expr) :
    Date X (privateCount B) (totalLocal B) where
  shelf:=privateShelf B
  kind:=fun _=>0
  header:=header
  original:=original
  rows:=H*chunks Gs M
  lanes:=M
  metaBits:=metaBits
  zeroBits:=zeroBits
  haloBits:=haloBits
  argBits:=argBits
  wordBits:=DescentSharedCableNames.Packed.bits (publicShape B).count
  fn:=fun _=>privateWord shape
  «fields»:={
    «meta»:=fun p=>let q:=finProdFinEquiv.symm p;«meta» q.1 q.2
    zero:=fun p=>zero (finProdFinEquiv.symm p).1
    halo:=fun p=>selfHalo (finProdFinEquiv.symm p).1
    arg:=fun p=>DescentUniformSlotOperands.expr argBase H Gs M argBits (finProdFinEquiv.symm p).2}

private theorem cast_origin {α : Type*} (b : ℕ) (x : Option α) (f : α → ℕ) :
    x.elim 0 (fun a => (f a : Cell b)) = ((x.elim 0 f : ℕ) : Cell b) := by
  cases x <;> rfl

set_option maxHeartbeats 800000 in
/-- On the literal return memory of the scatter, the private original bank reads
the number assigned by the same native parent codec as the mixed public dates. -/
theorem private_posted {X H Gs : ℕ} (L : Date X (privateCount B) (totalLocal B))
    (shelf : L.shelf=privateShelf B) (kind : ∀j,L.fn (L.kind j)=privateWord shape)
    (room : L.Room w) (m : Memory w) (x : Fin X) (j : Fin (privateCount B))
    (rows : L.rows=H*chunks Gs L.lanes) (hosts : Fin H→Fin Gs→Host)
    (src : Fin H→Fin Gs→Meta) (mb : 0<L.metaBits) (zb : 0<L.zeroBits)
    (active : ∀v g,(src v g).live=(localOrigin B (hosts v g) (privateShelfIndex B j)).isSome)
    (haloFit : ∀v g,haloNumber B (hosts v g) (receiverRoot B (hosts v g)).1<2^L.haloBits)
    (slotFit : j.val<2^L.argBits)
    (ms : Source (L.fields.meta (finProdFinEquiv (x,j))) (fun h g=>DescentResetFieldAssembler.raw L.metaBits (src h g)) L.lanes m)
    (zs : Source (L.fields.zero (finProdFinEquiv (x,j))) (fun h g=>((zeroCoarse B (hosts h g)).toNat:Cell L.zeroBits)) L.lanes m)
    (hs : Source (L.fields.halo (finProdFinEquiv (x,j))) (fun h g=>(haloNumber B (hosts h g) (receiverRoot B (hosts h g)).1:Cell L.haloBits)) L.lanes m)
    (ds : Source (L.fields.arg (finProdFinEquiv (x,j))) (fun _ : Fin H=>fun _ : Fin Gs=>(j.val:Cell L.argBits)) L.lanes m) :
    Source (.lookup (DescentResetOriginalSlots.bank L.original L.rows (totalLocal B) x.val (privateShelfIndex B j).val) .row)
      (fun h g=>((localOrigin B (hosts h g) (privateShelfIndex B j)).elim 0
        (fun e=>wordNumber B (hosts h g) e.val):Cell L.wordBits)) L.lanes (L.dst m) := by
  have fetched:=L.posted room m x j rows src (fun h g=>zeroCoarse B (hosts h g)) _ _ mb zb
    (by rw [kind];rfl) ms zs hs ds
  rw [OriginalDate.Date.output,shelf] at fetched
  convert fetched using 1
  · rfl
  · funext h g
    rw [kind,active,Fin.val_cast_of_lt (haloFit h g),Fin.val_cast_of_lt slotFit]
    apply (cast_origin _ _ _).trans
    exact congrArg (fun j : ℕ => (j : Cell L.wordBits)) (private_slot_word B (hosts h g) j).symm


set_option maxHeartbeats 800000 in
/-- A compact physical roster can have ghost hosts. On these rows the zero live
bit alone makes the original wire number zero, regardless of the halo input. -/
theorem private_posted_rows {X H Gs : ℕ} (L : Date X (privateCount B) (totalLocal B))
    (shelf : L.shelf=privateShelf B) (kind : ∀j,L.fn (L.kind j)=privateWord shape)
    (room : L.Room w) (m : Memory w) (x : Fin X) (j : Fin (privateCount B))
    (rows : L.rows=H*chunks Gs L.lanes) (host : Fin H→Fin Gs→Option Host)
    (src : Fin H→Fin Gs→Meta) (zero : Fin H→Fin Gs→Bool) (halo : Fin H→Fin Gs→Cell L.haloBits)
    (mb : 0<L.metaBits) (zb : 0<L.zeroBits) (slotFit : j.val<2^L.argBits)
    (active : ∀h g,(src h g).live=(host h g).any (fun u=>(localOrigin B u (privateShelfIndex B j)).isSome))
    (zeroAt : ∀h g u,host h g=some u→zero h g=zeroCoarse B u)
    (haloAt : ∀h g u,host h g=some u→(halo h g).val=haloNumber B u (receiverRoot B u).1)
    (ms : Source (L.fields.meta (finProdFinEquiv (x,j))) (fun h g=>DescentResetFieldAssembler.raw L.metaBits (src h g)) L.lanes m)
    (zs : Source (L.fields.zero (finProdFinEquiv (x,j))) (fun h g=>((zero h g).toNat:Cell L.zeroBits)) L.lanes m)
    (hs : Source (L.fields.halo (finProdFinEquiv (x,j))) halo L.lanes m)
    (ds : Source (L.fields.arg (finProdFinEquiv (x,j))) (fun _ : Fin H=>fun _ : Fin Gs=>(j.val:Cell L.argBits)) L.lanes m) :
    Source (.lookup (DescentResetOriginalSlots.bank L.original L.rows (totalLocal B) x.val (privateShelfIndex B j).val) .row)
      (fun h g=>((host h g).elim 0 (fun u=>(localOrigin B u (privateShelfIndex B j)).elim 0
        (fun e=>wordNumber B u e.val)):Cell L.wordBits)) L.lanes (L.dst m) := by
  have fetched:=L.posted room m x j rows src zero halo _ mb zb (by rw [kind];rfl) ms zs hs ds
  rw [OriginalDate.Date.output,shelf] at fetched
  convert fetched using 1
  · rfl
  · funext h g
    rw [kind,active,Fin.val_cast_of_lt slotFit]
    cases hit : host h g with
    | none => simp [private_dead]
    | some u =>
      simp [zeroAt h g u hit,haloAt h g u hit,private_slot_word B]
      exact cast_origin _ _ _

/-- Mount the candidate ordinals once and execute the sparse private date.
Every returned lane reads its true graph number on the actual final memory. -/
theorem private_executed {X H Gs M mb zb hb ab argBase header original : ℕ}
    («meta» : Fin X→Fin (privateCount B)→Expr) (zero selfHalo : Fin X→Expr)
    (m : Memory w)
    (small : privateCount B ≤ 2^ab)
    (operandRoom : DescentUniformSlotOperands.stop argBase (privateCount B) H Gs M ab<2^w)
    (r : (privateOriginalDate B X H Gs M mb zb hb ab argBase header original «meta» zero selfHalo).Room w)
    (fm : ∀x j,(«meta» x j).Fits w argBase) (fz : ∀x,(zero x).Fits w argBase)
    (fh : ∀x,(selfHalo x).Fits w argBase) (mbPos : 0< mb) (zbPos : 0<zb)
    (hosts : Fin X→Fin H→Fin Gs→Host) (src : Fin X→Fin (privateCount B)→Fin H→Fin Gs→Meta)
    (active : ∀x j v g,(src x j v g).live=(localOrigin B (hosts x v g) (privateShelfIndex B j)).isSome)
    (haloFit : ∀x v g,haloNumber B (hosts x v g) (receiverRoot B (hosts x v g)).1<2^hb)
    (ms : ∀x j,Source («meta» x j) (fun h g=>DescentResetFieldAssembler.raw mb (src x j h g)) M m)
    (zs : ∀x,Source (zero x) (fun h g=>((zeroCoarse B (hosts x h g)).toNat:Cell zb)) M m)
    (hs : ∀x,Source (selfHalo x) (fun h g=>(haloNumber B (hosts x h g)
       (receiverRoot B (hosts x h g)).1:Cell hb)) M m) :
    let L:=privateOriginalDate B X H Gs M mb zb hb ab argBase header original «meta» zero selfHalo
    let J:=privateCount B
    let N:=DescentResetHaloBroadcast.count H Gs M ab
    let staged:=DescentUniformSlotOperands.result argBase J H Gs M ab m
    ((DescentUniformSlotOperands.program argBase J H Gs M ab w).seq (L.code w)).Exec m (L.dst staged)
      (((4+10*J)+(4+10*N))+L.ticks) ∧
    ∀x j, Source (.lookup (DescentResetOriginalSlots.bank original (H*chunks Gs M)
      (totalLocal B) x.val (privateShelfIndex B j).val) .row)
      (fun h g=>((localOrigin B (hosts x h g) (privateShelfIndex B j)).elim 0
        (fun e=>wordNumber B (hosts x h g) e.val):Cell L.wordBits)) M (L.dst staged) := by
  intro L J N staged
  obtain ⟨mounted,digits,frame,_⟩:=DescentUniformSlotOperands.produce argBase J H Gs M ab m small operandRoom
  have kept {bits : ℕ} (e : Expr) (vals : Fin H→Fin Gs→Cell bits) (fit : e.Fits w argBase)
      (read : Source e vals M m) : Source e vals M staged :=
    fun p=>(ProtocolRAM.eval_below e _ m staged fit (fun a ha=>frame a (.inl ha))).trans (read p)
  refine ⟨mounted.then (L.any r staged).1,?_⟩
  intro x j
  apply private_posted B L rfl (fun _=>rfl) r staged x j rfl (hosts x) (src x j)
    mbPos zbPos (active x j) (haloFit x) (j.isLt.trans_le small)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact kept _ _ (fm x j) (ms x j)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact kept _ _ (fz x) (zs x)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact kept _ _ (fh x) (hs x)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact digits j

/-- Physical compact-host execution, including all unoccupied capacity rows. -/
theorem private_compact_run {X H Gs M mb zb hb ab argBase header original : ℕ}
    («meta» : Fin X→Fin (privateCount B)→Expr) (zero selfHalo : Fin X→Expr)
    (m : Memory w)
    (small : privateCount B ≤ 2^ab)
    (operandRoom : DescentUniformSlotOperands.stop argBase (privateCount B) H Gs M ab<2^w)
    (r : (privateOriginalDate B X H Gs M mb zb hb ab argBase header original «meta» zero selfHalo).Room w)
    (fm : ∀x j,(«meta» x j).Fits w argBase) (fz : ∀x,(zero x).Fits w argBase)
    (fh : ∀x,(selfHalo x).Fits w argBase) (mbPos : 0< mb) (zbPos : 0<zb)
    (hosts : Fin X→Fin H→Fin Gs→Option Host)
    (zvalue : Fin X→Fin H→Fin Gs→Bool) (hvalue : Fin X→Fin H→Fin Gs→Cell hb) (src : Fin X→Fin (privateCount B)→Fin H→Fin Gs→Meta)
    (active : ∀x j v g,(src x j v g).live=(hosts x v g).any (fun u=>(localOrigin B u (privateShelfIndex B j)).isSome))
    (zeroAt : ∀x h g u,hosts x h g=some u→zvalue x h g=zeroCoarse B u)
    (haloAt : ∀x h g u,hosts x h g=some u→(hvalue x h g).val=haloNumber B u (receiverRoot B u).1)
    (ms : ∀x j,Source («meta» x j) (fun h g=>DescentResetFieldAssembler.raw mb (src x j h g)) M m)
    (zs : ∀x,Source (zero x) (fun h g=>((zvalue x h g).toNat:Cell zb)) M m)
    (hs : ∀x,Source (selfHalo x) (hvalue x) M m) :
    let L:=privateOriginalDate B X H Gs M mb zb hb ab argBase header original «meta» zero selfHalo
    let J:=privateCount B
    let N:=DescentResetHaloBroadcast.count H Gs M ab
    let staged:=DescentUniformSlotOperands.result argBase J H Gs M ab m
    ((DescentUniformSlotOperands.program argBase J H Gs M ab w).seq (L.code w)).Exec m (L.dst staged)
      (((4+10*J)+(4+10*N))+L.ticks) ∧
    ∀x j, Source (.lookup (DescentResetOriginalSlots.bank original (H*chunks Gs M)
      (totalLocal B) x.val (privateShelfIndex B j).val) .row)
      (fun h g=>((hosts x h g).elim 0 (fun u=>(localOrigin B u (privateShelfIndex B j)).elim 0
        (fun e=>wordNumber B u e.val)):Cell L.wordBits)) M (L.dst staged) := by
  intro L J N staged
  obtain ⟨mounted,digits,frame,_⟩:=DescentUniformSlotOperands.produce argBase J H Gs M ab m small operandRoom
  have kept {bits : ℕ} (e : Expr) (vals : Fin H→Fin Gs→Cell bits) (fit : e.Fits w argBase)
      (read : Source e vals M m) : Source e vals M staged :=
    fun p=>(ProtocolRAM.eval_below e _ m staged fit (fun a ha=>frame a (.inl ha))).trans (read p)
  refine ⟨mounted.then (L.any r staged).1,?_⟩
  intro x j
  apply private_posted_rows B L rfl (fun _=>rfl) r staged x j rfl (hosts x) (src x j)
    (zvalue x) (hvalue x) mbPos zbPos (j.isLt.trans_le small) (active x j) (zeroAt x) (haloAt x)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact kept _ _ (fm x j) (ms x j)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact kept _ _ (fz x) (zs x)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact kept _ _ (fh x) (hs x)
  · simp only [L,privateOriginalDate, Equiv.symm_apply_apply]
    exact digits j


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
