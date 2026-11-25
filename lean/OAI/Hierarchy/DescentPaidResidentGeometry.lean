import OAI.Hierarchy.DescentPaidResidentCount
import OAI.Hierarchy.DescentOrdinaryActorInputs
import OAI.Hierarchy.DescentOrdinaryParticleReceipt

namespace OAI
/-! # True per-receiver record lengths, including coalesced hubs and renamed sites -/
namespace Hierarchy.DescentPaidResidentCount
open DescentSIMDLookup DescentPackedActorMask
open DescentSixParty DescentHostDirectory DescentSharedCableNames DescentCableDonorNames
open Computability.BorderVNP.Crossing GadgetNetwork MarkedWorld StarKeys
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

def fiberJoin {X Y Z : Type} (f : X→Y) (g : Y→Z) (z : Z) :
    (Σy : {y //g y=z},{x //f x=y.val}) ≃ {x //g (f x)=z} where
  toFun x:=⟨x.2.val,(congrArg g x.2.property).trans x.1.property⟩
  invFun x:=⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
  left_inv := by
    rintro ⟨⟨y,h⟩,⟨x,eqn⟩⟩
    change f x = y at eqn
    subst y
    rfl
  right_inv:=by intro x;rfl

theorem nested {X Y Z : Type} [Fintype X] [Fintype Y] (f : X→Y) (g : Y→Z) (z : Z) (cost : X→ℕ) :
    (∑y : {y //g y=z}, ∑x : {x //f x=y.val},cost x.val)=∑x : {x //g (f x)=z},cost x.val := by
  rw [←Fintype.sum_sigma']
  exact (fiberJoin f g z).sum_comp (fun x=>cost x.val)

def total {O B X : Type} [Fintype O] [Fintype B] (loc : O ⊕ B→X) (rec : O→ℕ) (v : X) : ℕ :=
  (∑u : {u : O //loc (.inl u)=v},rec u.val)+Fintype.card {t : B //loc (.inr t)=v}

private theorem sum_all_eq {X : Type} {a b : Fintype X} {f g : X → ℕ}
    (h : ∀x,f x=g x) : (@Finset.univ X a).sum f=(@Finset.univ X b).sum g := by
  cases Subsingleton.elim a b
  exact Finset.sum_congr rfl (fun x _ => h x)

private theorem card_all_eq {X : Type} {a b : Fintype X} :
    @Fintype.card X a = @Fintype.card X b :=
  congrArg (@Fintype.card X) (Subsingleton.elim a b)

private theorem nested_total {O B Y Z : Type} [Fintype O] [Fintype B] [Fintype Y]
    (first : O ⊕ B → Y) (second : Y → Z) (charge : O → ℕ) (c : Z) :
    (∑v : {v //second v=c},total first charge v.val)=total (second ∘ first) charge c := by
  unfold total
  rw [Finset.sum_add_distrib]
  apply congrArg₂ Nat.add
  · exact nested (fun u => first (.inl u)) second c charge
  · have count := nested (fun t => first (.inr t)) second c (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.mul_one, Nat.cast_id] at count
    refine Eq.trans ?_ (count.trans ?_)
    · exact sum_all_eq (fun _ => card_all_eq)
    · exact card_all_eq

private abbrev lengthClaim {F : Type*} [Field F] {d : ℕ} {P V O B E : Type}
    {bits : P → ℕ} [DecidableEq V] [Fintype O] [Fintype B] (A : MarkedWorld F d P bits)
    (key : A.graph.Site ↪ Key V) (hub : V → Bool) (k g : ℕ)
    (first : O ⊕ B → A.graph.Site) (charge : O → ℕ) (rows : A.graph.Site → List E)
    (c : (coalesced A key hub k g).graph.Site) : Prop :=
  (coalescedRecords A key hub k g rows c).length =
    total (address A key hub k g ∘ first) charge c

private theorem coalesced_total {F : Type*} [Field F] {d : ℕ} {P V O B E : Type}
    {bits : P → ℕ} [DecidableEq V] [Fintype O] [Fintype B] (A : MarkedWorld F d P bits)
    (key : A.graph.Site ↪ Key V) (hub : V → Bool) (k g : ℕ)
    (first : O ⊕ B → A.graph.Site) (charge : O → ℕ) (rows : A.graph.Site → List E)
    (counts : ∀v,(rows v).length=total first charge v)
    (c : (coalesced A key hub k g).graph.Site) :
    lengthClaim A key hub k g first charge rows c := by
  unfold lengthClaim
  refine (coalescedRecords_length A key hub k g rows c).trans ?_
  refine Eq.trans ?_ (nested_total first (address A key hub k g) charge c)
  exact sum_all_eq (fun v => counts v.val)

private structure CountFact where
  statement : Prop
  checked : statement

private structure RecordCounts (O B X E : Type) [Fintype O] [Fintype B] where
  venue : O ⊕ B → X
  charge : O → ℕ
  rows : X → List E
  counted : ∀ v, (rows v).length = total venue charge v

private def coalescedCountFact {F : Type*} [Field F] {d : ℕ} {P V O B E : Type}
    {bits : P → ℕ} [DecidableEq V] [Fintype O] [Fintype B] (A : MarkedWorld F d P bits)
    (keys : A.graph.Site ↪ Key V) (flag : V → Bool) (k g : ℕ)
    (data : RecordCounts O B A.graph.Site E) : CountFact :=
  ⟨∀ c, lengthClaim A keys flag k g data.venue data.charge data.rows c,
    coalesced_total A keys flag k g data.venue data.charge data.rows data.counted⟩

private theorem new_records_total {d : ℕ} {P I C Atom : Type} {bits : P → ℕ} [Fintype I]
    (N : Network d P bits) (pick : I × Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site → C)
    (rec : N.Site → List Atom) {bound : ℕ} (z : I → ℕ) (p : I → Profile bound)
    (v : Merged N pick layout pack) :
    (newRecords N pick layout pack rec z p v).length =
      total (newSite N pick layout pack) (fun u => (rec u).length) v := by
  refine (newRecords_length N pick layout pack rec z p v).trans ?_
  unfold total siteBirths
  exact congrArg₂ Nat.add (sum_all_eq (fun _ => rfl)) card_all_eq

private def newRecordCounts {d : ℕ} {P I C Atom : Type} {bits : P → ℕ} [Fintype I]
    (N : Network d P bits) (pick : I × Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site → C)
    (rec : N.Site → List Atom) {bound : ℕ} (z : I → ℕ) (p : I → Profile bound) :
    RecordCounts N.Site (I × Fin 6) (Merged N pick layout pack) (Record Atom bound) where
  venue := newSite N pick layout pack
  charge := fun u => (rec u).length
  rows := newRecords N pick layout pack rec z p
  counted := new_records_total N pick layout pack rec z p

section Stage
variable {F : Type*} [Field F] {d : ℕ} {I C P V Atom : Type} [Fintype I] [DecidableEq V] {bits : P→ℕ}

set_option maxHeartbeats 1600000 in
private def selectedCountFact (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (pick : I × Fin 2 ↪ W.graph.Edge) (z : I → ℕ) (hz : ∀ i, 0 < z i)
    (fit : ∀ i s, W.graph.width (pick (i,s)) = z i * G.b)
    (pack : W.graph.Site → C) (p : I → Profile G.C)
    (keys : (W.selected G pick z hz fit pack p).graph.Site ↪ Key V) (flag : V → Bool) (k g : ℕ)
    (rec : W.graph.Site → List Atom) : CountFact :=
  coalescedCountFact (F:=F) (d:=d) (P:=P) (bits:=bits) (V:=V)
    (O:=W.graph.Site) (B:=I × Fin 6) (E:=Record Atom G.C)
    (W.selected G pick z hz fit pack p) keys flag k g
    (newRecordCounts W.graph pick (bestLayout (branchWidth G z p)) pack rec z p)

/-- The actual retained list of the `ParticleRows.stage` constructor. An old
record contributes its previous funded multiplicity; a genuine birth contributes one. -/
theorem site_length (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (pick : I × Fin 2 ↪ W.graph.Edge) (z : I → ℕ) (hz : ∀ i, 0 < z i)
    (fit : ∀ i s, W.graph.width (pick (i,s)) = z i * G.b)
    (pack : W.graph.Site → C) (p : I → Profile G.C)
    (key : (W.selected G pick z hz fit pack p).graph.Site ↪ Key V) (hub : V → Bool) (k g : ℕ)
    (rec : W.graph.Site → List Atom) :
    (selectedCountFact W G pick z hz fit pack p key hub k g rec).statement :=
  (selectedCountFact W G pick z hz fit pack p key hub k g rec).checked

end Stage

section Issuance
variable {F P J V I C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype C] {d k age D b n : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S age) (pick : I×Fin 2↪W.graph.Edge) (picked : ∀i,pick (i,0)∈W.core)
    (dest : W.graph.Site ⊕ (I×Fin 6)→C) (halo : Halo C W.graph.Site D)
    (oldHere : ∀u,u∈halo.member (dest (.inl u)))
    (bornHere : ∀i j,W.graph.src (pick (i,0))∈halo.member (dest (.inr (i,j))))
local notation "slot" => DescentOrdinaryLocalBirth.outgoingSlot A native S ready pick picked

private theorem memberAt {α β : Type} {slots : ℕ} (h : Halo α β slots)
    {x y : α} {v : β} (same : x=y) (member : v∈h.member x) : v∈h.member y :=
  (congrArg (fun t : α => v∈h.member t) same).mp member

def prior (c : C) : {u : W.graph.Site // dest (.inl u) = c} ↪ Fin D where
  toFun u:=halo.slot c ⟨u.val,memberAt halo u.property (oldHere u.val)⟩
  inj' := by
    intro u v same
    apply Subtype.ext
    exact congrArg (fun x : ↥(halo.member c) => x.val) ((halo.slot c).injective same)

def birth (c : C) : {ij : I×Fin 6 // dest (.inr ij) = c} ↪ Fin (D*(A.cap*6)) where
  toFun t:=finProdFinEquiv (halo.slot c ⟨W.graph.src (pick (t.val.1,0)),memberAt halo t.property (bornHere t.val.1 t.val.2)⟩,
    finProdFinEquiv (slot t.val.1,t.val.2))
  inj' := by
    rintro ⟨⟨i,j⟩,hi⟩ ⟨⟨i',j'⟩,hj⟩ same
    have fields := (finProdFinEquiv (m:=D) (n:=A.cap*6)).injective same
    have src : W.graph.src (pick (i,0))=W.graph.src (pick (i',0)) :=
      congrArg Subtype.val ((halo.slot c).injective (congrArg Prod.fst fields))
    have localFields := (finProdFinEquiv (m:=A.cap) (n:=6)).injective (congrArg Prod.snd fields)
    have edge := Stage.outgoing_identify A native S ready
      ⟨pick (i,0),A.quantum_positive _ (picked i)⟩ ⟨pick (i',0),A.quantum_positive _ (picked i')⟩ src
      (congrArg Prod.fst localFields)
    have sourcePair : (i,(0 : Fin 2)) = (i',(0 : Fin 2)) := pick.injective (congrArg Subtype.val edge)
    have sameActor : i = i' := congrArg (fun t : I × Fin 2 => t.1) sourcePair
    have sameRole : j = j' := congrArg (fun t : Fin A.cap × Fin 6 => t.2) localFields
    apply Subtype.ext
    change (i,j) = (i',j')
    exact Prod.ext sameActor sameRole

variable (c : C) (wanted : Cell n) (addresses : Fin (actors D A.cap)→Cell n)
    (counts : Fin D→Cell b) (rec : W.graph.Site→ℕ)
local notation "donor" => DescentOrdinaryLocalBirth.donorAt halo c

include oldHere bornHere in
omit [Fintype C] in
/-- Real signed old slots and matched role destinations give exactly the prior
charged lengths and six individual births landing at this receiver. -/
theorem issued (active : wanted≠0)
    (oldAddressRead : ∀v,addresses (oldAddress A.cap v)=wanted ↔ ∃u,donor v=some u ∧ dest (.inl u)=c)
    (birthAddressRead : ∀v s j,addresses (bornAddress v (finProdFinEquiv (s,j)))=wanted ↔
      ∃i,donor v=some (W.graph.src (pick (i,0))) ∧ slot i=s ∧ dest (.inr (i,j))=c)
    (oldRead : ∀v,(counts v).val=(donor v).elim 0 rec) :
    counted D A.cap b (target n _ wanted (encode n _ addresses)) (encode b _ counts)=
      ((∑u : {u : W.graph.Site // dest (.inl u) = c},rec u.val)+Fintype.card ({ij : I×Fin 6 // dest (.inr ij) = c}):ℕ) := by
  let oldSlot := prior (W:=W) dest halo oldHere c
  let birthSlotMap := birth A native S ready pick picked dest halo bornHere c
  apply paid oldSlot birthSlotMap (fun u=>rec u.val) wanted addresses counts active
  · intro v
    rw [oldAddressRead]
    constructor
    · rintro ⟨u,present,owned⟩
      exact ⟨⟨u,owned⟩,((DescentOrdinaryLocalBirth.donorAt_eq halo c).mp present).choose_spec⟩
    · rintro ⟨u,rfl⟩
      exact ⟨u.val,(DescentOrdinaryLocalBirth.donorAt_eq halo c).mpr
        ⟨memberAt halo u.property (oldHere u.val),rfl⟩,u.property⟩
  · intro t
    obtain ⟨⟨v,t⟩,rfl⟩ := (finProdFinEquiv (m:=D) (n:=A.cap*6)).surjective t
    obtain ⟨⟨s,j⟩,rfl⟩ := (finProdFinEquiv (m:=A.cap) (n:=6)).surjective t
    simp only [birthSlot,Equiv.symm_apply_apply,birthAddressRead]
    constructor
    · rintro ⟨i,got,same,owned⟩
      refine ⟨⟨⟨i,j⟩,owned⟩,?_⟩
      apply congrArg (finProdFinEquiv (m:=D) (n:=A.cap*6))
      exact Prod.ext ((DescentOrdinaryLocalBirth.donorAt_eq halo c).mp got).choose_spec
        (congrArg (fun t : Fin A.cap => finProdFinEquiv (t,j)) same)
    · rintro ⟨⟨⟨i,q⟩,owned⟩,same⟩
      have pair := (finProdFinEquiv (m:=D) (n:=A.cap*6)).injective same
      have t := (finProdFinEquiv (m:=A.cap) (n:=6)).injective (congrArg Prod.snd pair)
      have role:q=j:=congrArg (fun u : Fin A.cap × Fin 6 => u.2) t
      subst q
      exact ⟨i,(DescentOrdinaryLocalBirth.donorAt_eq halo c).mpr
        ⟨memberAt halo owned (bornHere i j),congrArg Prod.fst pair⟩,congrArg Prod.fst t,owned⟩
  · intro u
    have present : donor (oldSlot u)=some u.val :=
      (DescentOrdinaryLocalBirth.donorAt_eq halo c).mpr ⟨memberAt halo u.property (oldHere u.val),rfl⟩
    rw [oldRead,present]; rfl

end Issuance
section Trajectory
open DescentKernelHistory
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {u ε : ℝ} (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
private abbrev receiverWorld :=
  let r := BitDescription.scannedRows he T
  W.selected G r.pick (fun _ => T.z) (fun _ => T.unitPos) r.fit r.pack (r.profile c)

private abbrev receiverActors :=
  W.graph.Site ⊕ ((BitDescription.scannedRows he T).pairs × Fin 6)

private abbrev receiverVenue :=
  let r := BitDescription.scannedRows he T
  newSite W.graph r.pick (bestLayout (branchWidth G (fun _ => T.z) (r.profile c))) r.pack

theorem reindex {O B X Y : Type} [Fintype O] [Fintype B] (loc : O ⊕ B→X) (rec : O→ℕ)
    (e : X≃Y) (v : Y) : total (e∘loc) rec v=total loc rec (e.symm v) := by
  let old : {a : O // (e ∘ loc) (.inl a) = v} ≃ {a : O // loc (.inl a) = e.symm v} :=
    Equiv.subtypeEquivRight fun _ => e.eq_symm_apply.symm
  let born : {a : B // (e ∘ loc) (.inr a) = v} ≃ {a : B // loc (.inr a) = e.symm v} :=
    Equiv.subtypeEquivRight fun _ => e.eq_symm_apply.symm
  exact congrArg₂ Nat.add (Fintype.sum_equiv old _ _ (fun _ => rfl)) (Fintype.card_congr born)

def changeLand {N M : MarkedWorld F d P bits} {Y : Type} (same : N=M) (f : Y→M.graph.Site) :
    Y→N.graph.Site := same.symm ▸ f

omit [Field F] in
theorem transfer_total {N M : MarkedWorld F d P bits} {O B : Type} [Fintype O] [Fintype B]
    (same : N=M) (land : O ⊕ B→M.graph.Site) (rec : O→ℕ) (counts : M.graph.Site→ℕ)
    (sound : ∀v,counts v=total land rec v) (v : N.graph.Site) :
    transferRow same counts v=total (changeLand same land) rec v := by
  subst M;exact sound v

/-- These are the actual two venue maps followed by precisely the reported
physical renamings. This inductive receipt excludes unrelated relabellings. -/
inductive Lands (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice) :
    (N : MarkedWorld F d P bits) → (norm : Normalize N) →
    (receiverActors he T → norm.result.graph.Site) → Prop where
  | stage {V : Type} [DecidableEq V] (key : (receiverWorld he T c).graph.Site ↪ Key V) (flag : V→Bool)
      (k g q : ℕ) (old : ∀e∈W.core,q∣W.graph.width e)
      (used : ∀j,(BitDescription.scannedRows he T).pick j∈W.core)
      (chunks : ∀_i : (BitDescription.scannedRows he T).pairs,q∣T.z) :
      Lands he T c _ (subroundNormalize W G (BitDescription.scannedRows he T).pick
        (fun _ => T.z) (fun _ => T.unitPos) (BitDescription.scannedRows he T).fit
        (BitDescription.scannedRows he T).pack ((BitDescription.scannedRows he T).profile c)
        key flag k g q old used chunks)
        (address (receiverWorld he T c) key flag k g ∘ receiverVenue he T c)
  | named {N : MarkedWorld F d P bits} (norm : Normalize N)
      (land : receiverActors he T → norm.result.graph.Site)
      (prior : Lands he T c _ norm land) (s : Equiv.Perm norm.result.graph.Site) (e : Equiv.Perm norm.result.graph.Edge) :
      Lands he T c _ (norm.appendNames s e) (changeLand (norm.appendNames_result s e) (s∘land))

set_option maxHeartbeats 1600000 in
theorem trajectory {N : MarkedWorld F d P bits} {norm : Normalize N} {counts : norm.result.graph.Site→ℕ}
    {hub : norm.result.graph.Site→Bool} (receipt : ParticleRows he T c N norm counts hub) :
    ∃land : receiverActors he T → norm.result.graph.Site,Lands he T c N norm land ∧
      ∀v,counts v=total land (fun u=>(T.records u).length) v := by
  induction receipt with
  | stage key flag pos tags k g q old used chunks inc packed same =>
    let r := BitDescription.scannedRows he T
    refine ⟨address (receiverWorld he T c) key flag k g ∘ receiverVenue he T c,
      .stage key flag k g q old used chunks, ?_⟩
    intro v
    exact site_length W G r.pick (fun _ => T.z) (fun _ => T.unitPos)
      r.fit r.pack (r.profile c) key flag k g T.records v
  | named norm prior s e ih =>
    obtain ⟨land,auth,count⟩:=ih
    exact ⟨_,.named norm land auth s e,transfer_total (norm.appendNames_result s e) (s∘land) _ _
      (fun v=>(count (s.symm v)).trans (reindex land _ s v).symm)⟩

end Trajectory
end
end Hierarchy.DescentPaidResidentCount

end OAI
