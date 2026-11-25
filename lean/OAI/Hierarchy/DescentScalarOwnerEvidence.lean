import OAI.Hierarchy.DescentScalarVenueEvidence
import OAI.Hierarchy.DescentScalarActorPublisher
import OAI.Hierarchy.DescentPackedParentIncidence
import OAI.Hierarchy.DescentPackedMatchPrepareIssued

namespace OAI
/-! # A source ticket decoded from its actual mask and its two owner arrays -/
namespace Hierarchy.DescentScalarVenueMask
open DescentSIMDLookup DescentPacking.PackedMatch.Local DescentSixParty DescentSixParty.StarKeys DescentHostDirectory
open DescentStageEdgeReceipt DescentHaloWalkRAM DescentSharedCableNames
open scoped Classical Fin.CommRing
noncomputable section
variable {r D cap d : ℕ}

private theorem fields_zero (a n : ℕ) : (encode a n).symm 0=(fun _=>0):=by
  apply (encode a n).symm_apply_eq.mpr;apply Fin.ext
  change 0=(finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val;simp

private theorem real_hop {Z : Type} {next : Z→Fin D→Option Z} {z : Z} {w : Walk} {target : Key Z} (ok : walked next z w target) : w.1≤D:=by
  have path:=ok.1;change (location next z (w.1,0,0)).bind _=some target.1 at path
  cases h:location next z (w.1,0,0) with
  | none=>simp [h] at path
  | some y=>exact ActorPath.bounds next (w.1,0,0) h

private theorem head_bound (B n : ℕ) (u : Panel r D (2*cap) d) (l : Bool) (rows : Fin (D+1)→Owners.Register r D d)
    (x : Fin r) (s : Fin (2*cap)) (j : Fin 6) (f : Fin 6→Walk)
    (born : (actorHeads B n u l (Owners.addressed (rows 0)) (fun v=>Owners.addressed (rows v.succ)) x s).born=some f)
    (first : (f j).1≤D) : Bounded (Owners.digits r D d) (f j):=by
  unfold actorHeads at born;dsimp only at born
  obtain ⟨i,_,h⟩:=Option.map_eq_some_iff.mp born
  subst f;exact look_fit (rows 0) (fun v=>rows v.succ) _ first

/-- Read the complete party tag at the actual selected first-grain slot.
The valid first hop supplies the only field width beyond those inherent
in the three-component owner registers. -/
theorem from_head {Z : Type} (step : Z→Fin D→Option Z) (root : Z) (B n slots raw : ℕ) (u : Panel r D (2*cap) d)
    (l : Bool) (rows : Fin (D+1)→Owners.Register r D d) (x : Fin r) (s : Fin cap) (j : Fin 6) (mask : Cell (1*r))
    (live : (encode 1 r).symm mask x≠0) (won : u.winner x≠0) (width : 0<Owners.digits r D d)
    (trace : ∀f,(actorHeads B n u l (Owners.addressed (rows 0)) (fun v=>Owners.addressed (rows v.succ)) x (s.castLE (by omega : cap≤2*cap))).born=some f→∃a,walked step root (f j) a) :
    let t:=(s.castLE (by omega : cap≤2*cap));let q:=actorHeads B n u l (Owners.addressed (rows 0)) (fun v=>Owners.addressed (rows v.succ)) x t
    let head:=Owners.report r D (2*cap) d B n (Owners.register l u) (encode _ (D+1) rows)
    newTicket x t j slots raw mask head=q.born.bind (fun f=>issue D slots raw (f j)) :=by
  dsimp only;apply new_at _ _ _ _ _ _ (Owners.from_active u l B n x _ won rows) live width
  intro f obs;obtain ⟨a,walk⟩:=trace f obs
  exact head_bound B n u l rows x _ j f obs (real_hop walk)

namespace Stage
open DescentPacking
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
open DescentPacking.PackedMatch.Local.Stage
local notation "names"=>cableNames k rank
local notation "next"=>rotor A rank
local notation "panel"=>terrain (short:=short) A native S ready names win next
local notation "addr"=>nativeAddress he A.stage
local notation "home"=>scanHomeAt he A.stage
local notation "color"=>scanColorAt he A.stage
local notation "N"=>W.graph
local notation "pick"=>colorPick N W.core home color A.cap
local notation "pairs"=>NativePair N W.core home color A.cap
local notation "slot"=>DescentSharedCableNames.Stage.outgoing A native S ready
local notation "paid"=>fun p : pairs => picked A he (Sigma.fst p) (Sigma.snd p) true

def firstGrain (p : pairs) : DescentSharedCableNames.Stage.Positive A:=
  ⟨pick (p,0),A.quantum_positive _ (by
    have h : (paid p).val=pick (p,0):=picked_old A he p.1 p.2 true
    exact h ▸ (paid p).property.1)⟩

def parent : (N).Site⊕(pairs×Fin 6)→(N).Site
  | .inl u=>u
  | .inr (p,_)=>(N).src (pick (p,0))

def localSlot : (N).Site⊕(pairs×Fin 6)→Fin (1+A.cap*6)
  | .inl _=>finSumFinEquiv (Sum.inl (0:Fin 1))
  | .inr (p,j)=>finSumFinEquiv (Sum.inr (finProdFinEquiv (slot (firstGrain A he p),j)))

/-- A nonempty numerical choice names the actual old site and its
unique local outgoing ordinal, including when other signed slots are empty. -/
theorem marked_slot (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (u : (N).Site) (s : Fin A.cap)
    (p : pairs) (same : p.1=home u) :
    rawTriple A native S ready names he p.1 true (paid p) 0=(A.block u).val*(2*A.cap)+s.val ↔
      (N).src (pick (p,0))=u ∧ slot (firstGrain A he p)=s:=by
  let q:=event A he p.1 true (paid p)
  have edge:(paid p).val=pick (p,0):=picked_old A he p.1 p.2 true
  have tick:=source_wire A native S ready ((addr p.1).1,q.1) q.2
  change (address A native S ready ((addr p.1).1,q.1) q.2).val=(slot ⟨(paid p).val,A.quantum_positive _ (paid p).property.1⟩).val at tick
  change q.1.val*(2*A.cap)+(address A native S ready ((addr p.1).1,q.1) q.2).val=_ ↔ _
  rw [tick];change (A.block ((N).src (paid p).val)).val*(2*A.cap)+(slot _).val=_ ↔ _
  have eqe : (⟨(paid p).val,A.quantum_positive _ (paid p).property.1⟩:DescentSharedCableNames.Stage.Positive A)=firstGrain A he p:=Subtype.ext edge
  rw [eqe,edge]
  constructor
  · intro hit
    have pos:A.pos ((N).src (pick (p,0)))=A.pos u:=by
      have orig : home ((N).src (paid p).val)=p.1:=(paid p).property.2.1
      rw [edge] at orig;rw [←source_host A he ((N).src (pick (p,0))),orig,same,source_host]
    have be : finProdFinEquiv (A.block ((N).src (pick (p,0))),((slot (firstGrain A he p)).castLE (by omega : A.cap≤2*A.cap)))=
        finProdFinEquiv (A.block u,s.castLE (by omega : A.cap≤2*A.cap)):=by
      apply Fin.ext;simpa only [finProdFinEquiv_apply_val,Fin.val_castLE,Nat.mul_comm (2*A.cap),Nat.add_comm] using hit
    have parts:=finProdFinEquiv.injective be
    exact ⟨coord (Prod.ext pos (congrArg Prod.fst parts)),Fin.ext (congrArg (fun t=>t.2.val) parts)⟩
  · rintro ⟨target,ord⟩;rw [target,ord]

variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "key"=>nativeKey N W.core home color A.cap addr same lay
local notation "venue"=>newSite N pick lay (coloredPack N W.core home color A.cap)
local notation "here"=>fun z x=>resolved A.cap profile (panel z) lay x
local notation "nearby"=>fun z v x=>Option.elim (next z v) (0,0,0) (fun y=>here y x)
local notation "heads"=>fun z x t=>actorHeads A.cap profile (panel z) lay (here z) (nearby z) x t
local notation "mask"=>DescentActorRaster.actorMask A.pos A.block
local notation "R"=>2^k
local notation "D"=>A.degree
local notation "b"=>Owners.digits R D short
local notation "signedWidth"=>2*A.cap
local notation "old"=>fun z=>Owners.render R D signedWidth short A.cap profile (Owners.register lay (panel z))

def registerRows (z : J×V) : Fin (D+1)→Owners.Register R D short :=
  Fin.cases (old z) (fun v=>(next z v).elim 0 (fun y=>old y))

def reports (z : J×V) :=Owners.report R D signedWidth short A.cap profile (Owners.register lay (panel z))
  (encode _ (D+1) (registerRows (short:=short) A native S ready rank win profile lay z))

variable {H groupsN : ℕ} (groups : J↪Fin groupsN) (hosts : V↪Fin H)
local notation "reg"=>registerRows (short:=short) A native S ready rank win profile lay
local notation "repr"=>reports (short:=short) A native S ready rank win profile lay

def tokens (slots : ℕ) (x : Fin R) (s : Fin (1+A.cap*6)) (h : Fin H) (g : Fin groupsN) : Ticket (breadth D) (2^(k+1)*slots) :=
  Publisher.ticket («D»:=D) (d:=short) (slots:=slots) (raw:=2^(k+1)*slots) (x,s)
    (Prepare.actors A groups hosts h g) (Prepare.spreadField groups hosts 0 old h g) (Prepare.spreadField groups hosts 0 repr h g)

omit [DecidableEq V] [DecidableEq J] in
private theorem spread_at {B : Type*} (blank : B) (fn : J×V→B) (z : J×V) :
    Prepare.spreadField groups hosts blank fn (hosts z.2) (groups z.1)=fn z:=by
  have ex : ∃t:J×V,groups t.1=groups z.1 ∧ hosts t.2=hosts z.2:=⟨z,rfl,rfl⟩
  rw [Prepare.spreadField,dite_eq_left ex,show ex.choose=z from Prod.ext (groups.injective ex.choose_spec.1) (hosts.injective ex.choose_spec.2)]

private theorem active (u : (N).Site) : (encode 1 R).symm (mask (A.pos u)) (A.block u)≠0:=by
  have h:∃v,A.pos v=A.pos u ∧ A.block v=A.block u:=⟨u,rfl,rfl⟩
  simp [DescentActorRaster.actorMask,DescentActorRaster.present,h]

private theorem head_eq (u : (N).Site) (s : Fin signedWidth) : actorHeads A.cap profile (panel (A.pos u)) lay (Owners.addressed (reg (A.pos u) 0))
    (fun i=>Owners.addressed (reg (A.pos u) i.succ)) (A.block u) s=heads (A.pos u) (A.block u) s:=by
  have local_ : Owners.addressed (reg (A.pos u) 0)=here (A.pos u):=funext (fun x=>Owners.addressed_read ..)
  have away (i : Fin D) : Owners.addressed (reg (A.pos u) i.succ)=nearby (A.pos u) i:=by
    funext x;cases h:next (A.pos u) i with
    | some y=>simp only [registerRows,Fin.cases_succ,h,Option.elim_some];exact Owners.addressed_read ..
    | none=>simp only [registerRows,Fin.cases_succ,h,Option.elim_none];simp [Owners.addressed,fields_zero]
  rw [local_,funext away]

include coord named fit winner df edgeOrder same in
theorem decode_born (slots : ℕ) (u : (N).Site) (s : Fin A.cap) (j : Fin 6) :
    tokens (short:=short) A native S ready rank win profile lay groups hosts slots (A.block u)
      (finSumFinEquiv (Sum.inr (finProdFinEquiv (s,j)))) (hosts (A.pos u).2) (groups (A.pos u).1)=
    (heads (A.pos u) (A.block u) (s.castLE (by omega : A.cap≤2*A.cap))).born.bind (fun q=>issue D slots (2^(k+1)*slots) (q j)):=by
  have act:=real_winner (short:=short) A native S ready names win next u (fit u)
  have yes:(panel (A.pos u)).winner (A.block u)≠0:=by intro h;rw [h] at act;have w:=winner u;simp at act;omega
  have positive : 0<b:=by
    have nonzero : 0<short:=by
      by_contra! off
      have eq0 : short=0 := Nat.eq_zero_of_le_zero off
      have room := fit u
      rw [eq0, pow_zero] at room
      have w := winner u
      omega
    exact nonzero.trans_le (le_max_left ..)
  let t:=s.castLE (by omega : A.cap≤2*A.cap)
  have hist:=issued_heads A native S ready names win next he rank coord named fit winner (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay u t
  have decoded:=from_head next (A.pos u) A.cap profile slots (2^(k+1)*slots) (panel (A.pos u)) lay (reg (A.pos u)) (A.block u) s j (mask (A.pos u)) (active A u) yes positive (fun f ok=>by
    rw [head_eq A native S ready rank win profile lay u t] at ok
    obtain ⟨_,_,trace⟩:=hist.2 f ok;exact ⟨_,trace j⟩)
  simp only [tokens,Prepare.actors,spread_at,Publisher.ticket,Equiv.symm_apply_apply,Sum.elim_inr]
  dsimp only at decoded
  rw [head_eq A native S ready rank win profile lay u t] at decoded
  exact decoded

local notation "ticketAt"=>tokens (short:=short) A native S ready rank win profile lay groups hosts
local notation "actorKey"=>key∘venue
variable (slots : ℕ)
local notation "stock"=>Descriptors slots k A.pos A.block (parent A he) (localSlot A native S ready he) actorKey hosts groups next (ticketAt slots)

include coord named fit winner df edgeOrder in
theorem original_descriptors : stock:=by
  let bornAt:=fun (u:(N).Site) (s:Fin A.cap) (j:Fin 6)=>decode_born A native S ready rank win he coord named fit winner df edgeOrder profile same lay groups hosts slots u s j
  constructor
  · rintro (u|⟨p,j⟩)
    · let w:Walk:=(0,here (A.pos u) (A.block u))
      refine ⟨w,?_,?_⟩
      · simp only [parent,localSlot,tokens,Prepare.actors,spread_at,Publisher.ticket,Equiv.symm_apply_apply,Sum.elim_inl]
        exact old_read _ _ _ _ _ _ (active A u)
      · have v:=old_location A native S ready names win next he rank coord named fit winner (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay u
        exact v
    · let e:=firstGrain A he p;let u:=(N).src e.val
      obtain ⟨f,chosen,route⟩:=parent_born A native S ready rank win he coord named fit winner df edgeOrder profile same lay e p rfl
      refine ⟨f j,?_,route j⟩
      refine (bornAt u (slot e) j).trans ?_
      change (parentHeads (short:=short) A native S ready rank win profile lay e).born.bind _=_
      rw [chosen]
      rfl
  · intro x t h g missing
    by_cases actor : ∃u:(N).Site,A.block u=x ∧ hosts (A.pos u).2=h ∧ groups (A.pos u).1=g
    · obtain ⟨u,rfl,rfl,rfl⟩:=actor
      generalize ht:(finSumFinEquiv.symm t : Fin 1⊕Fin (A.cap*6))=tag
      cases tag with
      | inl o=>
        have pos:t=finSumFinEquiv (Sum.inl (0:Fin 1)):=by
          have v:finSumFinEquiv.symm t=Sum.inl (0:Fin 1):=ht.trans (congrArg Sum.inl (Subsingleton.elim o 0))
          exact (finSumFinEquiv.apply_symm_apply t).symm.trans (congrArg finSumFinEquiv v)
        exact (missing ⟨.inl u,rfl,pos.symm,rfl,rfl⟩).elim
      | inr q=>
        let z:Fin A.cap×Fin 6:=finProdFinEquiv.symm q
        have pos:t=finSumFinEquiv (Sum.inr (finProdFinEquiv z)):=by
          apply finSumFinEquiv.symm_apply_eq.mp
          simpa only [z,Equiv.apply_symm_apply] using ht
        rw [pos,bornAt u z.1 z.2]
        have src:=issued_heads A native S ready names win next he rank coord named fit winner (rotor_sorted A rank) (rotor_routes A native S ready rank) df edgeOrder profile same lay u (z.1.castLE (by omega : A.cap≤2*A.cap))
        have empty:=(src.1).2 (by
          rintro ⟨e,hit⟩;let p:pairs:=⟨home u,e⟩
          obtain ⟨s,f⟩:=(marked_slot A native S ready rank he coord u z.1 p rfl).1 hit
          exact missing ⟨.inr (p,z.2),congrArg A.block s,by simp only [localSlot,f,←pos],congrArg (fun v=>hosts (A.pos v).2) s,congrArg (fun v=>groups (A.pos v).1) s⟩)
        rw [empty];rfl
    · have absent:(encode 1 R).symm (Prepare.actors A groups hosts h g) x=0:=by
        unfold Prepare.actors Prepare.spreadField;split
        · rename_i h_;simp only [DescentActorRaster.actorMask,Equiv.symm_apply_apply,DescentActorRaster.present]
          apply ite_eq_right;rintro ⟨u,hu,bu⟩;apply actor;exact ⟨u,bu,(congrArg (fun z:J×V=>hosts z.2) hu).trans h_.choose_spec.2,(congrArg (fun z:J×V=>groups z.1) hu).trans h_.choose_spec.1⟩
        · simp only [fields_zero]
      unfold tokens Publisher.ticket
      cases tag:finSumFinEquiv.symm t with
      | inl j=>exact old_missing _ _ _ absent
      | inr p=>exact new_missing _ _ _ _ _ absent

end Stage
end
end Hierarchy.DescentScalarVenueMask

end OAI
