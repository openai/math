import OAI.Hierarchy.DescentDatedSignedHeader
import OAI.Hierarchy.DescentDatedSignedReturnRecords
import OAI.Hierarchy.DescentDatedSignedMapReads

namespace OAI
/-! The receiver gate recovers actual query and comparison operands on all
three axes, including holes in a partially occupied packed group. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSixParty.Chronology DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinarySignedRanks
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U J E X T V:Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K b M H groups blocks oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (names:Stage.Host J U k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))
  (home:Fin blocks→Fin H→Fin groups→Option (Stage.Host J U k))
local notation "e₀" => (⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent)
local notation "census" => Incidence.of_measured C R symm Z orders
local notation "qr" => queryRaw C R symm Z shelf small orders home
local notation "ar" => itemRaw C R symm Z shelf small orders home
local notation "zhead" => DescentOrdinarySignedWindows.header A native S ready names C marked census home
local notation "target" => DescentOrdinarySignedWindows.target A native S ready names home

local notation "R₀" => Measured.roster C R symm Z
local notation "R₁" => Fused.fetched C R Z shelf small
local notation "flag" => signedControls C marked R symm Z home
local notation "reach" => Gather.reaching R
local notation "P" => breadth D

theorem resident_address {α:Type*} {n:ℕ} (a:α↪Fin n) {j:Fin n} {e:α}
    (read:resident a j=some e):a e=j:=by
  unfold resident at read
  split at read
  next has=>exact (Option.some.inj read) ▸ has.choose_spec
  next=>contradiction

def itemOf (s:SignedExtent) (c:s.Consumer):Option (Fin s.candidates):=Fin.cases none some c.2.2

private theorem item_choice {n:ℕ} (fallback:Fin n) (i:Fin (n+1)):
    Fin.cases fallback id i=(Fin.cases none some i : Option (Fin n)).getD fallback:=by
  induction i using Fin.cases with
  | zero=>rfl
  | succ i=>rfl

theorem source_slot (s:SignedExtent) (c:s.Consumer) (r:Fin s.reach):
    (s.sourceAt c r).2=(s.itemOf c).getD (finProdFinEquiv (r,(s.priorSlot c).2)):=item_choice _ _

theorem local_slot (s:SignedExtent) (c:s.Consumer):
    (s.socketAt c).2=(s.itemOf c).getD c.2.1:=item_choice _ _

variable {A native}
def wanted (c:(e₀).Consumer) (v:Fin H) (g:Fin groups):=
  (request C census home c.1.1 c.1.2 c.2.1 v g).bind
    (fun pos=>R₁ pos.1 (((e₀).itemOf c).getD ((census).addr pos.1 pos.2)))

variable (I:(⟨blocks,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent).Input) (base:ℕ) (m:Memory w)
local notation "sheet"=>(e₀).installed I base m
local notation "gt"=>gateTable ((e₀).gateStart base) b M
local notation "localCell" c:arg v:arg g:arg=>Fused.cell C R Z shelf small (home (c).1.1) ((e₀).socketAt c).2 v g
local notation "expected" =>wanted C R symm Z shelf small orders home
local notation "sourceLocal" e => (⟨(e).val,(e).property.1,Or.inl rfl⟩:Local C (C.src (e).val))

variable (A) in
/-- The original directed donor port and both representations of its
source are measured on the prior geometry, independent of rank fields. -/
structure RouteWitness
    (v:(e₀).RouteDigits) (I:(e₀).Input)
    (home:Fin blocks→Fin H→Fin groups→Option (Stage.Host J U k)):Prop where
  receiver:∀x h g t,home x h g=some t→(e₀).rack I.hostPitch h=some (Z.venue t).1
  placed:∀x h g t,home x h g=some t→∀e:Local C t,
    (((e₀).lifted I.hostPitch (Z.venue (C.src e.val)).2 (Z.venue (C.src e.val)).1).bind
      (fun u=>home x u g))=some (C.src e.val)
  donor:∀h (e:Local C h),Z.loc (Z.raw h e)=Z.loc (Z.raw (C.src e.val) (sourceLocal e))
  forward:∀x h g t,home x h g=some t→∀e:Local C t,
    let u:=C.src e.val;let orig:=Z.loc (Z.raw t e)
    v.forward x orig.2 orig.1 g=Packed.token (some (Z.read u (sourceLocal e)).src.path)
  low:∀x h g t,home x h g=some t→∀e:Local C t,
    let orig:=Z.loc (Z.raw t e)
    (v.low x orig.2 orig.1 g).val=(Z.venue (C.src e.val)).2.val
  back:∀x o h g,v.back x o h g=SourceReturn.Query.packedRoute R h (Packed.readToken P (v.forward x o h g))

def routedValue (v:(e₀).RouteDigits) (c:(e₀).Consumer) (f:Fin 11) (h:Fin H) (g:Fin groups):Cell b:=
  let source:=fun l r old j=>
    ((e₀).lifted I.hostPitch l old).elim 0 (fun u=>
      Fused.columns (Fused.cell C R Z shelf small (home c.1.1) ((e₀).sourceAt c r).2 u j) f)
  ((e₀).selected I R ((e₀).priorSlot c).1 h).elim 0 (fun old=>
    SourceReturn.RAM.output reach source (v.choice c.1.1 ((e₀).priorSlot c).2) old g)

theorem routed_live (v:(e₀).RouteDigits) (geo:RouteWitness A C R Z v I home)
    (c:(e₀).Consumer) (f:Fin 11) (h:Fin H) (g:Fin groups) (t:Stage.Host J U k) (e:Local C t)
    (pos:home c.1.1 h g=some t) (slot:(R₀).address t e=c.2.1):
    routedValue C R Z shelf small home I v c f h g=
      Fused.columns (R₁ (C.src e.val) (((e₀).itemOf c).getD ((R₀).address _ (sourceLocal e)))) f:=by
  let u:=C.src e.val;let ee:Local C u:=sourceLocal e
  let p:Fin P:=(Z.read u ee).src.path
  let prior:=Z.loc (Z.raw u ee)
  let key:Fin Q→Fin oldH→Fin groups→Option (Stage.Host J U k):=fun l old gg=>
    ((e₀).lifted I.hostPitch l old).bind (fun v'=>home c.1.1 v' gg)
  let field:=fun t' s=>Fused.columns (R₁ t' s) f
  let oracle:=fun old j=>v.choice c.1.1 prior.2 old j
  have same:=geo.donor t e
  have parts:(e₀).priorSlot c=(Measured.visit C R symm Z t e,prior.2):=by
    unfold priorSlot;rw [←slot];change finProdFinEquiv.symm (finProdFinEquiv (_,_))=_
    rw [Equiv.symm_apply_apply];exact congrArg (Prod.mk _) (congrArg Prod.snd same)
  have visit:=Resident.visit_read C t (fun v'=>(Z.venue v').1) Z.loc (Z.raw t) reach (Measured.near C R symm Z t) e
  have seen:Gather.select reach (Z.venue t).1 ((e₀).priorSlot c).1=some (Z.old u ee):=by
    rw [parts];exact visit.trans (congrArg (some ∘ Prod.fst) same)
  have near:reach (Z.old u ee) p=some (Z.venue u).1:=(Z.reached u ee).src
  have fw:v.forward c.1.1 prior.2 prior.1 g=Packed.token (some p):=by simpa only [same] using geo.forward _ _ _ _ pos e
  have low:(v.low c.1.1 prior.2 prior.1 g).val=(Z.venue u).2.val:=by simpa only [same] using geo.low _ _ _ _ pos e
  have back:=geo.back c.1.1 prior.2 prior.1 g
  rw [fw,Packed.token_back] at back
  have issued:Packed.token (oracle prior.1 g)=SourceReturn.Query.finish P Q
      (SourceReturn.Query.forward P Q (Packed.token (some p)) (v.low c.1.1 prior.2 prior.1 g))
      (SourceReturn.Query.packedRoute R prior.1 (some p)):=by
    exact (v.measures_choice c.1.1 prior.2 prior.1 g).symm.trans (by rw [fw,back]; rfl)
  have lemma':=SourceReturn.received_raw C R symm Z key field t u ee g p ((e₀).priorSlot c).1
    seen near (geo.placed _ _ _ _ pos e) oracle _ low issued ((e₀).itemOf c)
  let src:=fun l r old j=>((e₀).lifted I.hostPitch l old).elim 0 (fun fresh=>
    Fused.columns (Fused.cell C R Z shelf small (home c.1.1) ((e₀).sourceAt c r).2 fresh j) f)
  have eqn:src=SourceReturn.rawShelf key field prior.2 ((e₀).itemOf c):=by
    funext l r old j
    cases found:(e₀).lifted I.hostPitch l old with
    | none=>simp [src,SourceReturn.rawShelf,key,found]
    | some fresh=>
      cases inside:home c.1.1 fresh j with
      | none=>simp [src,SourceReturn.rawShelf,key,found,Fused.cell,inside,Fused.columns]
      | some t'=>simp [src,SourceReturn.rawShelf,key,field,source_slot,Fused.cell,found,inside,parts]; rfl
  change (((e₀).rack I.hostPitch h).bind _).elim 0 (fun old=>SourceReturn.RAM.output reach src _ old g)=_
  rw [geo.receiver _ _ _ _ pos,Option.bind_some,eqn]
  simp only [parts,SourceReturn.donated,oracle,field] at lemma' ⊢
  exact lemma'

theorem operand_gate (v:(e₀).RouteDigits) (geo:RouteWitness A C R Z v I home)
    (fits:(e₀).Fits I base w) (space:(e₀).roof base<2^w) (c:(e₀).Consumer) (f:Fin 11)
    (flags:Source ((e₀).flags I base (c.1.1,c.2.1)) (flag c.1.1 c.2.1) M sheet)
    (localRead:Source ((e₀).rawField base ((e₀).socketAt c) f) (fun h g=>Fused.columns (localCell c h g) f) M sheet)
    (remoteRead:c.1.2.val=2→Source ((e₀).remoteWord I base c f) (routedValue C R Z shelf small home I v c f) M sheet)
    (fit:DescentPackedZip.Fits gt ((e₀).flags I base (c.1.1,c.2.1))
      (if c.1.2.val=2 then (e₀).remoteWord I base c f else (e₀).rawField base ((e₀).socketAt c) f)
      (1*4) b M ((e₀).tailStart base) w):
    Source ((e₀).operand I base c f) (fun h g=>Fused.columns (expected c h g) f) M sheet:=by
  let atom:=if c.1.2.val=2 then routedValue C R Z shelf small home I v c f else fun h g=>Fused.columns (localCell c h g) f
  have body:Source (if c.1.2.val=2 then (e₀).remoteWord I base c f else (e₀).rawField base ((e₀).socketAt c) f) atom M sheet:=by
    by_cases remote:c.1.2.val=2
    · simpa only [atom,ite_eq_left remote] using remoteRead remote
    · simpa only [atom,ite_eq_right remote] using localRead
  have code:=read_data gt _ _ _ fit keepField (by rfl) sheet ((e₀).static_gate I base m fits space) _ _ flags body
  suffices agree:(fun h g=>keepField (flag c.1.1 c.2.1 h g) (atom h g))=(fun h g=>Fused.columns (expected c h g) f) by
    simpa only [operand,agree] using code
  funext h g
  have live:=signed_flags_active C marked R symm Z home c.1.1 c.2.1 h g
  cases pos:home c.1.1 h g with
  | none=>
    have off:(flag c.1.1 c.2.1 h g).val=0:=by simpa [pos] using live
    simp [keepField,off,wanted,request,pos,Fused.columns]
  | some t=>
    cases hit:resident ((R₀).address t) c.2.1 with
    | none=>
      have off:(flag c.1.1 c.2.1 h g).val=0:=by simpa [pos,hit] using live
      simp [keepField,off,wanted,request,pos,Incidence.of_measured,hit,Fused.columns]
    | some e=>
      have active:(flag c.1.1 c.2.1 h g).val≠0:=live.mpr (by simp [pos,hit])
      have slot:=resident_address _ hit
      rw [keepField,ite_eq_right active]
      by_cases remote:c.1.2.val=2
      · rw [show atom h g=routedValue C R Z shelf small home I v c f h g by simp [atom,remote],
          routed_live C R symm Z shelf small home I v geo c f h g t e pos slot]
        simp [wanted,request,point,pos,remote,Incidence.of_measured,hit]
      · have index:((e₀).socketAt c).2=((e₀).itemOf c).getD ((R₀).address t e):=by
          rw [slot];exact local_slot _ _
        simp [atom,remote,Fused.cell,index,wanted,request,point,pos,Incidence.of_measured,hit]

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
