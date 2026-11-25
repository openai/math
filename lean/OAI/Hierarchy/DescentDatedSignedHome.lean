import OAI.Hierarchy.DescentDatedSignedGate
import OAI.Hierarchy.DescentDatedVenueSources

namespace OAI
/-! The ordinary return uses the same numeric host and block tape as
the next dated stage's published signed panel. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSixParty DescentSixParty.Chronology DescentSharedCableNames DescentParallelBase DescentParallelBase.ParentFilter
open DescentOrdinarySignedParents DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinarySignedRanks
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F Pin U J E X T V:Type} [Field F] [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype E] [Fintype X] [Fintype T]
  {d k i D Q O K b M H groups oldH w:ℕ} {bits:Pin→ℕ} {W:MarkedWorld F d Pin bits}
  {G:PoweredGadget F} {price ε:ℝ}
variable (A:GroupStage W G price ε J U k) (native:W.graph.Edge↪ℕ) (S:DescentCompiler.AtomSchedule)
  (ready:A.StateBounds S i) (names:Stage.Host J U k↪ℕ) (C:Blocks (Stage.source A native) E) (marked:E→Prop)
  (R:Fin oldH→Fin D→Option (Fin oldH)) (symm:∀v u p,R v p=some u→∃z,R u z=some v)
  (Z:Measured C R X T V Q O K A.cap) (shelf:Measured.Shelf C R Z)
  (small:∀h path x (s:ParentFilter.Source (breadth D) Q K A.cap) f,Machine.fields R (Z.venue h) path (Z.loc x).1 s f<2^b)
  (orders:∀h (e f:Local C h),Incidence.srcKey C R symm Z h e<Incidence.srcKey C R symm Z h f ↔ Z.site (Z.src (Z.head h e))<Z.site (Z.src (Z.head h f)))

local notation "ext₀"=> (⟨2^k,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent)
local notation "Prep" => DescentPacking.PackedMatch.Local.Stage.Prepare.spreadField
variable (group:J↪Fin groups) (host:U↪Fin H)
def wholeHost (x:Fin (2^k)) (h:Fin H) (g:Fin groups):Option (Stage.Host J U k):=
  Prep group host none (fun u=>some (u,x)) h g

omit [DecidableEq J] [DecidableEq U] in
theorem wholeHost_iff (x:Fin (2^k)) (h:Fin H) (g:Fin groups) (u:Stage.Host J U k):
    wholeHost group host x h g=some u ↔ group u.1.1=g ∧ host u.1.2=h ∧ u.2=x:=by
  unfold wholeHost DescentPacking.PackedMatch.Local.Stage.Prepare.spreadField
  split
  next live=>
    constructor
    · intro eqn;cases Option.some.inj eqn;exact ⟨live.choose_spec.1,live.choose_spec.2,rfl⟩
    · rintro ⟨g₀,h₀,x₀⟩
      have eqn:live.choose=u.1:=Prod.ext (group.injective (live.choose_spec.1.trans g₀.symm)) (host.injective (live.choose_spec.2.trans h₀.symm))
      cases u;cases x₀;rw [eqn]
  next missing=>
    constructor
    · intro absurd;contradiction
    · rintro ⟨a,c,_⟩;exact False.elim (missing ⟨u.1,a,c⟩)

omit [Fintype E] in
theorem shared_lane (e:E) (pos:0<C.count e):
    (C.src e).1.1=(C.dst e).1.1 ∧ (C.src e).2=(C.dst e).2:=by
  let i:Fin (C.count e):=⟨0,pos⟩
  let grain:=((Stage.stream A native).symm (C.order ⟨e,i⟩)).1
  rw [←C.atSource e i,←C.atTarget e i]
  change (A.pos (W.graph.src grain)).1=(A.pos (W.graph.dst grain)).1 ∧ A.block (W.graph.src grain)=A.block (W.graph.dst grain)
  obtain ⟨v,_,truth⟩:=Finset.mem_map.mp (A.peers grain).1
  have groups := congrArg Prod.fst truth
  exact ⟨groups,A.same grain⟩

omit [Fintype E] in
theorem source_lane (h:Stage.Host J U k) (e:Local C h):
    (C.src e.val).1.1=h.1.1 ∧ (C.src e.val).2=h.2:=by
  rcases e.property.2 with src|dst
  · rw [src];exact ⟨rfl,rfl⟩
  · obtain ⟨groupAt, blockAt⟩ := shared_lane A native C e.val e.property.1
    exact ⟨groupAt.trans (congrArg (fun u => u.1.1) dst), blockAt.trans (congrArg Prod.snd dst)⟩

local notation "home" =>wholeHost group host
variable (I:(⟨2^k,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent).Input) (v:(⟨2^k,oldH,H,groups,M,D,O,Q,K,A.cap,b⟩:SignedExtent).RouteDigits)
local notation "sourceLocal" e=>(⟨(e).val,(e).property.1,Or.inl rfl⟩:Local C (C.src (e).val))

omit [Fintype E] in
/-- Immutable host names are enumerated with the actual compact physical
pitch; both terminal sides have the same group and block by their real cable. -/
theorem route_of_hosts
    (physical:∀u, (host u.1.2).val=(Z.venue u).1.val*I.hostPitch+(Z.venue u).2.val)
    (lowFits:∀u,(Z.venue u).2.val<I.hostPitch)
    (raw:∀h (e:Local C h),Z.loc (Z.raw h e)=Z.loc (Z.raw (C.src e.val) (sourceLocal e)))
    (forward:∀x h g t,home x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e);v.forward x a.2 a.1 g=Packed.token (some (Z.read (C.src e.val) (sourceLocal e)).src.path))
    (low:∀x h g t,home x h g=some t→∀e:Local C t,
      let a:=Z.loc (Z.raw t e);(v.low x a.2 a.1 g).val=(Z.venue (C.src e.val)).2.val)
    (back:∀x o u g,v.back x o u g=SourceReturn.Query.packedRoute R u (Packed.readToken _ (v.forward x o u g))):
    RouteWitness A C R Z v I home:=by
  refine ⟨?_,?_,raw,forward,low,back⟩
  · intro x h g t at_
    have used:=(wholeHost_iff group host _ _ _ _).mp at_
    have pitch:0<I.hostPitch:=Nat.zero_lt_of_lt (lowFits t)
    have div_:h.val/I.hostPitch=(Z.venue t).1.val:=by
      rw [←used.2.1,physical t,Nat.mul_comm _ I.hostPitch,Nat.mul_add_div pitch,Nat.div_eq_of_lt (lowFits t),Nat.add_zero]
    unfold rack;rw [dite_eq_left ⟨pitch,div_ ▸ (Z.venue t).1.isLt⟩]
    exact congrArg some (Fin.ext div_)
  · intro x h g t at_ e
    let u:=C.src e.val
    have used:=(wholeHost_iff group host _ _ _ _).mp at_
    have same:=source_lane A native C t e
    have place:u.1.1=t.1.1 ∧ u.2=t.2:=same
    have lift_:(ext₀).lifted I.hostPitch (Z.venue u).2 (Z.venue u).1=some (host u.1.2):=by
      rw [lifted,dite_eq_left ⟨lowFits u,(physical u) ▸ (host u.1.2).isLt⟩]
      exact congrArg some (Fin.ext (physical u).symm)
    rw [lift_,Option.bind_some]
    exact (wholeHost_iff group host _ _ _ _).mpr ⟨(congrArg group place.1).trans used.1,rfl,place.2.trans used.2.2⟩

theorem signed_target (groups':J↪Fin groups) (rank:Stage.Host J U k↪ℕ) (x:Fin (2^k)) (j:Fin (2*A.cap)) (h:Fin H) (g:Fin groups):
    DescentOrdinarySignedWindows.target A native S ready rank (wholeHost groups' host) x j h g=
      Prep groups' host none (fun u=>Stage.signedPanel A native S ready rank (u,x) j) h g:=by
  unfold DescentOrdinarySignedWindows.target wholeHost DescentPacking.PackedMatch.Local.Stage.Prepare.spreadField
  split <;> rfl

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
