import OAI.Hierarchy.DescentDatedOperandHeaderPair
import OAI.Hierarchy.DescentDatedMouthPersistence

namespace OAI
/-! # Original W selector ordinals and the three collected newborn fields on the actual two-prefix RAM -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

namespace HeaderWords
def atShape {H G H' G' t : ℕ} (host : H'=H) (group : G'=G) (x : Fin H→Fin G→Cell t) :
    Fin H'→Fin G'→Cell t :=fun h g=>x (h.cast host) (g.cast group)

theorem source {w H G M H' G' M' t : ℕ} (host : H'=H) (group : G'=G) (lane : M'=M)
    (x : Fin H→Fin G→Cell t) (e : Expr) (m : Memory w) (actual : Source e x M m) :
    Source e (atShape host group x) M' m :=by cases host;cases group;cases lane;exact actual

theorem reads {w H G M H' G' M' t : ℕ} (host : H'=H) (group : G'=G) (lane : M'=M)
    (x : Fin H→Fin G→Cell t) (B : Bank) (m : Memory w) (actual : Reads B x M m) :
    Reads B (atShape host group x) M' m :=by cases host;cases group;cases lane;exact actual
end HeaderWords

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "res₀" => v.resolver
local notation "vec₀" => v.vector
local notation "born₀" => v.bornBook
local notation "ref₀" => v.reference
local notation "geom₀" => v.ticketReadGeometry
abbrev SourceReferences :=References v.vector v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
abbrev SourceMasks :=Fin v.vector.lows→Refs v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
abbrev OriginalDonors (a nb mb : ℕ) :=
  Fin v.vector.lows→DescentOrdinaryAtomFieldRAM.ScalarOperand.Values v.reference.degree v.reference.k
    v.reference.oldNodes v.reference.capacity v.vector.hosts (v.vector.groups*v.vector.radix) a nb mb

def originHeaderValue {a nb mb} (shape : v.VectorShape) (donors : v.OriginalDonors a nb mb)
    (j : Fin (res₀).jobs) (f : Fin 6) : DescentDatedOperandReadPipeline.Values geom₀ v.operandShortBits :=
  let (block,node,_):=(res₀).index.symm j
  let ledger:=DescentScalarBookReshape.book
    (fun l h g=>selection v.originCandidates (res₀).nodes v.originBits (marked (donors l) h g)) (block.cast shape.blocks)
  HeaderWords.atShape shape.hosts shape.groups
    (fun h g=>DescentOrdinaryOriginPorts.readLaw v.originChart v.operandShortBits node f (ledger h g))

variable (floor : ℕ) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
local notation "mouth₀" => v.mouthChart mat.newBlocks
local notation "work₀" => (vec₀).lanes*(vec₀).radix
local notation "vecAt" => v.vectorStart floor
local notation "portsAt" => v.originPortEnd floor
local notation "mouthAt₀" => v.originMouthEnd floor

def mouthHeaderValue {nb mb} (donors : Fin (born₀).args→Fin (vec₀).lows→(mouth₀).Val nb mb)
    (chip : Fin (born₀).hosts→Fin (born₀).groups→Cell (born₀).chipBits)
    (home : (born₀).hosts=(vec₀).hosts) (group : (born₀).groups=(vec₀).groups*(vec₀).radix)
    (j : Fin (res₀).jobs) (f : Fin 3) :
    DescentDatedOperandReadPipeline.Values geom₀ ((born₀).bits*(res₀).nodes) :=
  let (block,_,arg):=(res₀).index.symm j
  let id:=finProdFinEquiv (arg.cast (shape.operands.trans mat.newArgs.symm),f)
  let vals:=DescentScalarBookReshape.book
    (fun l h g=>((mouth₀).vals donors chip id l).book (res₀).nodes h (g.cast group.symm)) (block.cast shape.blocks)
  HeaderWords.atShape (shape.hosts.trans (congrArg (·*(vec₀).lows) home.symm)) shape.groups vals

set_option maxHeartbeats 1000000 in
theorem origin_header_six {w a nb mb} (refs : v.SourceReferences) (orig : v.SourceMasks)
    (donors : v.OriginalDonors a nb mb) (m : Memory w) (good : refs.Room w vecAt)
    (obs : ∀l,Measured (orig l) (donors l) (res₀).nodes work₀ vecAt m)
    (space : portsAt<2^w) (j : Fin (res₀).jobs) (f : Fin 6) :
    let after:=(v.originPrefix floor v.operandShortBits w orig).image ((refs.phase w vecAt).image m)
    Held geom₀ portsAt after (v.originAt floor v.operandShortBits shape j f) (v.originHeaderValue shape donors j f) :=by
  intro after_
  obtain ⟨⟨block,node,arg⟩,rfl⟩ := (res₀).index.surjective j
  simp only [originAt,originHeaderValue,Equiv.symm_apply_apply]
  let ledger := DescentScalarBookReshape.book (fun low h g =>
    selection v.originCandidates (res₀).nodes v.originBits (marked (donors low) h g)) (block.cast shape.blocks)
  let value := fun h g => DescentOrdinaryOriginPorts.readLaw v.originChart v.operandShortBits node f (ledger h g)
  let port := v.originPort floor v.operandShortBits (block.cast shape.blocks) node f
  have stamped := v.gathered_origin_ports floor v.operandShortBits refs orig donors m good obs space
    (block.cast shape.blocks) node f
  exact ⟨stamped.1, HeaderWords.source shape.hosts shape.groups shape.lanes value port after_ stamped.2⟩

theorem mouth_header_three {w a nb mb nb' mb'} (refs : v.SourceReferences) (orig : v.SourceMasks)
    (original : v.OriginalDonors a nb mb)
    (donors : Fin (born₀).args→Fin (vec₀).lows→(mouth₀).Val nb' mb')
    (chip : Fin (born₀).hosts→Fin (born₀).groups→Cell (born₀).chipBits) (m : Memory w)
    (good : refs.Room w vecAt) (obs : ∀l,Measured (orig l) (original l) (res₀).nodes work₀ vecAt m)
    (witness : ∀a l,Measured (v.mouthRef A mat a l) (donors a l) (res₀).nodes work₀ vecAt m)
    (input : (A.chipBank v floor).Fits w vecAt) (span : (born₀).rows≤(A.chipBank v floor).size)
    (read : Reads (A.chipBank v floor) chip (born₀).lanes m)
    (home : (born₀).hosts=(vec₀).hosts) (lane : (born₀).lanes=work₀)
    (group : (born₀).groups=(vec₀).groups*(vec₀).radix) (space : mouthAt₀<2^w)
    (j : Fin (res₀).jobs) (f : Fin 3) :
    let after:=(v.originAndMouth floor w A mat v.operandShortBits orig).image ((refs.phase w vecAt).image m)
    let B:=v.mouthBankAt floor A mat shape j f
    B.Fits w mouthAt₀ ∧ (res₀).rows≤B.size ∧
      Reads B (v.mouthHeaderValue floor A mat shape donors chip home group j f) (res₀).lanes after :=by
  intro after_ B
  let arg:=((res₀).index.symm j).2.2.cast (shape.operands.trans mat.newArgs.symm)
  let block:=((res₀).index.symm j).1.cast shape.blocks
  have seen:=v.gathered_mouth floor w A mat v.operandShortBits refs orig donors chip m good witness input span read
    (fun l=>(read_mask (orig l) (original l) (obs l)).1) lane group space arg f block
  have eqn:=v.mouth_translated floor mat.newBlocks
  have bounds:=(mouth₀).placed portsAt arg f block (eqn.symm ▸ space)
  have h:=(shape.hosts.trans (congrArg (·*(vec₀).lows) home.symm))
  have nrows : (res₀).rows=(mouth₀).nextRows :=by
    change (res₀).hosts*chunks (res₀).groups (res₀).lanes=((born₀).hosts*(vec₀).lows)*chunks (vec₀).groups (vec₀).lanes
    rw [h,shape.groups,shape.lanes]
  refine ⟨?_,nrows.symm ▸ bounds.2,HeaderWords.reads h shape.groups shape.lanes _ B after_ seen⟩
  change ((mouth₀).returned portsAt arg f block).Fits w mouthAt₀
  rw [←eqn]
  exact bounds.1

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
