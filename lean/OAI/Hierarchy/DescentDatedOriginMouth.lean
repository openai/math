import OAI.Hierarchy.DescentDatedWOrigin
import OAI.Hierarchy.DescentOrdinaryAfterSigned
import OAI.Hierarchy.DescentOrdinaryMouthMeasured
import OAI.Hierarchy.DescentFundedOriginReturn

namespace OAI
/-! The three actual newborn operand coordinates in the ordinary resolver's preparation. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryMouthReturn DescentOrdinaryBorn DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentPackedColony DescentSIMDLookup DescentOrdinaryReferenceInputs DescentOperandVectorArena
open DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

def mouthChart (blocks : v.bornBook.blocks=2^v.reference.k) : DescentOrdinaryMouthReturn.Layout :=
  ⟨v.bornBook,v.reference.degree,v.reference.k,v.reference.oldNodes,v.resolver.nodes,v.vector.lows,
    v.vector.groups,v.vector.radix,v.vector.lanes,blocks⟩

/-- The reserved aperture depends only on the public dimensions, including when the book is empty. -/
def originMouthWords :=
  let B:=v.bornBook
  let V:=v.vector
  let n:=B.args*3
  let a:=B.bits*v.resolver.nodes
  let raw:=RolePorts.endAddress B 0+2^Nat.clog 2 (n*DescentVectorBookReshape.sourceWords B.hosts V.lows V.groups V.lanes)
  DescentVectorBookReshape.output raw n B.hosts V.lows V.groups V.radix a V.lanes+
    n*DescentVectorBookReshape.rows B.hosts V.lows V.groups V.radix V.lanes+
    2^Nat.clog 2 ((B.hosts*V.lows)*chunks V.groups V.lanes)
def originMouthEnd (floor : ℕ) := v.originPortEnd floor+v.originMouthWords

theorem mouth_translated (floor : ℕ) (blocks : v.bornBook.blocks=2^v.reference.k) :
    (v.mouthChart blocks).endAddress (v.originPortEnd floor)=v.originMouthEnd floor :=by
  simp only [mouthChart,originMouthEnd,originMouthWords,DescentOrdinaryMouthReturn.Layout.endAddress,
    DescentOrdinaryMouthReturn.Layout.nextRows,DescentOrdinaryMouthReturn.Layout.out,DescentOrdinaryMouthReturn.Layout.transpose,
    DescentOrdinaryMouthReturn.Layout.raw,DescentOrdinaryMouthReturn.Layout.pages,DescentOrdinaryMouthReturn.Layout.bits,
    DescentOrdinaryMouthReturn.Layout.start,RolePorts.endAddress,RolePorts.output,Bank.size,DescentVectorBookReshape.output,
    Nat.zero_add,Nat.add_assoc]

private def castMouthRef {D k K c d : ℕ} (h : c=d) (r : Refs D k K c) : Refs D k K d := h ▸ r

private theorem castMouthWork {D k K c d : ℕ} (h : c=d) (r : Refs D k K c) :
    (castMouthRef h r).want.work+(castMouthRef h r).addr.work+(castMouthRef h r).counts.work=
      r.want.work+r.addr.work+r.counts.work := by subst d;rfl

def mouthRef {floor} (A : v.ArgumentEntry) (match_ : A.Match v floor) (arg : Fin v.bornBook.args) :
    Fin v.vector.lows→(v.mouthChart match_.newBlocks).Ref :=
  fun low=>castMouthRef match_.newCap.symm ((A.directory v floor match_).refs
    (finProdFinEquiv ((0:Fin 7),arg.cast match_.newArgs)) low)

private theorem castMouthExpr {D k K c d : ℕ} (cap : c=d) (r : Refs D k K c) (H : ℕ) :
    (castMouthRef cap r).expr H=r.expr H :=by cases cap;rfl

theorem mouthRef_expr {floor} (A : v.ArgumentEntry) (match_ : A.Match v floor)
    (arg : Fin v.bornBook.args) (low : Fin v.vector.lows) (H : ℕ) :
    ((v.mouthRef A match_ arg low).expr H)=
      (((A.directory v floor match_).refs (finProdFinEquiv ((0:Fin 7),arg.cast match_.newArgs)) low).expr H) :=
  castMouthExpr _ _ _

theorem mouth_sources {floor} (A : v.ArgumentEntry) (match_ : A.Match v floor) (arg : Fin v.bornBook.args) (l : Fin v.vector.lows) :
    let r:=v.mouthRef A match_ arg l
    r.want.work+r.addr.work+r.counts.work≤26 :=by
  let directory := A.directory v floor match_
  let page := finProdFinEquiv ((0 : Fin 7), arg.cast match_.newArgs)
  exact (castMouthWork match_.newCap.symm (directory.refs page l)).le.trans (origin_sources directory page l)

/-- The W-reference prefix has already run when this phase starts. -/
def originPrefixMouth (floor w : ℕ) (A : v.ArgumentEntry) (match_ : A.Match v floor) : NativePhase w :=
  (v.mouthChart match_.newBlocks).phase (A.chipBank v floor) (v.originPortEnd floor) w (v.mouthRef A match_)

def originMouthBank (floor : ℕ) (blocks : v.bornBook.blocks=2^v.reference.k) (arg : Fin v.bornBook.args)
    (field : Fin 3) (b : Fin v.vector.radix) : Bank :=
  (v.mouthChart blocks).returned (v.originPortEnd floor) arg field b

variable {w : ℕ} (floor : ℕ) (A : v.ArgumentEntry) (match_ : A.Match v floor)
set_option quotPrecheck false in
local notation "Lₘ" => v.mouthChart match_.newBlocks
set_option quotPrecheck false in
local notation "Cₘ" => v.mouthRef A match_

theorem originPrefixMouth_any (m : Memory w) (old : (A.chipBank v floor).Fits w (v.originPortEnd floor))
    (same : v.bornBook.groups=v.vector.groups*v.vector.radix) (hm : 0<v.vector.lanes) (hr : 0<v.vector.radix)
    (early : ∀a l,((Cₘ a l).expr v.bornBook.hosts).inputEnd≤v.originPortEnd floor) (space : v.originMouthEnd floor<2^w) :
    (v.originPrefixMouth floor w A match_).Runs m ∧
    ∀i,i<v.originPortEnd floor ∨ v.originMouthEnd floor≤ i → (v.originPrefixMouth floor w A match_).image m i=m i :=by
  rw [←v.mouth_translated floor match_.newBlocks] at space ⊢
  apply (Lₘ).any (A.chipBank v floor) (v.originPortEnd floor) Cₘ m old same hm hr _ space
  have bounds:=(Lₘ).bounds (v.originPortEnd floor)
  exact (Lₘ).early (v.originPortEnd floor) Cₘ early (bounds.2.1.trans_lt (bounds.2.2.1.trans_lt
    ((Nat.le_add_right ..).trans_lt (bounds.2.2.2.trans_lt space))))

theorem originPrefixMouth_read {nb mb} (m : Memory w)
    (V : Fin v.bornBook.args→Fin v.vector.lows→(Lₘ).Val nb mb)
    (chip : Fin v.bornBook.hosts→Fin v.bornBook.groups→Cell v.bornBook.chipBits)
    (prior : ∀a l,Measured (Cₘ a l) (V a l) v.resolver.nodes (v.vector.lanes*v.vector.radix) (v.originPortEnd floor) m)
    (early : (A.chipBank v floor).Fits w (v.originPortEnd floor)) (span : v.bornBook.rows≤(A.chipBank v floor).size)
    (old : Reads (A.chipBank v floor) chip v.bornBook.lanes m) (lanes : v.bornBook.lanes=v.vector.lanes*v.vector.radix)
    (same : v.bornBook.groups=v.vector.groups*v.vector.radix) (hm : 0<v.vector.lanes) (hr : 0<v.vector.radix)
    (space : v.originMouthEnd floor<2^w) (arg : Fin v.bornBook.args) (f : Fin 3) (b : Fin v.vector.radix) :
    Reads (v.originMouthBank floor match_.newBlocks arg f b)
      (DescentScalarBookReshape.book (fun l h g=>((Lₘ).vals V chip (finProdFinEquiv (arg,f)) l).book
        v.resolver.nodes h (g.cast same.symm)) b) v.vector.lanes ((v.originPrefixMouth floor w A match_).image m) :=
  (Lₘ).issued _ _ _ V m chip prior early span old lanes same hm hr (by rwa [v.mouth_translated]) arg f b

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
