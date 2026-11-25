import OAI.Hierarchy.DescentPrimitiveMoverLayout
import OAI.Hierarchy.DescentResetRetainedIssue
import OAI.Hierarchy.DescentResetRetainedPlacementRead
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # Move genuine one-based global role digits through the elected reset basis -/
namespace Hierarchy.DescentRetainedPrimitive.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentGL DescentColonies
open DescentSixParty.PackedFlow.Channels DescentResetRetainedSetup DescentResetRetainedSetup.Layout
open DescentSixParty.Chronology DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentRetainedPrimitive.Layout) {w U : ℕ}

/-- Each previous block contributes the very same immutable primitive register to
the census and value projections. The register may use the full dictionary width. -/
def prior (prev : Fin z.transfer.blocks→Bank) (j : Fin z.transfer.sources) :=prev (finProdFinEquiv.symm j : Fin z.transfer.fields×Fin z.transfer.blocks).2
def priorValues (X : Fin z.transfer.blocks→Fin z.transfer.hosts→Fin z.transfer.groups→Cell z.transfer.wholeWord) (j : Fin z.transfer.sources) :=
  X (finProdFinEquiv.symm j : Fin z.transfer.fields×Fin z.transfer.blocks).2

def choose (n : Fin z.transfer.nodes) (word : Cell z.transfer.siteWord) : Cell z.transfer.bits :=
  match z.transfer.root word n.val with
  | none=>0
  | some d=>
    if h:n.val-z.transfer.offset word d<z.transfer.previousNodes then
      z.transfer.entry word d ⟨_,h⟩ z.transfer.occupiedField
    else 0

theorem chosen (q : Fin z.transfer.donors) (i : Fin z.transfer.previousNodes) (n : Fin z.transfer.nodes) (wrd : Cell z.transfer.siteWord)
    (atSlot : n.val=z.transfer.offset wrd q+i.val) (live : i.val<z.transfer.originalCount wrd q) :
    z.choose n wrd=z.transfer.entry wrd q i z.transfer.occupiedField:=by
  simp only [choose,atSlot,z.transfer.root_at wrd q i.val live,Nat.add_sub_cancel_left,dite_eq_left i.isLt]

def role (n : Fin z.transfer.nodes) (x : Fin z.transfer.channels→Cell z.transfer.stripWord) :=
  z.choose n (encode z.transfer.stripWord z.transfer.channels x)

theorem role_zero (n : Fin z.transfer.nodes) : z.role n (fun _=>0)=0:=by
  have blank : encode z.transfer.stripWord z.transfer.channels (fun _=>0)=0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin z.transfer.channels => (0 : Cell z.transfer.stripWord))).val = 0
    simp
  rw [role,blank]
  change z.choose n (0 : Cell z.transfer.siteWord) = 0
  unfold choose
  rw [z.transfer.root_zero n.val]

variable (floor : ℕ) (prev : Fin z.transfer.blocks→Bank) (key count inverse : Bank) (primary : Fin z.shapes→Bool)
local notation "low" => z.transfer.tables floor
local notation "high" => z.placementBase floor
def channel (j : Fin z.transfer.channels) : Expr :=.lookup (z.transfer.hostBank floor j) .row
def query (n : Fin z.transfer.nodes) :=DescentOperandFamilyBook.expr z.role z.transfer.decodedLanes low n (z.channel floor)
def movedImage (m : Memory w) :=z.transfer.movedImage floor (z.prior prev) key m
def prepared (m : Memory w) :=DescentOperandFamilyBook.image z.role z.transfer.decodedLanes low (z.movedImage floor prev key m)
def finalMem (m : Memory w) :=z.placement.image z.batch high primary (z.query floor) count inverse (z.prepared floor prev key m)
def program (w : ℕ) :=((z.transfer.moved floor w (z.prior prev) key).seq (DescentOperandFamilyBook.program z.role z.transfer.decodedLanes low w)).seq
  (z.placement.code z.batch high w primary (z.query floor) count inverse)
def ticks (w : ℕ) :=z.transfer.movedTicks floor w (z.prior prev) key+DescentOperandFamilyBook.ticks z.transfer.nodes z.transfer.channels z.transfer.stripWord z.transfer.decodedLanes+
  z.placement.ticks z.batch high (z.query floor) count inverse

private theorem bounds : floor≤low ∧ low≤high ∧ high≤z.endAddress floor:=by
  obtain ⟨a,b,c,d,e,_⟩:=z.transfer.order floor
  rw [endAddress,z.placement.affine (z.batch) high]
  exact ⟨a.trans (b.trans (c.trans (d.trans e))),Nat.le_add_right ..,Nat.le_add_right ..⟩

theorem query_fit (space : z.endAddress floor<2^w) (n : Fin z.transfer.nodes) : (z.query floor n).Fits w high:=by
  have bb:=z.bounds floor
  have room:=(bb.2.1.trans bb.2.2).trans_lt space
  apply DescentOperandFamilyBook.expr_fits _ _ _ _ _ _ (bb.2.2.trans_lt space)
  intro j
  exact ⟨(Strip.fits (w:=w) (z.transfer.mixed floor) z.transfer.hosts z.transfer.grouped z.transfer.matrixLanes z.transfer.decodedLanes z.transfer.stripWord j room).1,trivial⟩

structure Room (w : ℕ) : Prop where
  previous : ∀j,(prev j).Fits w floor
  saved : key.Fits w floor
  countFit : count.Fits w floor
  inverseFit : inverse.Fits w floor
  lanes : 0<z.lanes
  blocks : 0<z.blocks
  roof : z.endAddress floor<2^w

variable (r : z.Room floor prev key count inverse w)
include r in
theorem any (m : Memory w) :
    (z.program floor prev key count inverse primary w).Exec m (z.finalMem floor prev key count inverse primary m)
      (z.ticks floor prev key count inverse w) ∧ CheapCode (z.program floor prev key count inverse primary w) ∧
    ∀a,a<floor ∨ z.endAddress floor≤a→z.finalMem floor prev key count inverse primary m a=m a:=by
  have bb:=z.bounds floor
  have framed:=bb.1.trans bb.2.1
  have top:=bb.2.2.trans_lt r.roof
  have m₁:=z.transfer.moved_any floor (z.prior prev) key m (fun j=>r.previous _) r.saved (bb.2.1.trans_lt top)
  have m₂:=DescentOperandFamilyBook.any z.role z.transfer.decodedLanes low (z.movedImage floor prev key m) top
  have bank {B : Bank} (fit : B.Fits w floor) : B.Fits w high:=⟨fit.1,fit.2.1,fit.2.2.trans framed⟩
  have m₃:=z.placement.any z.batch high primary (z.query floor) count inverse (z.prepared floor prev key m) r.lanes r.blocks
    (z.query_fit floor r.roof) (bank r.countFit) (bank r.inverseFit) r.roof
  refine ⟨Procedure.Exec.then (Procedure.Exec.then m₁.1 m₂.1) m₃.1,cheap_seq (cheap_seq m₁.2.2 m₂.2.1) m₃.2.2,?_⟩
  intro j h
  exact (m₃.2.1 j (h.imp_left (·.trans_le framed))).trans <|
    (m₂.2.2.1 j (h.imp (·.trans_le bb.1) (bb.2.2.trans ·))).trans (m₁.2.1 j (h.imp_right ((bb.2.1.trans bb.2.2).trans ·)))

def inputs (size : 2^(z.transfer.high+z.transfer.low)=z.transfer.groups*z.transfer.blocks) (cut : z.transfer.cut≤z.transfer.high+z.transfer.low)
    (L : DescentGL.Layout (z.transfer.high+z.transfer.low)) (X : Fin z.transfer.blocks→Fin z.transfer.hosts→Fin z.transfer.groups→Cell z.transfer.wholeWord)
    (n : Fin z.transfer.nodes) (h : Fin z.transfer.hosts) (g : Fin z.transfer.grouped) :=
  z.role n (fun j=>blockValues cut (z.transfer.before size (z.priorValues X) j) L h g)

/-- The compressed donor offset removes all earlier positive role digits. Its
value at the selected local ordinal is the original packed role digit read in the
old block named by the inverse of the actual elected basis. -/
theorem original (size : 2^(z.transfer.high+z.transfer.low)=z.transfer.groups*z.transfer.blocks) (cut : z.transfer.cut≤z.transfer.high+z.transfer.low)
    (L : DescentGL.Layout (z.transfer.high+z.transfer.low)) (X : Fin z.transfer.blocks→Fin z.transfer.hosts→Fin z.transfer.groups→Cell z.transfer.wholeWord)
    (n : Fin z.transfer.nodes) (h : Fin z.transfer.hosts) (g : Fin z.transfer.grouped) (d : Fin z.transfer.donors) (j : Fin z.transfer.previousNodes) :
    let wrd:=z.transfer.site (fun i=>blockValues cut (z.transfer.before size (z.priorValues X) i) L) h g
    let old:=(rearrange L).symm (DescentIssuedFallbackPanel.join cut g d)
    let pos:=(finProdFinEquiv.symm (Fin.cast size old) : Fin z.transfer.groups×Fin z.transfer.blocks)
    n.val=z.transfer.offset wrd d+j.val→j.val<z.transfer.originalCount wrd d→
      z.inputs size cut L X n h g=ScalarOperand.take (a:=z.transfer.bits) j (X pos.2 h pos.1):=by
  intro wrd old pos index occupied
  change z.choose n wrd=_
  rw [z.chosen d j n wrd index occupied]
  simpa only [priorValues,DescentResetRetainedSetup.Layout.sourceID,Equiv.symm_apply_apply] using
    z.transfer.prior_digit (z.priorValues X) size cut L h g d j z.transfer.occupiedField

private theorem recast_source {A B H d M w : ℕ} (h : A=B) (e : Expr) (m : Memory w)
    (xs : Fin H → Fin B → Cell d) (he : Source e xs M m) :
    Source e (fun a j => xs a (Fin.cast h j)) M m := by
  subst B
  exact he

include r in
theorem issued (m : Memory w) (size : 2^(z.transfer.high+z.transfer.low)=z.transfer.groups*z.transfer.blocks) (batch : 2^z.transfer.low=z.transfer.gatherLanes*z.transfer.blocks)
    (hg : 0<z.transfer.gatherLanes) (hb : 0<z.transfer.blocks) (hp : 0<z.transfer.previousLanes) (cut : z.transfer.cut≤z.transfer.high+z.transfer.low)
    (pitch : z.transfer.matrixLanes*z.transfer.donors=2^z.transfer.low) (live : 0<z.transfer.matrixLanes) (dec : 0<z.transfer.decodedLanes)
    (L : DescentGL.Layout (z.transfer.high+z.transfer.low)) (elected : m key.base=((DescentExterior.matrixCode L).val:Word w))
    (X : Fin z.transfer.blocks→Fin z.transfer.hosts→Fin z.transfer.groups→Cell z.transfer.wholeWord)
    (capacity : ∀j,z.transfer.hosts*chunks z.transfer.groups z.transfer.previousLanes≤(prev j).size)
    (read : ∀j,Reads (prev j) (X j) z.transfer.previousLanes m) (groups : z.groups*z.blocks=z.transfer.grouped)
    (name : Fin U→Fin z.placement.sparse) (cnt : m count.base=(U:Word w))
    (inv : ∀i:Fin U,m (inverse.base+i.val)=((name i).val:Word w))
    (narrow : U<2^w) (hosts : z.newHosts≤2^w) (saved : U≤ inverse.size) (n : Fin z.transfer.nodes) (x : Fin z.blocks) :
    Source (.lookup (z.bank floor n x) .row)
      (z.placement.compact z.batch primary name (fun j h g=>z.inputs size cut L X j h (g.cast groups)) n x)
      z.lanes (z.finalMem floor prev key count inverse primary m) :=by
  have bb:=z.bounds floor
  have top:=bb.2.2.trans_lt r.roof
  have before:=bb.2.1.trans_lt top
  have frames:=z.transfer.moved_any floor (z.prior prev) key m (fun j=>r.previous _) r.saved before
  have mk:=DescentOperandFamilyBook.any z.role z.transfer.decodedLanes low (z.movedImage floor prev key m) top
  have same i (lo:i<floor) : z.prepared floor prev key m i=m i:=
    (mk.2.2.1 i (.inl (lo.trans_le bb.1))).trans (frames.2.1 i (.inl lo))
  have bank {B : Bank} (fit : B.Fits w floor) : B.Fits w high:=⟨fit.1,fit.2.1,fit.2.2.trans (bb.1.trans bb.2.1)⟩
  have first:=z.transfer.moved_reads floor (z.prior prev) key m (fun j=>r.previous _) r.saved before size batch hg hb hp cut pitch live
    L elected (z.priorValues X) (fun j=>capacity _) (fun j=>read _)
  have selected (j : Fin z.transfer.nodes) : Source (z.query floor j) (z.inputs size cut L X j) z.transfer.decodedLanes (z.prepared floor prev key m):=by
    apply (DescentOperandFamilyBook.issued z.role z.role_zero z.transfer.decodedLanes low j (z.channel floor) (z.movedImage floor prev key m)
      (fun h g i=>blockValues cut (z.transfer.before size (z.priorValues X) i) L h g) ?_ ?_ top).2
    · intro i
      exact ⟨(Strip.fits (w:=w) (z.transfer.mixed floor) z.transfer.hosts z.transfer.grouped z.transfer.matrixLanes z.transfer.decodedLanes z.transfer.stripWord i before).1,trivial⟩
    · intro i
      obtain ⟨fit,cap⟩:=Strip.fits (w:=w) (z.transfer.mixed floor) z.transfer.hosts z.transfer.grouped z.transfer.matrixLanes z.transfer.decodedLanes z.transfer.stripWord i before
      exact source_column _ _ fit _ _ cap (first i)
  apply z.placement.read z.batch high primary (z.query floor) count inverse (z.prepared floor prev key m) r.lanes dec r.blocks
    (z.query_fit floor r.roof) (bank r.countFit) (bank r.inverseFit) r.roof name ((same _ (by have pos:=r.countFit.1;have bound:=r.countFit.2.2;omega)).trans cnt)
    (fun i=>(same _ ((Nat.add_lt_add_left (i.isLt.trans_le saved) _).trans_le r.inverseFit.2.2)).trans (inv i))
    narrow hosts saved _ _ n x
  intro i
  exact recast_source groups _ _ _ (selected i)

end
end Hierarchy.DescentRetainedPrimitive.Layout

end OAI
