import OAI.Hierarchy.DescentDatedCandidateSheets
import OAI.Hierarchy.DescentResetOriginalZeroHaloPrice
import OAI.Hierarchy.DescentStemCoordinateBook
import OAI.Hierarchy.DescentResetNumberStem
import OAI.Hierarchy.DescentResetPrivateOriginal
import OAI.Hierarchy.DescentResetPublicWordLookup

namespace OAI
/-! The original-number pages for stems, graph contacts, the public trunk and the private roots. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets
open DescentSIMDLookup DescentResetMixedWordRAM OriginalDate DescentResetPublicParentWord
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 350000
variable {w : ℕ} (s : CandidateSheets)

/-- The graph, public local menu and previous RAM expressions are fixed for a physical date. -/
structure OriginalInputs where
  boardBits : ℕ
  boardPorts : ℕ
  signedSlots : ℕ
  stems : ℕ
  board : NonlinearExpanders.Graph boardBits boardPorts
  geometry : DescentResetPublicParentWord.Shape
  treeHeight : ℕ
  degree : ℕ
  blockBits : ℕ
  resultBits : ℕ
  publicShelf : Fin (s.contacts+1)↪Fin s.candidates
  stemShelf : Fin stems↪Fin s.candidates
  privateShelf : Fin s.privates↪Fin s.candidates
  request : Fin s.contacts→Bool×ℕ
  side : Fin stems→Bool
  sensor : DescentResetOriginalDonors.Sensors s.originalDonors.slots
  sources : DescentResetPublicOriginalPhase.Prior s.blocks s.contacts signedSlots
  stem : Fin s.blocks→Fin stems→Fin 6→Expr
  privateMeta : Fin s.blocks→Fin s.privates→Expr
  zero : Fin s.blocks→Expr
  halo : Fin s.blocks→Expr

namespace OriginalInputs
variable {s} (u : s.OriginalInputs) (base : ℕ)
local notation "X" => s.blocks
local notation "J" => s.privates
local notation "K" => s.candidates

def publicSide : DescentResetPublicOriginalPhase.Layout X s.contacts K u.signedSlots :=
  { req:=u.request,shelf:=u.publicShelf,fn:=fun mode=>
      if mode=0 then trunkWord u.board u.geometry.halo u.geometry.depth u.geometry.span u.geometry.cap
        u.geometry.sockets u.geometry.program u.treeHeight
      else fun v z h j=>directWord u.geometry u.treeHeight v z (h-1) j
    M:=s.lanes,hosts:=s.hosts,groups:=s.groups,selectorBits:=s.selectorBits,shortBits:=s.shortBits,
    metaBits:=s.metaBits,zeroBits:=s.zeroBits,resultBits:=u.resultBits,donor:=s.inputDonorsEnd base,
    format:=s.donorEnd base,original:=s.original base,old:=u.sources }

def stemSide : DescentResetNumberStem.Layout X u.stems K :=
  { degree:=u.degree,k:=u.blockBits,depth:=u.geometry.depth,Y:=u.geometry.ports,labels:=u.geometry.span,
    cap:=u.geometry.cap,links:=u.geometry.sockets,pc:=u.geometry.program,wordBits:=u.resultBits,
    field:=s.stemBits,M:=s.lanes,rows:=s.rows,header:=s.publicFormatEnd base,original:=s.original base,
    shelf:=u.stemShelf,side:=u.side,src:=u.stem }

def privateSide : Date X J K :=
  { shelf:=u.privateShelf,kind:=fun _=>0,header:=s.privateArgsEnd base,original:=s.original base,rows:=s.rows,
    lanes:=s.lanes,metaBits:=s.metaBits,zeroBits:=s.zeroBits,haloBits:=s.haloBits,argBits:=s.argBits,
    wordBits:=u.resultBits,fn:=fun _=>privateWord u.geometry,
    «fields» := { «meta» := fun p => u.privateMeta (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2,
                  zero := fun p => u.zero (finProdFinEquiv.symm p).1,
                  halo := fun p => u.halo (finProdFinEquiv.symm p).1,
                  arg := fun p =>DescentUniformSlotOperands.expr (s.stemFormatEnd base) s.hosts s.groups s.lanes s.argBits (finProdFinEquiv.symm p).2} }

local notation "P" => u.publicSide base
local notation "T" => u.stemSide base
local notation "A" => u.privateSide base
local notation "S" => s.stemFormatEnd base
local notation "slots" w => DescentUniformSlotOperands.program S J s.hosts s.groups s.lanes s.argBits w
local notation "slotState" m => DescentUniformSlotOperands.result S J s.hosts s.groups s.lanes s.argBits m

local notation "D₀" => s.originalDonors
local notation "d₀" => s.inputDonorsBase base
local notation "deck" => s.coordinateEnd base
def scalarPhase (w : ℕ) := DescentResetOriginalZeroHalo.phase w deck s.hosts s.groups s.lanes s.metaBits
  s.zeroBits s.shortBits s.haloBits u.degree

def «prefix» (w : ℕ) :=((s.stemSources.program (s.metaEnd base) w).seq (u.scalarPhase base w).program).seq
  ((D₀).program d₀ u.sensor w)
def prefixTime :=(s.stemSources.ticks + 4+10*DescentResetOriginalZeroHalo.count s.hosts s.groups s.lanes s.metaBits)+
  (D₀).ticks d₀ u.sensor
def prefixOutput (m : Memory w) :=(D₀).after d₀ u.sensor
  ((u.scalarPhase base w).image (s.stemSources.image (s.metaEnd base) m))

theorem prefix_any (m : Memory w) (r : (D₀).Ready d₀ u.sensor w) :
    (u.«prefix» base w).Exec m (u.prefixOutput base m) (u.prefixTime base) ∧ CheapCode (u.«prefix» base w) ∧
    ∀i,i<s.metaEnd base ∨ s.inputDonorsEnd base≤ i→u.prefixOutput base m i=m i :=by
  have deckLo : s.metaEnd base≤deck:=by rw [coordinateEnd,s.stemSources.extent];exact Nat.le_add_right ..
  have scalarLo : deck≤d₀:=by rw [inputDonorsBase,DescentResetOriginalZeroHalo.shift deck];exact Nat.le_add_right ..
  have donorLo : d₀≤ s.inputDonorsEnd base:=by obtain ⟨t,h,z⟩:=(D₀).cuts d₀;exact t.trans (h.trans z)
  let co:=s.stemSources.image (s.metaEnd base) m
  have C:=s.stemSources.any (s.metaEnd base) m ((scalarLo.trans donorLo).trans_lt r.room)
  have scalar:=DescentResetOriginalZeroHalo.any deck s.hosts s.groups s.lanes s.metaBits s.zeroBits s.shortBits
    s.haloBits u.degree co (donorLo.trans_lt r.room)
  have D:=(D₀).any d₀ u.sensor r ((u.scalarPhase base w).image co)
  refine ⟨?_,@cheap_seq w _ _ (@cheap_seq w _ _ (@C.2.1) (@(u.scalarPhase base w).cheap)) (@D.2.1),?_⟩
  · have ticks : u.prefixTime base = (s.stemSources.ticks + (u.scalarPhase base w).ticks) +
        (D₀).ticks d₀ u.sensor := by
      change (s.stemSources.ticks + 4 + 10 * DescentResetOriginalZeroHalo.count s.hosts s.groups s.lanes s.metaBits) + _ =
        (s.stemSources.ticks + (4 + 10 * DescentResetOriginalZeroHalo.count s.hosts s.groups s.lanes s.metaBits)) + _
      omega
    rw [ticks]
    intro labels regs pubs machine pc reg pub exit rom advice cfg mem enter same
    exact Procedure.Exec.then (Procedure.Exec.then (@C.1) (@scalar.1)) (@D.1) machine pc reg pub exit rom advice cfg mem enter same
  · intro i away
    exact (D.2.2 i (away.imp (fun h=>h.trans_le (deckLo.trans scalarLo)) id)).trans
      ((scalar.2 i (away.imp (fun h=>h.trans_le deckLo) (fun h=>donorLo.trans h))).trans
        (C.2.2 i (away.imp id (fun h=>(scalarLo.trans donorLo).trans h))))

def code (w : ℕ) := (((u.«prefix» base w).seq ((P).cpu w)).seq ((T).code w)).seq ((slots w).seq ((A).code w))
def time := ((u.prefixTime base+(P).clock)+(T).ticks)+
  (((4+10*J)+(4+10*DescentResetHaloBroadcast.count s.hosts s.groups s.lanes s.argBits))+(A).ticks)
def output (m : Memory w) := (A).dst (slotState ((T).image ((P).dst (u.prefixOutput base m))))

structure Room (w : ℕ) : Prop where
  donor : (D₀).Ready d₀ u.sensor w
  public_ : (P).Room w
  stem : (T).Room w
  private_ : (A).Room w
  args : J≤2^s.argBits
  pitches : s.inputDonorsEnd base≤ s.publicFormatEnd base ∧ s.publicFormatEnd base≤S ∧ S≤ s.privateArgsEnd base

theorem any (m : Memory w) (r : u.Room base w) :
    (u.code base w).Exec m (u.output base m) (u.time base) ∧ CheapCode (u.code base w) ∧
    ∀i,i<s.metaEnd base ∨ s.originalEnd base≤ i→u.output base m i=m i := by
  obtain ⟨a,b,c⟩:=r.pitches
  have endFit:s.originalEnd base<2^w:=r.private_.endFits
  have gateBefore:s.metaEnd base≤ s.inputDonorsEnd base:=by
    rw [donors_shift,coordinateEnd,s.stemSources.extent];omega
  obtain ⟨coords,c₀,k₀⟩:=u.prefix_any base m r.donor
  let co:=u.prefixOutput base m
  obtain ⟨publicRun,c₁,keepP⟩:=(P).any r.public_ co
  obtain ⟨stemRun,c₂,keepT⟩:=(T).any r.stem ((P).dst co)
  have argsEnd:s.privateArgsEnd base≤ s.original base:=Nat.le_add_right ..
  have slotEnd:s.original base≤ s.originalEnd base:=Nat.le_add_right ..
  have fit:s.originalEnd base<2^w:=r.private_.endFits
  obtain ⟨slotsRun,_,keepA,_⟩:=DescentUniformSlotOperands.produce S J s.hosts s.groups s.lanes s.argBits
    ((T).image ((P).dst co)) r.args (argsEnd.trans_lt (slotEnd.trans_lt fit))
  obtain ⟨privateRun,c₄,keepF⟩:=(A).any r.private_ _
  refine ⟨?_, ?_, ?_⟩
  · intro labels regs pubs machine pc reg pub exit rom advice cfg mem enter same
    exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (@coords) (@publicRun)) (@stemRun))
      (Procedure.Exec.then (@slotsRun) (@privateRun)) machine pc reg pub exit rom advice cfg mem enter same
  · exact @cheap_seq w _ _ (@cheap_seq w _ _ (@cheap_seq w _ _ (@c₀) (@c₁)) (@c₂))
      (@cheap_seq w _ _ (@cheap_seq w _ _ (@DescentStaticWordColumn.cheap _ _ _ _)
        (@DescentStaticWordColumn.cheap _ _ _ _)) (@c₄))
  · intro z away
    have endF:(A).firstEnd=s.original base:=rfl
    have pStop:(P).date.stop=s.originalEnd base:=rfl
    have tStop:(T).endAddress=s.originalEnd base:=rfl
    have k₁:=keepP z (by change z<s.inputDonorsEnd base ∨ (P).date.stop≤z;omega)
    have k₂:=keepT z (by change z<s.publicFormatEnd base ∨ (T).endAddress≤z;omega)
    have k₃:=keepA z (by change z<S ∨ s.privateArgsEnd base≤z;omega)
    have k₄:=keepF z (by change z<s.privateArgsEnd base ∨ (A).firstEnd≤z;omega)
      (by intro p
          rcases away with lo|hi
          · left;exact (lo.trans_le (gateBefore.trans (a.trans (b.trans (c.trans argsEnd))))).trans_le (Nat.le_add_right ..)
          · right;exact (DescentResetNumberStem.Layout.range (A).shelf (s.original base) s.rows p).trans hi)
    exact k₄.trans (k₃.trans (k₂.trans (k₁.trans (k₀ z (by omega)))))

end OriginalInputs
end
end Hierarchy.DescentDatedAddressBook.CandidateSheets

end OAI
