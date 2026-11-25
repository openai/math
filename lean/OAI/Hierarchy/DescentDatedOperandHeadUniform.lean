import OAI.Hierarchy.DescentDatedOperandHeadTransfer
import OAI.Hierarchy.DescentDatedOperandEarlyUniform

namespace OAI
/-! # One measured ordinary source-head program on every original history -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentHaloWalkRAM DescentSIMDLookup DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

/-- The selected geometry enters only through the public signed program and four
numerical addresses or sizes already determined by the ordinary argument plan. -/
structure HeadCode where
  signed : SignedProgram
  profile : ℕ
  mouth : ℕ
  first : ℕ
  pitch : ℕ

namespace HeadCode
variable (C : HeadCode)
local notation "mat₀" => C.signed.material.extent
local notation "fmt₀" => C.signed.material.depot
local notation "signed₀" => C.signed.signed
local notation "P" => breadth (fmt₀).degree
local notation "H" => (mat₀).oldHosts
local notation "G" => (mat₀).groups
local notation "M" => (mat₀).lanes
local notation "B" => (mat₀).blocks
local notation "b" => (mat₀).fieldBits
local notation "O" => DepotRAM.Material.roles fmt₀

def depot : DescentDatedOperandPages.Layout :=
  ⟨(mat₀).oldHosts,(mat₀).oldGroups,(mat₀).oldLanes,(mat₀).lanes*(mat₀).blocks,(mat₀).fieldBits,C.profile⟩
def paths :=DescentDatedOperandPages.lastAddress fmt₀ C.depot C.mouth
def ranks :=DescentDatedSourcePathDirectory.stop C.paths H G M (fmt₀).degree
def rankBanks :=PriorHeader.rankBanks H G M (fmt₀).degree C.signed.entry
def roster :=PriorHeader.ports H G M (fmt₀).degree C.signed.entry

def datum (block : Fin B) (path : Fin P) (col : Fin (DescentDatedOperandPages.count fmt₀)) : Expr :=
  DescentDatedOperandPages.socket fmt₀ H G (mat₀).hosts M B b ((mat₀).projectionStart C.signed.beginAt)
    C.rankBanks C.roster (DescentDatedOperandPages.resultBank fmt₀ C.depot C.mouth col) path block
def oldSlotHead (jobBlock : Fin B) (j : Fin 4)
    (i : Fin (P*((fmt₀).blocks*((fmt₀).degree*(fmt₀).cap)))) : Expr :=
  let (p,t):=finProdFinEquiv.symm i
  let (x,s):=finProdFinEquiv.symm t
  let (peer,first):=finProdFinEquiv.symm s
  C.datum jobBlock p (DescentDatedOperandPages.header fmt₀ x peer first j)

def anchorHead (jobBlock : Fin B) (j : Fin 5)
    (i : Fin (P*((fmt₀).blocks*((fmt₀).cap*3)))) : Expr :=
  let (p,t):=finProdFinEquiv.symm i
  let (x,s):=finProdFinEquiv.symm t
  let (old,mode):=finProdFinEquiv.symm s
  let col:=if live : mode.val<2 then DescentDatedOperandPages.anchor fmt₀ x old ⟨mode.val,live⟩ j
    else DescentDatedOperandPages.sibling fmt₀ x old j
  C.datum jobBlock p col

def receiverMap :=
  DepotRAM.Material.Route.bank (mat₀).hosts G M (DepotRAM.Material.Route.Projection.mapBase b B M
    ((mat₀).projectionStart (C.signed.beginAt)))
def previousPathHead (i : Fin (P*((fmt₀).degree+1))) : Expr :=
  let (p,d):=finProdFinEquiv.symm i
  let hdr:=DescentDatedSourcePathDirectory.chart (C.paths) H G M p d
  DepotRAM.Material.Route.lift (C.receiverMap) (H*chunks G M) (DescentSharedLeafLookup.source hdr (0:Fin 1))

def rawFieldHead (block : Fin B) (j : Fin 6) (i : Fin (P*O)) : Expr :=
  let (path,lo):=finProdFinEquiv.symm i
  C.signed.material.bankSocket C.signed.beginAt C.rankBanks C.roster
    (DepotRAM.Material.Sheets.rawId fmt₀ j ((DepotRAM.Material.seatIndex fmt₀).symm lo)) path block 0

def localRankHead (p : Fin P) : Expr :=
  let pub:=DescentDatedSourcePathDirectory.hostEnd (C.paths) (mat₀).oldHosts (fmt₀).degree
  let chart:=DescentDatedSourcePathDirectory.Local.chart pub (C.ranks) (mat₀).oldHosts (mat₀).groups (mat₀).lanes p
  DepotRAM.Material.Route.lift (C.receiverMap) ((mat₀).oldHosts*chunks (mat₀).groups (mat₀).lanes)
    (DescentSharedLeafLookup.source chart (0:Fin 1))

def parentSlot (c : C.signed.Chart) (i : Fin (P*O)) : Fin (signed₀).candidates :=
  i.cast (congrArg₂ Nat.mul (congrArg breadth c.degree.symm) c.seats.symm)
def parentSerial (c : C.signed.Chart) (x : Fin (mat₀).blocks) (i : Fin (P*O)) : Expr :=
  let core:=DescentOrdinarySignedParents.ROM.endAddress ((signed₀).tailStart (C.signed.afterMark)) (signed₀).degree (signed₀).lowSites
    (signed₀).tickets (signed₀).cap (signed₀).fieldBits (signed₀).lanes
  DescentOrdinarySignedAll.ranks core (signed₀).blocks (signed₀).candidates (signed₀).fieldBits (signed₀).lanes (signed₀).hosts (signed₀).groups
    (x.cast c.blocks.symm) 1 (C.parentSlot c i)
def parentPeer (c : C.signed.Chart) (x : Fin (mat₀).blocks) (i : Fin (P*O)) : Expr :=
  (signed₀).peerField (C.signed.input c) (C.signed.afterMark) (x.cast c.blocks.symm,C.parentSlot c i)

def signedRawHead (c : C.signed.Chart) (block : Fin (mat₀).blocks) (f : Fin 8) (i : Fin (P*O)) : Expr :=
  if live:f.val<6 then C.rawFieldHead block ⟨f.val,live⟩ i
  else if f.val=6 then C.parentSerial c block i else C.parentPeer c block i


def oldHeadCount := P*((fmt₀).blocks*((fmt₀).degree*(fmt₀).cap))
def anchorHeadCount := P*((fmt₀).blocks*((fmt₀).cap*3))
def rawHeadCount := P*((fmt₀).blocks*((fmt₀).cap*11))
def pathHeadCount := P*((fmt₀).degree+1)

/-- Only the block of an argument job participates in an original source read.
All nodes and all operand slots of that block share its returned words. -/
def wideHeads : DescentOrdinaryHeadRetile.Shape :=
  ⟨B*(4*C.oldHeadCount)+(B*(5*C.anchorHeadCount)+B*(8*C.rawHeadCount)),
    (mat₀).hosts,(mat₀).groups,(mat₀).lanes,C.pitch,(mat₀).fieldBits⟩
def narrowHeads : DescentOrdinaryHeadRetile.Shape :=
  ⟨C.pathHeadCount+P,(mat₀).hosts,(mat₀).groups,(mat₀).lanes,C.pitch,Packed.bits P⟩

abbrev WideHead := HeadTriple B 4 C.oldHeadCount ⊕
  (HeadTriple B 5 C.anchorHeadCount ⊕ HeadTriple B 8 C.rawHeadCount)
abbrev NarrowHead := Fin C.pathHeadCount ⊕ Fin P

def wideHeadNumber : C.WideHead ≃ Fin C.wideHeads.n :=
  ((headNumber ..).sumCongr (((headNumber ..).sumCongr (headNumber ..)).trans finSumFinEquiv)).trans finSumFinEquiv

def narrowHeadNumber : C.NarrowHead ≃ Fin C.narrowHeads.n := finSumFinEquiv
def wideHead (c : C.signed.Chart) (key : C.WideHead) : Expr :=
  match key with
  | .inl (x,f,i) => C.oldSlotHead x f i
  | .inr (.inl (x,f,i)) => C.anchorHead x f i
  | .inr (.inr (x,f,i)) => C.signedRawHead c x f i

def narrowHead (key : C.NarrowHead) : Expr :=
  match key with
  | .inl i => C.previousPathHead i
  | .inr p => C.localRankHead p

def wideHeadSource (c : C.signed.Chart) (i : Fin C.wideHeads.n) :=C.wideHead c (C.wideHeadNumber.symm i)
def narrowHeadSource (i : Fin C.narrowHeads.n) :=C.narrowHead (C.narrowHeadNumber.symm i)

def middle :=C.wideHeads.endAddress C.first
def finish :=C.narrowHeads.endAddress C.middle
def wideWord (key : C.WideHead) : Expr :=.lookup (C.wideHeads.bank C.first (C.wideHeadNumber key)) .row
def narrowWord (key : C.NarrowHead) : Expr :=.lookup (C.narrowHeads.bank C.middle (C.narrowHeadNumber key)) .row

def oldWord (x : Fin B) (f : Fin 4) (i : Fin C.oldHeadCount) :=C.wideWord (.inl (x,f,i))
def anchorWord (x : Fin B) (f : Fin 5) (i : Fin C.anchorHeadCount) :=C.wideWord (.inr (.inl (x,f,i)))
def rawWord (x : Fin B) (f : Fin 8) (i : Fin C.rawHeadCount) :=C.wideWord (.inr (.inr (x,f,i)))
def pathWord (i : Fin C.pathHeadCount) :=C.narrowWord (.inl i)
def rankWord (i : Fin P) :=C.narrowWord (.inr i)

theorem words_congr {D : HeadCode} (equal : C=D) :
    C.finish=D.finish ∧ HEq C.oldWord D.oldWord ∧ HEq C.anchorWord D.anchorWord ∧
    HEq C.rawWord D.rawWord ∧ HEq C.pathWord D.pathWord ∧ HEq C.rankWord D.rankWord :=by
  cases equal
  exact ⟨rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

def native (c : C.signed.Chart) (w : ℕ) : NativePhase w :=
  (C.wideHeads.phase C.first (C.wideHeadSource c) w).seq
    (C.narrowHeads.phase (C.wideHeads.endAddress C.first) C.narrowHeadSource w)

theorem congruent {D : HeadCode} (equal : C=D) (c : C.signed.Chart) (d : D.signed.Chart) (w : ℕ) :
    C.native c w=D.native d w :=by cases equal; rfl
end HeadCode

variable {F P F' P' : Type} [Field F] [Field F']
def headCode (v : PhysicalOrdinary F P) (floor : ℕ) : HeadCode :=
  ⟨v.signedProgram floor,v.profile,v.originMouthEnd floor,v.operandHeaderEnd floor,v.resolver.lanes⟩

private theorem public_wide_head (v : PhysicalOrdinary F P) (floor : ℕ) (c : v.SignedChart)
    (q : v.WideHead) :
    (v.headCode floor).wideHead (v.publicSignedChart floor c) q = v.wideHead floor c q := by
  rcases q with ⟨x,f,i⟩ | (⟨x,f,i⟩ | ⟨x,f,i⟩)
  · rfl
  · rfl
  · change (v.headCode floor).signedRawHead (v.publicSignedChart floor c) x f i = v.signedRawHead floor c x f i
    unfold HeadCode.signedRawHead signedRawHead
    split
    · rfl
    · split <;> rfl

private theorem public_narrow_head (v : PhysicalOrdinary F P) (floor : ℕ) (q : v.NarrowHead) :
    (v.headCode floor).narrowHead q = v.narrowHead floor q := by
  cases q <;> rfl

theorem actual_head_native (v : PhysicalOrdinary F P) (floor w : ℕ) (c : v.SignedChart) :
    (v.headCode floor).native (v.publicSignedChart floor c) w=v.headTransferPhase floor c w :=by
  have wide : (v.headCode floor).wideHeadSource (v.publicSignedChart floor c) = v.wideHeadSource floor c :=
    funext fun i => public_wide_head v floor c (v.wideHeadNumber.symm i)
  have narrow : (v.headCode floor).narrowHeadSource = v.narrowHeadSource floor :=
    funext fun i => public_narrow_head v floor (v.narrowHeadNumber.symm i)
  unfold HeadCode.native headTransferPhase
  rw [wide,narrow]
  rfl

theorem actual_head_words (v : PhysicalOrdinary F P) (floor : ℕ) :
    (v.headCode floor).finish=v.headTransferEnd floor ∧
    (∀q : v.WideHead,(v.headCode floor).wideWord q=v.wideWord floor q) ∧
    (∀q : v.NarrowHead,(v.headCode floor).narrowWord q=v.narrowWord floor q) :=
  ⟨rfl,fun _=>rfl,fun _=>rfl⟩

def ArgumentPlan.headCode (p : ArgumentPlan) (geo : StaticCore) : HeadCode :=
  ⟨geo.prefixProgram,geo.prefixProgram.material.setup.profile,p.originMouthEnd,p.headBound geo,p.resolver.lanes⟩

theorem head_code_plan (v : PhysicalOrdinary F P) (floor : ℕ) (A : v.ArgumentEntry) (m : A.Match v floor) :
    (v.bareArguments floor A m).headCode (v.staticCore floor)=v.headCode floor :=rfl

theorem head_code_eq (v : PhysicalOrdinary F P) (u : PhysicalOrdinary F' P') (floor next : ℕ)
    (A : v.ArgumentEntry) (B : u.ArgumentEntry) (a : A.Match v floor) (b : B.Match u next)
    («arguments» : v.bareArguments floor A a=u.bareArguments next B b) (core : v.staticCore floor=u.staticCore next) :
    v.headCode floor=u.headCode next :=by
  rw [←v.head_code_plan floor A a,←u.head_code_plan next B b,«arguments»,core]

attribute [local irreducible] DescentOrdinaryHeadRetile.Shape.bank DescentOrdinaryHeadRetile.Shape.endAddress

/-- Equality of the actual returned operand-bank expressions, including when the host,
block and route ordinal types are only propositionally equal across the two histories. -/
theorem head_words_plan_eq (v : PhysicalOrdinary F P) (u : PhysicalOrdinary F' P') (floor next : ℕ)
    (A : v.ArgumentEntry) (B : u.ArgumentEntry) (a : A.Match v floor) (b : B.Match u next)
    («arguments» : v.bareArguments floor A a=u.bareArguments next B b) (core : v.staticCore floor=u.staticCore next) :
    v.headTransferEnd floor=u.headTransferEnd next ∧
    HEq (v.transferredOld floor) (u.transferredOld next) ∧ HEq (v.transferredAnchor floor) (u.transferredAnchor next) ∧
    HEq (v.transferredRaw floor) (u.transferredRaw next) ∧ HEq (v.transferredPath floor) (u.transferredPath next) ∧
    HEq (v.transferredRank floor) (u.transferredRank next) :=by
  have ⟨last,old,anchor,raw,path,rank⟩ :=
    (v.headCode floor).words_congr (v.head_code_eq u floor next A B a b «arguments» core)
  exact ⟨last,old,anchor,raw,path,rank⟩

theorem head_transfer_plan_eq (v : PhysicalOrdinary F P) (u : PhysicalOrdinary F' P') (floor next w : ℕ)
    (A : v.ArgumentEntry) (B : u.ArgumentEntry) (a : A.Match v floor) (b : B.Match u next)
    (c : v.SignedChart) (d : u.SignedChart)
    («arguments» : v.bareArguments floor A a=u.bareArguments next B b) (core : v.staticCore floor=u.staticCore next) :
    v.headTransferPhase floor c w=u.headTransferPhase next d w :=by
  have shape:=v.head_code_eq u floor next A B a b «arguments» core
  exact (v.actual_head_native floor w c).symm.trans
    (((v.headCode floor).congruent shape (v.publicSignedChart floor c) (u.publicSignedChart next d) w).trans
      (u.actual_head_native next w d))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
