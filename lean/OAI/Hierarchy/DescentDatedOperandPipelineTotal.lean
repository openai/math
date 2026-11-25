import OAI.Hierarchy.DescentDatedOperandMeasuredRead

namespace OAI
/-! # On arbitrary input words the five native selectors stay inside their physical reservation -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (g : Geometry) (s : Sources g)
local notation "J" => g.jobs
local notation "a" => g.digitBits
local notation "P" => g.paths
local notation "D" => g.degree
local notation "B" => g.blocks
local notation "C" => g.cap
local notation "M" => g.lanes
local notation "S₁" => P*(B*(D*C))
local notation "S₂" => P*(D+1)
local notation "S₃" => P*(B*(C*3))
local notation "S₄" => P*(B*(C*11))

structure SourceRoom (w base : ℕ) : Prop where
  origin : ∀j f,(s.origin j f).Fits w base
  prior : ∀j f,(s.prior j f).Fits w base
  mouth : ∀j f,(s.mouth j f).Fits w base
  old : ∀j f i,(s.old j f i).Fits w base
  path : ∀i,(s.path i).Fits w base
  anchor : ∀j f i,(s.anchor j f i).Fits w base
  raw : ∀j f i,(s.raw j f i).Fits w base
  rank : ∀i,(s.rank i).Fits w base

theorem SourceRoom.extend {w low high : ℕ} (room : SourceRoom g s w low) (order : low≤high) :
    SourceRoom g s w high :=
  ⟨fun j f=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.origin j f),
   fun j f=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.prior j f),
   fun j f=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.mouth j f),
   fun j f i=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.old j f i),
   fun i=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.path i),
   fun j f i=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.anchor j f i),
   fun j f i=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.raw j f i),
   fun i=>ProtocolRAMGeneratedWrite.fits_mono _ order (room.rank i)⟩

private theorem selection_order (n cols count base : ℕ) : base≤after g n cols count base :=
  (show base≤DescentDatedOperandSelectionRun.nextAddress (layout g cols count) 1 n a base from Nat.le_add_right ..).trans
    (DescentDatedOperandSelectionRun.reaches _ base)

theorem selection_total {n cols count base w : ℕ} (law : Fin 1 → (Fin n → Cell a) → Cell (keyWidth count))
    (args : Fin J → Fin n → Expr) (head : Fin J → Fin cols → Fin count → Expr) (m : Memory w)
    (input : ∀j i,(args j i).Fits w base) (table : ∀j f i,(head j f i).Fits w base)
    (space : after g n cols count base<2^w) : Step base (after g n cols count base) (readStage g law args head base w) m ∧
      ∀j f,(lookup g n cols count base j f).Fits w (after g n cols count base) :=by
  let L:=layout g cols count
  let js:=fun (r:Fin (J*cols))=>(finProdFinEquiv.symm r : Fin J×Fin cols)
  have run:=DescentDatedOperandSelectionRun.any L law (fun _=>0) (fun r=>args (js r).1) (fun r=>head (js r).1 (js r).2)
    (fun r i=>input (js r).1 i) (fun r i=>table (js r).1 (js r).2 i) space m
  exact ⟨⟨selection_order g ..,run.1,run.2⟩,fun j f=>
    ⟨(DescentDatedOperandMux.bank_room L (DescentDatedOperandSelectionRun.nextAddress L 1 n a base)
      space (finProdFinEquiv (j,f))).1,trivial⟩⟩

set_option maxHeartbeats 500000 in
theorem pipeline_total {w base : ℕ} (m : Memory w) (source : SourceRoom g s w base) (space : endAddress g base<2^w) :
    Step base (endAddress g base) (phase g s base w) m ∧ ∀j f,(expression g s base j f).Fits w (endAddress g base) :=by
  have e₁:=selection_order g 6 4 S₁ base
  have e₂:=selection_order g 5 1 S₂ (pathBase g base)
  have e₃:=selection_order g 9 5 S₃ (anchorBase g base)
  have e₄:=selection_order g 5 8 S₄ (rawBase g base)
  have e₅:=selection_order g 3 1 P (rankBase g base)
  have e₆ : finalBase g base≤endAddress g base:=Nat.le_add_right ..
  have h₅:=e₆.trans_lt space
  have h₄:=e₅.trans_lt h₅
  have h₃:=e₄.trans_lt h₄
  have h₂:=e₃.trans_lt h₃
  have h₁:=e₂.trans_lt h₂
  have src₁:=SourceRoom.extend g s source e₁
  have src₂:=SourceRoom.extend g s src₁ e₂
  have src₃:=SourceRoom.extend g s src₂ e₃
  have src₄:=SourceRoom.extend g s src₃ e₄
  have src₅:=SourceRoom.extend g s src₄ e₅
  have oldInput (j i) : (oldArgs g s j i).Fits w base :=by
    fin_cases i
    · exact source.origin j 0
    · exact source.prior j 0
    · exact source.origin j 1
    · exact source.origin j 2
    · exact source.prior j 1
    · exact source.prior j 2
  have oldRun:=selection_total g (oldLaw P B D C a) (oldArgs g s) s.old m oldInput source.old h₁
  let m₁:=(oldPhase g s base w).image m
  have pathInput (j i) : (pathArgs g s base j i).Fits w (pathBase g base) :=by
    fin_cases i
    · exact src₁.origin j 0
    · exact src₁.origin j 1
    · exact oldRun.2 j 3
    · exact oldRun.2 j 1
    · exact oldRun.2 j 2
  have pathRun:=selection_total g (pathLaw P D a) (pathArgs g s base) (fun _ (_ : Fin 1)=>s.path) m₁
    pathInput (fun _ _ i=>src₁.path i) h₂
  let m₂:=(pathPhase g s base w).image m₁
  have anchorInput (j i) : (anchorArgs g s base j i).Fits w (anchorBase g base) :=by
    fin_cases i
    · exact src₂.origin j 0
    · exact src₂.prior j 0
    · exact src₂.origin j 1
    · exact pathRun.2 j 0
    · exact src₂.origin j 2
    · exact ProtocolRAMGeneratedWrite.fits_mono _ e₂ (oldRun.2 j 3)
    · exact ProtocolRAMGeneratedWrite.fits_mono _ e₂ (oldRun.2 j 2)
    · exact src₂.origin j 4
    · exact src₂.mouth j 0
  have anchorRun:=selection_total g (anchorLaw P B C a) (anchorArgs g s base) s.anchor m₂ anchorInput src₂.anchor h₃
  let m₃:=(anchorPhase g s base w).image m₂
  have rawInput (j i) : (rawArgs g s base j i).Fits w (rawBase g base) :=by
    fin_cases i
    · exact src₃.origin j 0
    · exact src₃.origin j 1
    · exact ProtocolRAMGeneratedWrite.fits_mono _ e₃ (pathRun.2 j 0)
    · exact anchorRun.2 j 4
    · exact src₃.mouth j 1
  have rawRun:=selection_total g (rawLaw P (B*(C*11)) a) (rawArgs g s base) s.raw m₃ rawInput src₃.raw h₄
  let m₄:=(rawPhase g s base w).image m₃
  have rankInput (j i) : (rankArgs g s j i).Fits w (rankBase g base) :=by
    fin_cases i
    · exact src₄.origin j 0
    · exact src₄.prior j 0
    · exact src₄.origin j 1
  have rankRun:=selection_total g (localLaw P a) (rankArgs g s) (fun _ (_ : Fin 1)=>s.rank) m₄
    rankInput (fun _ _ i=>src₄.rank i) h₅
  let m₅:=(rankPhase g s base w).image m₄
  have final (j i) : (finalArgs g s base j i).Fits w (finalBase g base) :=by
    have rawAt (f : Fin 8) : (raw g base j f).Fits w (finalBase g base) :=
      ProtocolRAMGeneratedWrite.fits_mono _ e₅ (rawRun.2 j f)
    have anchorAt (f : Fin 5) : (anchor g base j f).Fits w (finalBase g base) :=
      ProtocolRAMGeneratedWrite.fits_mono _ (e₄.trans e₅) (anchorRun.2 j f)
    fin_cases i
    · exact src₅.origin j 0
    · exact src₅.prior j 0
    · exact rankRun.2 j 0
    · exact src₅.origin j 2
    · exact src₅.origin j 1
    · exact ProtocolRAMGeneratedWrite.fits_mono _ (e₃.trans (e₄.trans e₅)) (pathRun.2 j 0)
    · exact rawAt 6
    · exact rawAt 7
    · exact src₅.mouth j 1
    · exact anchorAt 0
    · exact anchorAt 1
    · exact anchorAt 2
    · exact anchorAt 4
    · exact rawAt 2
    · exact rawAt 3
    · exact rawAt 4
    · exact rawAt 5
  have bank:=DescentOperandFamilyBook.any (finalLaw g) M (finalBase g base) m₅ space
  have last : Step (finalBase g base) (endAddress g base) (bankPhase g base w) m₅:=⟨e₆,bank.1,bank.2.2.1⟩
  exact ⟨(((((oldRun.1.thenStep pathRun.1).thenStep anchorRun.1).thenStep rawRun.1).thenStep rankRun.1).thenStep last),
    fun j f=>DescentOperandFamilyBook.expr_fits (finalLaw g) M (finalBase g base) f (finalArgs g s base j) (final j) space⟩

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
