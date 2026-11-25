import OAI.ThreeFlat.Diagonal.PhysicalRunRootNumber
import OAI.ThreeFlat.Diagonal.NavigationRootPublication

namespace OAI
/-! # Common semantic and native group assignments for every actual cursor lane -/
namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open PhysicalStage HistoryContraction Computability.VPVNP.BurstRAM RAM.TickPhysicalABI TickPhaseModel TickChronology
open scoped Classical BigOperators Fin.NatCast
noncomputable section
variable {F : Type} [Field F] {d l W : ℕ} {A : State d l}
variable (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges)
variable (start pairs : A.Site→ℕ)

def terminalRank (v : (r.plan.finish h).Site) := r.terminalOrdinal h ((r.finalSite h).symm v)

def atRank (value : (r.plan.finish h).Site→ℕ) (i : Fin a.rootCount) :=
  ∑ v : (r.plan.finish h).Site, if terminalRank r h v=i.val then value v else 0

def rankedWork := atRank a r h (fun v=>a.nodeBank.unitWork*r.chargeAt h C start v)

def rankedPairs := atRank a r h (fun v=>∑ x : {x // r.plan.destination h x=v}, pairs x.val)

def typedRoot : RootArchive := {a with rootCount:=Fintype.card (r.plan.finish h).Site}

def groupWord (W teams : ℕ) (work pay : Fin a.rootCount→ℕ) (rank : ℕ) : ℕ :=
  ((a.scheduled (W:=W) teams work pay a.ids)[rank]?).elim 0 (fun z=>z.1.val)

/-- This definition uses the raw Plan history and physical site order, so the
same buckets serve every valid input image and every tick of the execution. -/
def runBuckets (W teams : ℕ) (clock : Clock) (bits : r.plan.History→ℕ)
    (payloadWidth span : ℕ) (groupsPos : 0<clock.groups) (site : Fin a.initialLanes→A.Site)
    (positive : 0<span) (capacity : clock.chunks*payloadWidth≤a.initialLanes*span) :
    Buckets r.plan bits clock payloadWidth a.initialLanes span where
  site := site
  group hist v :=
    let b:=a.typedRoot r hist
    let raw:=b.groupWord W teams (b.rankedWork r hist C start) (b.rankedPairs r hist pairs) (terminalRank r hist v)
    ⟨raw%clock.groups,Nat.mod_lt _ groupsPos⟩
  positive:=positive
  fit:=capacity

variable (O : A.ArchiveSites) (p : r.ArchivePath h C O)
variable (card : a.rootCount=(r.finalArchive h C O p).1.count)

include C O p card in
theorem typedRoot_eq : a.typedRoot r h=a := by
  have ct : Fintype.card (r.plan.finish h).Site=a.rootCount :=
    (Fintype.card_congr (terminalOrder a r h C O p card).symm).trans (Fintype.card_fin _)
  unfold typedRoot;rw [ct]

private theorem ranked_iff (fit : r.FinalNumbered h C O p) (u : (r.plan.finish h).Site) (i : Fin a.rootCount) :
    terminalRank r h u=i.val ↔ u=runRootSite a r h C O p card i := by
  have number (v : (r.plan.finish h).Site) : (a.runRootId r h C O p card v).val=terminalRank r h v :=
    fit ((r.finalSite h).symm v)
  constructor
  · intro eqv
    have id : a.runRootId r h C O p card u=i := Fin.ext ((number u).trans eqv)
    rw [←id,rootSite_rank]
  · rintro rfl;rw [←number];simp [runRootId,runRootSite]

private theorem atRank_actual (fit : r.FinalNumbered h C O p) (value : (r.plan.finish h).Site→ℕ)
    (i : Fin a.rootCount) : a.atRank r h value i=value (runRootSite a r h C O p card i) := by
  unfold atRank
  simp_rw [ranked_iff a r h C O p card fit]
  simp

/-- The caller can choose both runtime operands from the decoded mathematical
history, before the chronological replay has returned its private memory. -/
def typedHeader : NavigationHeader :=
  ⟨a.initialLanes,a.rootCount,∑ i : Fin a.rootCount,a.rankedWork r h C start i,a.stageCount⟩

def typedOwner (width slots : ℕ) : ℕ → Word width × Word width :=
  fun i=>((a.scheduled (W:=width) slots (a.rankedWork r h C start) (a.rankedPairs r h pairs) a.ids)[i]?).getD (0,0)

theorem ranked_observables (m : Memory W) (rows : r.ArchiveRowsStored a.nodeBank (fun z=>(m z).val) h C O p)
    (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O p).1.first)
    (numbered : r.FinalNumbered h C O p) (slots : ℕ) :
    let N:=nodesOfRun a r h C O p m rows zero first card start pairs
    (a.rankedWork r h C start=N.work) ∧ (a.rankedPairs r h pairs=N.pairs) ∧
    (a.typedHeader r h C start=a.summaryHeader N) ∧
    (a.typedOwner r h C start pairs W slots=a.scheduledOwner N slots) := by
  intro N
  have work : a.rankedWork r h C start=N.work:=funext fun j=>
    atRank_actual a r h C O p card numbered _ j
  have pay : a.rankedPairs r h pairs=N.pairs:=funext fun j=>
    atRank_actual a r h C O p card numbered _ j
  refine ⟨work,pay,?_,?_⟩
  · unfold typedHeader summaryHeader workBefore
    rw [work,←Fin.sum_univ_eq_sum_range]
    simp only [countWord_work]
  · exact congrArg₂ (fun (times fees : Fin a.rootCount → ℕ) (i : ℕ) =>
        ((a.scheduled (W:=W) slots times fees a.ids)[i]?).getD (0,0)) work pay

private theorem groupWord_eq (N : Nodes a) (teams : ℕ) (sched : ScheduleFacts a W teams N.work N.pairs a.ids)
    (fits : a.groups<2^W) (i : Fin a.rootCount) :
    a.groupWord W teams N.work N.pairs i.val=(a.groupOf N teams sched fits i).val := by
  let labels:=a.scheduled (W:=W) teams N.work N.pairs a.ids
  have inside : i.val<labels.length := by
    rw [show labels.length=a.ids.length from scheduled_length a teams N.work N.pairs a.ids sched]
    simp [ids]
  change (labels[i.val]?).elim 0 _=_
  rw [List.getElem?_eq_getElem inside];rfl

/-- The exact home equality consumed by the last publication procedure. -/
theorem runBuckets_home (m : Memory W) (rows : r.ArchiveRowsStored a.nodeBank (fun z=>(m z).val) h C O p)
    (zero : O.layer.first=0) (first : a.firstFinal=(r.finalArchive h C O p).1.first)
    (numbered : r.FinalNumbered h C O p) (teams : ℕ) (clock : Clock) (bits : r.plan.History→ℕ)
    (payloadWidth span : ℕ) (groupsPos : 0<clock.groups) (site : Fin a.initialLanes→A.Site)
    (initial : ∀i,O.id (site i)=i.val) (positive : 0<span)
    (capacity : clock.chunks*payloadWidth≤a.initialLanes*span) (ng : a.groups=clock.groups)
    (lanes : a.initialLanes≤a.firstFinal+a.rootCount) (fits : a.groups<2^W)
    (schedule : ScheduleFacts a W teams
      (nodesOfRun a r h C O p m rows zero first card start pairs).work
      (nodesOfRun a r h C O p m rows zero first card start pairs).pairs a.ids)
    (i : Fin a.initialLanes) :
    let N:=nodesOfRun a r h C O p m rows zero first card start pairs
    let T:=a.runBuckets r C start pairs W teams clock bits payloadWidth span groupsPos site positive capacity
    finCongr ng (a.groupOf N teams schedule fits (N.laneRoot lanes i))=
      T.group h (r.plan.destination h (T.site i)) := by
  let N:=nodesOfRun a r h C O p m rows zero first card start pairs
  let assign:=a.groupOf N teams schedule fits
  let target:=r.plan.destination h (site i)
  let root:=a.runRootId r h C O p card target
  have work : a.rankedWork r h C start=N.work := funext fun j=>
    atRank_actual a r h C O p card numbered _ j
  have pay : a.rankedPairs r h pairs=N.pairs := funext fun j=>
    atRank_actual a r h C O p card numbered _ j
  have ord : root.val=terminalRank r h target := numbered ((r.finalSite h).symm target)
  have home : assign (N.laneRoot lanes i)=assign root :=
    group_of_destination a r h C O p card m rows zero first start pairs site initial lanes assign i
  have ct : Fintype.card (r.plan.finish h).Site=a.rootCount :=
    (Fintype.card_congr (terminalOrder a r h C O p card).symm).trans (Fintype.card_fin _)
  have ba : a.typedRoot r h=a := by unfold typedRoot;rw [ct]
  apply Fin.ext
  change (assign (N.laneRoot lanes i)).val=(a.typedRoot r h).groupWord W teams
    ((a.typedRoot r h).rankedWork r h C start) ((a.typedRoot r h).rankedPairs r h pairs)
    (terminalRank r h target)%clock.groups
  rw [ba,home,work,pay,←ord,groupWord_eq a N teams schedule fits root]
  exact (Nat.mod_eq_of_lt (show (assign root).val<clock.groups from (assign root).isLt.trans_eq ng)).symm

end

end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.Archive
open PhysicalStage
noncomputable section
variable {F : Type} [Field F] (A : Archive) (B : PhysicalStage.Block F) {k : ℕ}
    (hk : 2≤k) (low offsets slots : ℕ)

/-- The clipped input lanes occupy cursor position zero in the original numbered site array. -/
def firstLaneSite (i : Fin (2^k)) : (B.cursorState hk low offsets slots).Site :=
  (⟨0,by omega⟩,finFunctionFinEquiv.symm i)

theorem firstLaneSite_id (axes : k=A.axes) (lanes : A.remainingLanes=2^k)
    (zero : A.cursor.node=0) (i : Fin (2^k)) :
    (A.cursorSeedSites B hk low offsets slots axes lanes).id (firstLaneSite B hk low offsets slots i)=i.val := by
  have address := A.cursor_zero_id B hk low offsets slots axes lanes (finFunctionFinEquiv.symm i)
  rw [zero, Nat.zero_add] at address
  exact address.trans (congrArg Fin.val (finFunctionFinEquiv.apply_symm_apply i))

end

end ThreeFlat.Diagonal.NavigationPass.Archive

namespace ThreeFlat.Diagonal.NavigationPass.Parameters
open PhysicalStage Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows NavigationDirectory TickPhaseModel TickChronology
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F)
variable (u rem low stride cells tableOffset tariff : ℕ) (shape : PhysicalPinsExpr.Shape)
local notation "p" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "P" => B.repeat (u^8)
local notation "k" => ((P).charge+rem)
local notation "off" => (1+((k+low)+(k+low)))
local notation "A" => (p).archive (2^B.exponent 0) W
local notation "ss" => (P).directory rem (p).axes
local notation "n" => (p).nodeArchive A ss W
local notation "root" => (p).rootArchive A n ss W
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "C" => B.charges (u^8) rem X
local notation "O" => (A).cursorSeedSites B hk low off cells rfl rfl
local notation "start" => B.seedWork hk low off cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low off cells (2*shape.halfBits)
local notation "bits" => (R).readTerminal (fun Y=>Y.widthSum)
variable (clock : Clock) (groups : 0<clock.groups) (total : clock.chunks=2*shape.chunks)
    (cover : 2*shape.halfBits ≤ 2^(((B.repeat (u^8)).charge+rem)+low))

/-- The physical clock uses one group-slot for each team and evaluation tick. -/
def cursorBuckets : Buckets (R).plan bits clock shape.bits (2^k) (2^low) :=
  (root).runBuckets R C start pay W (clock.evaluateTicks*2^(u^3)) clock bits shape.bits (2^low) groups
    (Archive.firstLaneSite B hk low off cells) (Nat.two_pow_pos _) (by
      change clock.chunks*shape.bits≤2^k*2^low
      rw [total,←Nat.pow_add,Nat.mul_assoc];exact cover)

theorem cursorBuckets_home (hist : (R).plan.History) (path : (R).ArchivePath hist C O) (m : Memory W)
    (rs : (R).ArchiveRowsStored (root).nodeBank (fun z=>(m z).val) hist C O path)
    (zero : (O).layer.first=0) (first : (root).firstFinal=((R).finalArchive hist C O path).1.first)
    (card : (root).rootCount=((R).finalArchive hist C O path).1.count) (numbered : (R).FinalNumbered hist C O path)
    (ng : (root).groups=clock.groups) (lanes : (root).initialLanes≤(root).firstFinal+(root).rootCount) (word : (root).groups<2^W)
    (schedule : RootArchive.ScheduleFacts root W (clock.evaluateTicks*2^(u^3))
      (RootArchive.nodesOfRun root R hist C O path m rs zero first card start pay).work
      (RootArchive.nodesOfRun root R hist C O path m rs zero first card start pay).pairs (root).ids)
    (i : Fin (2^k)) :
    let ns:=RootArchive.nodesOfRun root R hist C O path m rs zero first card start pay
    let T:=cursorBuckets B u rem low stride cells tableOffset tariff shape hk clock groups total cover
    finCongr ng ((root).groupOf ns (clock.evaluateTicks*2^(u^3)) schedule word (ns.laneRoot lanes i))=
      T.group hist ((R).plan.destination hist (T.site i)) :=
  RootArchive.runBuckets_home root R hist C start pay O path card m rs zero first numbered _ clock bits _ _ groups _
    ((A).firstLaneSite_id B hk low off cells rfl rfl zero) _ _ ng lanes word schedule i

end

end ThreeFlat.Diagonal.NavigationPass.Parameters

end OAI
