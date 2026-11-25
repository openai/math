import OAI.Hierarchy.TraceReceiverMapExecution
import OAI.Hierarchy.TraceReceiverPublishedRoot
import OAI.Hierarchy.TraceReceiverPreparationRoom
import OAI.Hierarchy.GridReceiverDirectoryFrame

namespace OAI
/-! # Starting the terminal root loop at the elected tick's genuine task image -/
noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal RAM PhysicalStage HistoryContraction
open Computability.VPVNP.BurstRAM PrivateRAM HistoryStageBody.Physical TraceAdmission TraceAdmission.Resources
open scoped Fin.CommRing BigOperators Classical

variable {F Pins : Type} [Field F] [Fintype F] {w p suffix N d l : ℕ}

/-- The three columns scanned by the task publisher refer to the actual
terminal arity, relation cells, and hidden bits of the elected roots. -/
def columns (X : State d l) (L : X.Words Pins) {n : ℕ} (site : Fin n→X.Site) (value : Fin n→NodeValue F) :
    Fin 3→Fin n→ℕ := ![fun i=>L.ports.form.width (site i),fun i=>(value i).net.cells,fun i=>(value i).net.internal]

variable (X : State d l) (L : X.Words Pins) (O : X.ArchiveSites)
variable (ids : List (Fin N)) (site : Fin ids.length→X.Site) (value : Fin ids.length→NodeValue F)
variable (tag : ((Fin 3→Bool)→F)→ℕ) (banks : NavigationNodeRows.Banks) (x : TerminalWireArchive.Layout)
variable (elected scan : Memory (64*w)) (rootBase seeds heapLo heapHi : ℕ)

set_option quotPrecheck false
local notation "D" => GridReceiverBanks.tasks w
local notation "u" => receiverAge w
local notation "after" => TraceReceiverTasks.beforeImage D (TickWorkspace.base u 18+1) (GridReceiverBanks.limit w)
  (GridReceiverBanks.width w) ids.length
  (TraceAdmission.Resources.mounted (D).parent [rootBase,p,0,0] elected)

/-- The fixed sector-30 cap covers every selected prefix when each real
column value and the number of roots obey the registered pointwise charge. -/
theorem column_sum {n w : ℕ} (large : 7≤w) (count : n≤2^(3*w/5))
    (v : Fin n→ℕ) (each : ∀ i,v i≤2^(3*w/5)) : ∑ i,v i≤GridReceiverBanks.limit w := by
  have rows : ∑ i, v i≤n*2^(3*w/5) := by
    simpa [nsmul_eq_mul] using (Finset.sum_le_sum (s:=Finset.univ) (fun i _=>each i))
  have product := Nat.mul_le_mul_right (2^(3*w/5)) count
  rw [←pow_add] at product
  have span : 2^(3*w/5+3*w/5)<GridReceiverBanks.gap w :=
    Nat.pow_lt_pow_right (by decide) (by omega : 3*w/5+3*w/5<4*w)
  change ∑ i,v i≤GridReceiverBanks.gap w-1
  omega

omit [Field F] [Fintype F] in
/-- The registered actual cache bound charges all three published amounts. -/
theorem columns_paid (localPins : ∀ i,(value i).pins=L.ports.form.width (site i))
    (paid : ∀ i,(value i).net.cells+(value i).net.internal+(value i).pins≤2^(3*w/5)) :
    ∀ j i,columns X L site value j i≤2^(3*w/5) := by
  intro j i
  have h:=paid i
  have hp:=localPins i
  fin_cases j <;> simp [columns] <;> omega

omit [Field F] [Fintype F] in
/-- Second election, observed final-layer cache and three real physical
counts determine every field used by the preparation scan. -/
theorem selected_facts (prior : Memory (64*w)) (target : Word (64*w))
    (election : GridReceiverTickDirectory.Ticked (GridReceiverTickDirectory.banks w u) ids target prior elected)
    (first : elected (D).first=(O.layer.first:Word (64*w)))
    (ord : ∀ i : Fin ids.length,(O.ord (site i)).val=ids[i.val].val)
    (large : 7≤w) (age : u^10≤5*w) (countSmall : ids.length≤2^(3*w/5))
    (paid : ∀ j i,columns X L site value j i≤2^(3*w/5))
    (original : ∀ i,TraceReceiverRootRetain.Publication u (GridReceiverBanks.base w) p suffix seeds heapLo heapHi
      elected scan X L O (site i) (value i) tag banks x i (fun j=>(value j).net.cells)) :
    TraceReceiverTasks.SelectedInputFacts (GridReceiverTickDirectory.banks w u) D ids
      (TickWorkspace.base u 18+1) (GridReceiverBanks.limit w) (GridReceiverBanks.width w)
      O.layer.first (columns X L site value) elected rootBase p := by
  obtain ⟨bounds,apart⟩:=TraceReceiverTasks.grid_before_sites large age countSmall
  obtain ⟨bank,roof,slots⟩:=TraceFactorReceiver.Gather.grid_window large age
  have croom : TickWorkspace.base u 18+4<GridReceiverBanks.base w := by
    have a:=TickWorkspace.apart («u» := u) (by decide : 19<45)
    have b:=TickWorkspace.apart («u» := u) (by decide : 18<19)
    have z:=TraceAdmission.receiverAge_lower w
    have h : 8≤TickWorkspace.stride u := by
      change 8≤(2^(u^10))^4
      have four : 2^3≤2^(u^10) := Nat.pow_le_pow_right (by decide) (by omega)
      exact four.trans (Nat.le_self_pow (by decide) _)
    omega
  have id (i : Fin ids.length) : O.id (site i)=O.layer.first+ids[i.val].val := by
    change O.layer.first+(O.ord (site i)).val=_;rw [ord]
  have near (i : Fin ids.length) :
      (D).results+8*(O.layer.first+ids[i.val].val)+4<(D).current := by
    let pub:=original i
    have limit:=pub.nodesFit
    have rank:=(O.ord (site i)).isLt
    have oi:=ord i
    have wide:=(TraceReceiverRootRetain.slot_room pub.large).1
    have lo:=TickWorkspace.apart («u» := u) (by decide : 13<45)
    change TickWorkspace.base u 13+8*(O.layer.first+ids[i.val].val)+4<GridReceiverBanks.base w
    omega
  apply TraceReceiverTasks.before_selected (GridReceiverTickDirectory.banks w u) D ids
    (TickWorkspace.base u 18+1) (GridReceiverBanks.limit w) (GridReceiverBanks.width w)
    O.layer.first (columns X L site value) prior elected rootBase p election.toPublished rfl first bounds apart
    (by change GridReceiverBanks.base w≤GridReceiverBanks.base w+16;omega)
    (by change GridReceiverBanks.base w+16+4≤_;omega) bounds.firstLow bounds.selectedLow croom near
  · intro i j
    let pub:=original i
    have hp:=(congrArg HistoryStageRoot.Result.pins pub.cache.header).trans pub.localPins
    have hc:=congrArg HistoryStageRoot.Result.rows pub.cache.header
    have hh:=congrArg HistoryStageRoot.Result.bits pub.cache.header
    change (elected (TickWorkspace.base u 13+8*(O.layer.first+ids[i.val].val)+(j.val+1))).val=_
    rw [←id i]
    fin_cases j
    · exact hp
    · exact hc
    · exact hh
  · intro j
    exact column_sum large countSmall _ (paid j)

/-- Use the actual list of selected S17 rows and the columns of its computed
five-word task entries. The native loop starts exactly at the phase boundary. -/
def Source.ofSelected (order : X.OrderedHalves L)
    (ord : ∀ i : Fin ids.length,(O.ord (site i)).val=ids[i.val].val)
    (facts : TraceReceiverTasks.SelectedInputFacts (GridReceiverTickDirectory.banks w u) D ids
      (TickWorkspace.base u 18+1) (GridReceiverBanks.limit w) (GridReceiverBanks.width w)
      O.layer.first (columns X L site value) elected rootBase p)
    (large : 7≤w) (age : u^10≤5*w) (sites : ids.length≤2^(3*w/5))
    (heapMargin : heapHi≤GridReceiverBanks.base w-16)
    (edgeEnd : x.prefixBase+X.edgeCount≤GridReceiverBanks.base w)
    (original : ∀ i,TraceReceiverRootRetain.Publication u (GridReceiverBanks.base w) p suffix seeds heapLo heapHi
      elected scan X L O (site i) (value i) tag banks x i (fun j=>(value j).net.cells)) :
    Source F Pins w u p suffix ids.length d l where
  initial := after
  scan := scan
  x := x
  X := X
  L := L
  O := O
  order := order
  site := site
  value := value
  tag := tag
  banks := banks
  seeds := seeds
  heapLo := heapLo
  heapHi := heapHi
  large := large
  age := age
  jobs := calc
    5*ids.length ≤ 2^3*2^(3*w/5) := Nat.mul_le_mul (by decide) sites
    _ = 2^(3+3*w/5) := (pow_add ..).symm
    _ ≤ GridReceiverBanks.gap w := Nat.pow_le_pow_right (by decide) (by omega : 3+3*w/5≤4*w)
  pinSum := (facts.totals 0).trans (Nat.sub_le ..)
  rowFit := by
    have h:=facts.totals 1
    change (∑ i,(value i).net.cells)≤GridReceiverBanks.gap w-1 at h
    obtain ⟨_,hi,_⟩:=TraceFactorReceiver.Gather.grid_window large age
    omega
  bitFit := by
    have h:=facts.totals 2
    change (∑ i,(value i).net.internal)≤GridReceiverBanks.gap w-1 at h
    obtain ⟨_,hi,_⟩:=TraceFactorReceiver.Gather.grid_window large age
    omega
  original i := by
    apply (original i).prepared facts rfl _ heapMargin edgeEnd
    have exp : TickWorkspace.stride u=2^(u^10*4) := (pow_mul ..).symm
    have lo : TickWorkspace.base u 45<GridDescription.sector w := calc
      _ ≤ 2^6*TickWorkspace.stride u := Nat.mul_le_mul_right _ (by decide)
      _ = 2^(6+u^10*4) := by rw [exp,pow_add]
      _ < 2^(32*w) := Nat.pow_lt_pow_right (by decide) (by omega)
    change TickWorkspace.base u 45≤30*GridDescription.sector w-16
    omega
  counts := facts.counters
  task := by
    intro i
    have h:=facts.tasks i
    have id : O.id (site i)=O.layer.first+ids[i.val].val:=by
      change O.layer.first+(O.ord (site i)).val=_
      rw [ord]
    simpa [id,columns,GridReceiverBanks.tasks] using h


end Hierarchy.TraceReceiverForward

end
end OAI
