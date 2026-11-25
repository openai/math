import OAI.Hierarchy.TraceReceiverOwnerParents
import OAI.ThreeFlat.RAM.HistorySelectedInterior
import OAI.ThreeFlat.RAM.HistorySelectedFamily
import OAI.ThreeFlat.Diagonal.PhysicalIndividualCharge
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveChargeRun

namespace OAI
/-! # Earlier published child caches at a selected physical stage -/

namespace Hierarchy.HistorySelectedChildren
open ThreeFlat RAM Diagonal
open HistoryNodeDirectory HistoryNodeDirectory.Selected HistoryStageBody.Physical
open Diagonal.HistoryContraction Diagonal.PhysicalStage Diagonal.TickWorkspace
open RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {F Pins E : Type} [Field F]

/-- Field one of every old eight-word record names its chronological parent
in the selected run. The starting address can be the original resident bank
or its byte-for-byte mounted copy. -/
def parentVisit (bank : Banks) (num : ℕ→ℕ) (terminal : ℕ) : Run.WordVisit F Pins :=
  fun R i _ _ O _ row=>row.sites.layer.first≤terminal ∧
    ∀x,num (bank.nodes+8*O.id x+1)=row.sites.id (R.parent i x)

theorem parentVisits {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (J : Run.WordSteps Pins r) (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (bank : Banks) (num : ℕ→ℕ)
    (out : r.ArchiveRowsStored bank num h C O p) :
    r.WordVisits (parentVisit bank num (r.finalArchive h C O p).1.first) h J L C O p := by
  induction r with
  | done => trivial
  | step R next ih =>
    exact ⟨⟨((next h.1).archive_bounds (Run.tailHistory R next h) (C.2 h.1) p.1.sites p.2).1,
      out.2.1⟩,ih h.1 (Run.tailHistory R next h) (J.2 h.1) (J.1 L h.1).words
        (C.2 h.1) p.1.sites p.2 out.2.2⟩

variable {W n u : ℕ} (chron : Chronology n) (D : Directory W n)
    (rootCode : ℕ→Word W) (roots : ∀j,D.root j=rootCode (chron.root j))

include roots in
/-- At every node before the final layer, the reverse root pass assigns
exactly the same owner word to the child as to its recorded parent. -/
theorem picked_child (j p : Fin n) (early : j.val<chron.firstFinal) (parent : chron.parent j=p)
    (chosen : picked D p.val=true) : picked D j.val=true := by
  have same : D.root j=D.root p := by
    rw [roots,roots]
    apply congrArg rootCode
    conv_lhs => rw [Chronology.root]
    simp only [dite_eq_left early,parent]
  simpa only [picked,dite_eq_left j.isLt,dite_eq_left p.isLt,same] using chosen

variable (tag : ((Fin 3→Bool)→F)→ℕ) (values : Fin n→NodeValue F)
    {save : ℕ→Prop} {warm before : Memory W}

omit [Field F] in
/-- Incrementing the owner cursor changes no earlier S12 operand or S13
node header. All address conditions use the actual configurable word width. -/
theorem cached_bump (j : Fin n) (cached : (values j).Cached tag u j.val before)
    (wordRoom : base u 18<2^W) (headerRoom : base u 13+8*n≤base u 14)
    (rows : (values j).stream+4*(values j).net.cells≤base u 14)
    (ends : (values j).ext+(values j).external≤base u 14) :
    (values j).Cached tag u j.val (bump (ownerData W u) before) := by
  apply NodeValue.Cached.retain (values j) tag cached
  intro a touched
  have top : a<base u 14 := by
    rcases touched with hdr|cell|endpoint
    · have hj:=j.isLt
      change base u 13+8*j.val≤a ∧ a<base u 13+8*j.val+6 at hdr
      omega
    · omega
    · omega
  have ordered : base u 14 ≤ base u 18 :=
    Nat.mul_le_mul_right (stride u) (by decide : 14 + 1 ≤ 18 + 1)
  exact bumped_outside u before wordRoom (ne_of_lt (top.trans_le ordered))

variable {d l d' l' : ℕ} {A : State d l} (R : Move F A d' l')
    (i : Fin R.rules.count) (L : A.Words Pins) (step : R.WordStep Pins L i)
    (O : A.ArchiveSites) (charge : (R.next i).Site→ℕ) (row : R.ArchiveStep i O charge)
    (site : (R.next i).Site)
local notation "child" => fun k:Fin row.sites.layer.childCount=>row.data.child (row.sites.ord site) k

include roots in
/-- The selected stage row's authentic compact parent field and child label
supply the root and order needed by the ledger. No condition asserts a child
was selected or that its cache survives the bump. -/
theorem stage_children (bank : Banks) (out : Memory W)
    (parentAt : ∀j : Fin n,j.val<chron.firstFinal →
      out (bank.nodes+8*j.val+1)=((chron.parent j).val:Word W))
    (mounted : parentVisit bank (fun a=>(out a).val) chron.firstFinal R i L step O charge row)
    (current : Fin n) (rank : current.val=row.sites.id site)
    (ledger : Ledger u D tag values save warm current.val before) (chosen : picked D current.val=true)
    (fits : n≤2^W) (wordRoom : base u 18<2^W) (headerRoom : base u 13+8*n≤base u 14)
    (rows : ∀j,(values j).stream+4*(values j).net.cells≤base u 14)
    (ends : ∀j,(values j).ext+(values j).external≤base u 14) :
    ∀k,∃bound : child k<n,(values ⟨child k,bound⟩).Cached tag u (child k) (bump (ownerData W u) before) := by
  intro k
  have idx : child k=O.id (row.row.children site k).val := row.row.childId site k
  have early : child k<row.sites.layer.first := by
    rw [idx,row.row.contiguous]
    exact Nat.add_lt_add_left (O.ord _).isLt _
  have past : child k<current.val := by rw [rank];exact early.trans_le (Nat.le_add_right ..)
  let j : Fin n := ⟨child k,past.trans current.isLt⟩
  have beforeFinal : j.val<chron.firstFinal := early.trans_le mounted.1
  have parent : chron.parent j=current := by
    apply Fin.ext
    have fetched := congrArg Fin.val (parentAt j beforeFinal)
    rw [Fin.val_cast_of_lt ((chron.parent j).isLt.trans_le fits)] at fetched
    have addr : j.val=O.id (row.row.children site k).val := idx
    rw [addr] at fetched
    have stored : (out (bank.nodes+8*O.id (row.row.children site k).val+1)).val =
        row.sites.id (R.parent i (row.row.children site k).val) := mounted.2 _
    calc
      _ = (out (bank.nodes+8*O.id (row.row.children site k).val+1)).val := fetched.symm
      _ = row.sites.id (R.parent i (row.row.children site k).val) := stored
      _ = row.sites.id site := congrArg row.sites.id (row.row.children site k).property
      _ = current.val := rank.symm
  have selected := picked_child chron D rootCode roots j current beforeFinal parent chosen
  exact ⟨j.isLt,cached_bump tag values j (ledger.published j past selected)
    wordRoom headerRoom (rows j) (ends j)⟩

include roots in
/-- The child cache is the actual selected child network and carries the
stage-specific stream and endpoint pointers belonging to that ordinal. -/
theorem exact_children (bank : Banks) (out : Memory W)
    (parentAt : ∀j : Fin n,j.val<chron.firstFinal →
      out (bank.nodes+8*j.val+1)=((chron.parent j).val:Word W))
    (mounted : parentVisit bank (fun a=>(out a).val) chron.firstFinal R i L step O charge row)
    (current : Fin n) (rank : current.val=row.sites.id site)
    (ledger : Ledger u D tag values save warm current.val before) (chosen : picked D current.val=true)
    (fits : n≤2^W) (wordRoom : base u 18<2^W) (headerRoom : base u 13+8*n≤base u 14)
    (rows : ∀j,(values j).stream+4*(values j).net.cells≤base u 14)
    (ends : ∀j,(values j).ext+(values j).external≤base u 14)
    (forest : Forest F L.ports.form) (orig : ∀x,Fin (L.ext x)→E) (pointer : E→ℕ) (seedCount : ℕ)
    (prior : ∀k,∃bound : child k<n,values ⟨child k,bound⟩=
      NodeValue.ofSite (Run.nodeOfSite L forest orig (row.row.children site k).val) pointer
        (streamAt u seedCount (child k)) (endsAt u seedCount (child k))) :
    ∀k,(NodeValue.ofSite (Run.nodeOfSite L forest orig (row.row.children site k).val) pointer
      (streamAt u seedCount (child k)) (endsAt u seedCount (child k))).Cached tag u (child k)
        (bump (ownerData W u) before) := by
  intro k
  obtain ⟨hj,cached⟩ := stage_children chron D rootCode roots tag values R i L step O charge row site
    bank out parentAt mounted current rank ledger chosen fits wordRoom headerRoom rows ends k
  obtain ⟨_,eqn⟩ := prior k
  rw [eqn] at cached
  exact cached

end
end Hierarchy.HistorySelectedChildren

end OAI
