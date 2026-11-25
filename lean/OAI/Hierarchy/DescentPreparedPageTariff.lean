import OAI.Hierarchy.DescentPreparedRootPrice
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! Both data-dependent branches at every root have a fixed native schedule and text size. -/
namespace Hierarchy.DescentSixParty.Chronology.Shelf
open DescentStaticWordColumn ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
variable {w : ℕ}

theorem catalog_names {N : ℕ} (p : Fin N→Shelf w) :
    names (series (catalog p)).program=(∑i,names (p i).program)+15 := by
  have total (xs : List (Shelf w)) : names (series xs).program=(xs.map (fun a=>names a.program)).sum+15 := by
    induction xs with
    | nil=>change names (scan w 0 0 (.lit 0))=15;rw [names_scan];rfl
    | cons x xs ih=>
      change names (x.program.seq (series xs).program)=_
      rw [names_seq,ih]
      simp [Nat.add_assoc]
  rw [total,catalog,List.map_reverse,List.sum_reverse,List.map_ofFn,List.sum_ofFn]
  rfl

theorem catalog_ticks {N : ℕ} (p : Fin N→Shelf w) :
    (series (catalog p)).ticks=(∑i,(p i).ticks)+4 := by
  rw [series_ticks,catalog,List.map_reverse,List.sum_reverse,List.map_ofFn,List.sum_ofFn]
  rfl

end Hierarchy.DescentSixParty.Chronology.Shelf

namespace Hierarchy.DescentSixParty.Chronology.RootTemplates
open DescentPacking.PackedMatch.Local.Gather DescentSIMDLookup DescentPackedZip
open DescentSharedBookScan DescentFallbackPeriod DescentFallbackRankRAM DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {n r D L cap H G M Ht w : ℕ} (ts : RootTemplates n r D L cap)

def textFee (H Ht : ℕ) (p : RootPage r (2^n)) :=
  let win:=fun {N : ℕ} (t : RootTerms N)=>102+4*(assembly t.tables t.reads).work
  match p.2 with
  | .inl (g,j)=>win (ts.good p.1 g j).2
  | .inr e =>
    let t := ts.exceptional p.1 e
    11+4*(record t.1 H D (2^Ht) (Ht+2)).work+win t.2

theorem job_names (start : ℕ) (fit : ts.Fits start H G M Ht w) (p : RootPage r (2^n)) :
    names (ts.job start fit p).program=ts.textFee H Ht p := by
  rcases p with ⟨s,g|t⟩ <;>
    simp only [job,textFee,Shelf.window,Shelf.fallback,Shelf.seq,Shelf.ofScan,NativePhase.seq,
      names_seq,names_scan,DescentSIMDLookup.lookup_work] <;> omega

theorem full_catalog (start : ℕ) (fit : ts.Fits start H G M Ht w) :
    let cat:=Shelf.series (Shelf.catalog (ts.job start fit ∘ (rootIndex r (2^n)).symm))
    cat.ticks+7*names cat.program =
      (∑p,ts.fee H G M Ht p)+4+7*((∑p,ts.textFee H Ht p)+15) := by
  intro cat
  rw [show cat.ticks=_ from ts.clock start fit,Shelf.catalog_names]
  simp only [Function.comp_apply,ts.job_names]
  rw [(rootIndex r (2^n)).symm.sum_comp]

end
end Hierarchy.DescentSixParty.Chronology.RootTemplates

namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSixParty.Chronology DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {field w : ℕ}

def Query.headerWords (q : Query) (H G M : ℕ) := 2^(q.loBits*M)+2^Nat.clog 2 (H*chunks G M)

theorem Query.job_time (q : Query) (first H G M : ℕ) (room : q.Room first H G M field w) :
    (q.job first room).ticks=(4+10*q.headerWords H G M)+(4+44*(H*chunks G M)) := by
  change (4+10*((q.literals first H G M field w).length))+(4+_*(_*(lookup _).work+4))=_
  rw [lookup_work]
  simp [Query.literals,Query.out,Query.headerWords,DescentPackedColony.Phase.Arena.Image.length,
    Nat.add_assoc,Nat.mul_comm 44]

theorem Query.job_text (q : Query) (first H G M : ℕ) (room : q.Room first H G M field w) :
    names (q.job first room).program=15*(q.headerWords H G M+1)+91 := by
  change names (((q.literals first H G M field w).program).seq (scan w _ _ (lookup _)))=_
  rw [names_seq,names_scan,(q.literals first H G M field w).hardware.2,lookup_work]
  simp [Query.literals,Query.out,Query.headerWords,DescentPackedColony.Phase.Arena.Image.length,Nat.add_assoc]

namespace Receiver
variable {D cap N n r c H G K R M h l t Ht : ℕ} (a : Receiver D cap N n r c H G K R M h l t field Ht w)
    (b : RootBook n r D (2^r) cap field)

def projectionsBill :=
  let A:=fun j=>(a.lookup j).headerWords H (2^c) M
  (∑j,((4+10*A j)+(4+44*(H*chunks (2^c) M))))+4+
    7*((∑j,(15*(A j+1)+91))+15)

theorem projections_price (space : a.PrefixFits) :
    (a.projected space).ticks+7*names (a.projected space).program=a.projectionsBill := by
  simp only [projected,Shelf.catalog_ticks,Shelf.catalog_names,jobs,Query.job_time,Query.job_text,projectionsBill]

def rootCatalogBill :=
  let ts:=a.rootedTemplates b
  (∑p,ts.fee H (2^c) M Ht p)+4+7*((∑p,ts.textFee H Ht p)+15)

def rootROMWords := b.repeatEnd a.projectionEnd H (2^c) M-a.projectionEnd+
  Fintype.card (RootPage r (2^n))*b.pageBound H (2^c) M

theorem prepared_price (space : a.PreparedFits b) :
    a.preparedTicks b space+7*names (a.preparedRoots b space)≤
      (a.retileClock+7*names a.retileCPU)+(a.chipClock+7*names a.chipCPU)+a.projectionsBill+
      ((4+10*a.rootROMWords b)+7*(15*(a.rootROMWords b+1)))+a.rootCatalogBill b := by
  have catalog:=(a.rootedTemplates b).full_catalog (a.headerEnd b) space.rows
  have prev:=a.projections_price space.toPrefixFits
  have literals:=b.literal_fee a.projectionEnd H (2^c) M w
  have tx:=(a.headerImage b).hardware.2
  change 4+10*(a.headerImage b).length≤4+10*(a.rootROMWords b) at literals
  change (a.preparedCatalog b space).ticks+7*names (a.preparedCatalog b space).program=a.rootCatalogBill b at catalog
  have amount : (a.headerImage b).length=a.headerEnd b-a.projectionEnd := rfl
  simp only [preparedTicks,preparedRoots,prefixTime,Receiver.prefix,names_seq,tx]
  rw [←amount]
  omega

end Receiver
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
