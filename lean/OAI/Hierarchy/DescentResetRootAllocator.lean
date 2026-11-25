import OAI.Hierarchy.DescentRootArena
import OAI.Hierarchy.DescentResetWindowJobs
import OAI.Hierarchy.DescentResetCatalog

namespace OAI
/-! # A fixed workspace for every private-root publisher -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local.Gather DescentSIMDLookup DescentPackedZip
open DescentSharedBookScan DescentPackedFallbackTree.Image DescentFallbackPeriod DescentFallbackRankRAM
open DescentResetHostSize Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Native instruction operands and the three measured field widths are fixed
by the compiler for each catalog page. Actual field values remain in memory. -/
structure RootTemplates (n r D L cap : ℕ) where
  good : Bool → Code r→Bool ⊕ Fin (2^n)→Σ N,RootTerms N
  exceptional : Bool → Code r×Option (Fin (2^n))→Chart×RootTerms (inputCount D L cap n r)

namespace RootTemplates
variable {n r D L cap Ht H G M w : ℕ}
abbrev arena (start : ℕ) (H G M r n D : ℕ) : RootArena :=
  ⟨start,H*DescentSharedBookScan.width r (2^n) D,H*chunks G M⟩

def Fits (ts : RootTemplates n r D L cap) (start H G M Ht w : ℕ) : Prop :=
  let A:=arena start H G M r n D
  ∀p : RootPage r (2^n),
    let i:=(rootIndex r (2^n) p).val
    let inWindow := fun {N : ℕ} (t : RootTerms N)=>
      (assembly t.tables t.reads).Fits w (A.middle i) ∧ (lookup t.menu).Fits w (A.output i)
    (match p.2 with
     | .inl (root,j)=>inWindow (ts.good p.1 root j).2
     | .inr root=>let t:=ts.exceptional p.1 root
                  (record t.1 H D (2^Ht) (Ht+2)).Fits w (A.first i) ∧ inWindow t.2) ∧
    A.output i+A.rows<2^w

def job (ts : RootTemplates n r D L cap) (start : ℕ) (fit : ts.Fits start H G M Ht w)
    (p : RootPage r (2^n)) : Shelf w := by
  let area:=arena start H G M r n D
  have counterRoom:=RootArena.le_span area.counters
  have rowRoom:=RootArena.le_span area.rows
  obtain ⟨s,kind⟩:=p
  cases kind with
  | inl u =>
    let i:=(rootIndex r (2^n) (s,.inl u)).val
    let x:=ts.good s u.1 u.2
    have spec:=(fit (s,.inl u)).1
    have room:=(fit (s,.inl u)).2
    exact Shelf.window x.2.tables x.2.reads x.2.menu (area.middle i) (area.output i) spec.1 spec.2
      (by change area.middle i+area.rows<_
          change area.output i+area.rows<_ at room
          dsimp only [RootArena.output] at room
          omega) room
  | inr u =>
    let i:=(rootIndex r (2^n) (s,.inr u)).val
    let x:=ts.exceptional s u
    have spec:=(fit (s,.inr u)).1
    have room:=(fit (s,.inr u)).2
    exact Shelf.fallback x.1 x.2.tables x.2.reads x.2.menu (area.first i) (area.middle i) (area.output i)
      spec.1 (by change area.first i+area.counters<_;change area.output i+area.rows<_ at room
                 dsimp [RootArena.output,RootArena.middle] at room;omega) spec.2.1 spec.2.2
      (by change area.middle i+area.rows<_
          change area.output i+area.rows<_ at room
          dsimp only [RootArena.output] at room
          omega) room

theorem extent (ts : RootTemplates n r D L cap) (start : ℕ) (fit : ts.Fits start H G M Ht w)
    (p : RootPage r (2^n)) :
    let i:=(rootIndex r (2^n) p).val
    (arena start H G M r n D).first i≤(ts.job start fit p).first ∧ (ts.job start fit p).limit≤(arena start H G M r n D).first (i+1) := by
  have counterRoom:=RootArena.le_span (arena start H G M r n D).counters
  have rowRoom:=RootArena.le_span (arena start H G M r n D).rows
  rcases p with ⟨s,kind⟩
  cases kind with
  | inl g =>
    dsimp only [job,Shelf.window,Shelf.seq,Shelf.ofScan]
    rw [←RootArena.end_row]
    dsimp only [RootArena.middle,RootArena.output] at *
    omega
  | inr t =>
    dsimp only [job,Shelf.fallback,Shelf.window,Shelf.seq,Shelf.ofScan]
    rw [←RootArena.end_row]
    dsimp only [RootArena.middle,RootArena.output,arena] at *
    omega

/-- One unconditional CPU execution for the entire fixed catalog. Its final
memory supports every individual physical issuer on the same initial memory. -/
theorem run (ts : RootTemplates n r D L cap) (start : ℕ) (fit : ts.Fits start H G M Ht w) (m : Memory w) :
    let jobs:=ts.job start fit
    let program:=Shelf.series (Shelf.catalog (jobs ∘ (rootIndex r (2^n)).symm))
    program.Runs m ∧
    (∀p x,(jobs p).first≤x→x<(jobs p).limit→program.image m x=(jobs p).image m x) ∧
    ∀x,x<start ∨ (arena start H G M r n D).first (Fintype.card (RootPage r (2^n)))≤x→program.image m x=m x :=
  Shelf.all_root_pages (ts.job start fit) start (arena start H G M r n D).stride (ts.extent start fit) m


/-- Number of actual per-root kernels across the two orientations. -/
theorem page_count (r Y : ℕ) :
    Fintype.card (RootPage r Y)=2*((DescentHostDirectory.codes r).card*(2+Y)+
      (DescentHostDirectory.codes r).card*(Y+1)) := by
  classical
  simp [RootPage,Code,Fintype.card_prod,Fintype.card_sum,Fintype.card_option,Nat.add_comm]

def fee (ts : RootTemplates n r D L cap) (H G M Ht : ℕ) (p : RootPage r (2^n)) : ℕ :=
  let win:=fun {N : ℕ} (t : RootTerms N)=>
    (4+H*chunks G M*(2*(assembly t.tables t.reads).work+4))+(4+44*(H*chunks G M))
  match p.2 with
  | .inl (g,j)=>win (ts.good p.1 g j).2
  | .inr ticket=>let g:=ts.exceptional p.1 ticket
              (4+H*DescentSharedBookScan.width r (2^n) D*(2*(record g.1 H D (2^Ht) (Ht+2)).work+4))+win g.2

theorem job_ticks (ts : RootTemplates n r D L cap) (start : ℕ) (fit : ts.Fits start H G M Ht w)
    (p : RootPage r (2^n)) : (ts.job start fit p).ticks=ts.fee H G M Ht p := by
  have lookupTicks (menu : Banks) :
      4+(H*chunks G M)*(2*(lookup menu).work+4)=4+44*(H*chunks G M) := by
    rw [DescentSIMDLookup.lookup_work, Nat.mul_comm 44]
  rcases p with ⟨s,g|t⟩
  · exact congrArg (_ + ·) (lookupTicks (ts.good s g.1 g.2).2.menu)
  · exact congrArg (_ + ·) (congrArg (_ + ·) (lookupTicks (ts.exceptional s t).2.menu))

/-- The total tariff counts every physical tap sheet and every padded fallback
ticket, the local branch census, all gathers, all final lookups, and schedule exit. -/
theorem clock (ts : RootTemplates n r D L cap) (start : ℕ) (fit : ts.Fits start H G M Ht w) :
    (Shelf.series (Shelf.catalog (ts.job start fit ∘ (rootIndex r (2^n)).symm))).ticks=
       (∑p,ts.fee H G M Ht p)+4 := by
  have charged:=(Shelf.issued_catalog (ts.job start fit ∘ (rootIndex r (2^n)).symm) start (arena start H G M r n D).stride
    (fun i=>by simpa only [Function.comp_apply, Equiv.apply_symm_apply, RootArena.first] using ts.extent start fit ((rootIndex r (2^n)).symm i)) (fun _=>0 : Memory w)).2.1
  rw [charged]
  apply congrArg (·+4)
  exact ((rootIndex r (2^n)).symm.sum_comp _).trans (Finset.sum_congr rfl (fun p _=>ts.job_ticks start fit p))

end RootTemplates
end
end Hierarchy.DescentSixParty.Chronology

end OAI
