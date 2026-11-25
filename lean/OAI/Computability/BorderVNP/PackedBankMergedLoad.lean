import OAI.Computability.BorderVNP.PackedBankRoundSchema
import OAI.Computability.BorderVNP.PackedBankInheritedPlacedMass

/-! # Final merged directory sizes from actual cumulative site loads

The final cell holds each site's persistent private tables and shifted records
once. Equalities bind current incident words to canonical cell cables and
external ports. These guards cost one fixed template per actual incident row.
The stored table and expanded traversal counts use the true merged ordinals.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening CellSparse CellAddresses InheritedBank Finset
open scoped Classical
open private equalityCosts from OAI.Computability.BorderVNP.PackedBankBirthCharges

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits) (state : N.Site → Site)

/-- Cumulative static syntax and expanded work each fit their owning site's
appropriate singleton physical record count. -/
private theorem site_load_le (v : N.Site) :
    (state v).staticNodes ≤ localRecords N false (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
        (fun u => u = v) ∧
      (state v).expandedLoad ≤ localRecords N true (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
        (fun u => u = v) := by
  simp [localRecords,testedWidth,boxCost,recordCost]
  omega

private theorem ordered_sum_le (ex : Bool) (test : N.Site → Prop) (sites : List N.Site)
    (nodup : sites.Nodup) (owned : ∀ v ∈ sites, test v) (f : N.Site → ℕ) (C : ℕ)
    (each : ∀ v ∈ sites, f v ≤ C*localRecords N ex (fun v => (state v).staticNodes)
      (fun v => (state v).expandedLoad) (fun u => u = v)) :
    (sites.map f).sum ≤ C*localRecords N ex (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad) test := by
  let near := univ.filter test
  have eq : test = fun u => id u ∈ near := by funext u; apply propext; simp [near]
  rw [eq,localRecords_near N ex _ _ id near,mul_sum,← List.sum_toFinset _ nodup]
  apply (sum_le_sum (s := sites.toFinset) (fun v hv => each v (List.mem_toFinset.mp hv))).trans
  exact sum_le_sum_of_subset (fun v hv => by simpa [near] using owned v (List.mem_toFinset.mp hv))

/-- With the real site sizes as auxiliary widths, the complete guessed and
supplied cell bank fits in three times the physical expanded load. -/
theorem merged_bank_capacity {C : Type} (cell : N.Site → C) (c : C)
    (hin : ∀ v, (state v).incoming = incoming N v) :
    let aux := fun v => (state v).size
    guessedSize N cell c + siteSize N cell c aux + suppliedSize N cell c ≤
      3*localRecords N true (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad) (fun v => cell v = c) := by
  apply stagedCapacity_le N cell c _ _ _ 2
  intro v
  have he := (site_load_le N state v).2
  have hi := wireCapacity_le N id v (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad)
  change incoming N v ≤ _ at hi
  change (state v).work+(state v).incoming ≤ _
  rw [hin]
  have hw : (state v).work ≤ (state v).expandedLoad := Nat.le_add_right _ _
  have hs := Nat.add_le_add (hw.trans he) hi
  simpa only [two_mul,id_eq] using hs

variable (sites : List N.Site) (offset base : N.Site → ℕ) (bindRows : N.Site → List Record)

/-- Final assembled directory on the cell's actual stable site order. -/
def mergedSiteDirectory (reports : List (List ℕ)) : Directory :=
  Directory.mergeSites sites (fun v => (state v).boxes)
    (fun v => (state v).placedRows (offset v) (base v) ++ bindRows v) reports

/-- Exact resource inequalities for the installed cell directory. Each
final tie is charged to an actual distinct incident cable or external port;
zero-width rows still consume their public descriptor. -/
theorem merged_directory_load (reports : List (List ℕ)) (test : N.Site → Prop)
    (nodup : sites.Nodup) (owned : ∀ v ∈ sites, test v) (schema : ∀ v ∈ sites, (state v).Schema)
    (slot : ∀ v ∈ sites, ∀ i < (state v).boxes.length,
      (sites.flatMap fun u => (state u).boxes).getD (base v+i) [] = (state v).boxes.getD i [])
    (shape : ∀ v ∈ sites, ∀ r ∈ bindRows v, ∃ n w a b, r = .equal n w a b)
    (count : ∀ v ∈ sites, (bindRows v).length ≤ tieRows N (fun _ => True) v) :
    let dir := mergedSiteDirectory N state sites offset base bindRows reports
    let cost := fun ex => localRecords N ex (fun v => (state v).staticNodes) (fun v => (state v).expandedLoad) test
    dir.recordMass ≤ 1026*cost false + 1 ∧ dir.boxMass ≤ cost false + 1 ∧
      Packet.storedMass dir ≤ cost false ∧ dir.visitCount ≤ cost true := by
  intro dir cost
  let pub := fun v => (state v).staticNodes
  let pay := fun v => (state v).expandedLoad
  let one (ex : Bool) (v : N.Site) := localRecords N ex pub pay (fun u => u = v)
  let tables := fun v => (state v).boxes
  let merged := sites.flatMap tables
  let rs := fun v => (state v).placedRows (offset v) (base v) ++ bindRows v
  let bs := fun v => Directory.resolvedRows merged (rs v)
  have single (v : N.Site) (hm : v ∈ sites) :
      Directory.recordNodes (rs v) ≤ 1026*one false v ∧ Directory.blockNodes (bs v) ≤ one false v ∧
      Directory.tableNodes (tables v) ≤ one false v ∧
      ((bs v).map fun b => b.copies*b.factors.length).sum ≤ one true v := by
    let s := state v
    have h := s.placed_metrics (offset v) (base v) merged (fun r hr => (schema v hm r hr).1) (slot v hm)
    dsimp only at h
    have noBox : Directory.resolvedRows merged (bindRows v) = [] := by
      apply Directory.resolvedRows_wires
      intro r hr id b c st
      obtain ⟨n,w,a,d,rfl⟩ := shape v hm r hr
      simp
    have bseq : bs v = Directory.resolvedRows merged (s.placedRows (offset v) (base v)) := by
      dsimp only [bs,rs]
      rw [Directory.resolvedRows_append,noBox,List.append_nil]
    have rowEq : Directory.recordNodes (rs v) = Directory.recordNodes s.rows + 1025*(bindRows v).length := by
      dsimp only [rs]
      rw [Directory.recordNodes_append,h.2.1,(equalityCosts _ (shape v hm)).2]
    have load : s.staticNodes ≤ one false v ∧ s.expandedLoad ≤ one true v := site_load_le N state v
    have hties : (bindRows v).length ≤ one false v := (count v hm).trans (tieRows_le N false pub pay _ v)
    have ht := Nat.mul_le_mul_left 1025 hties
    have subs : Directory.recordNodes s.rows ≤ s.staticNodes ∧ Directory.blockNodes s.directory.blocks ≤ s.staticNodes ∧
        Directory.tableNodes s.boxes ≤ s.staticNodes := by unfold Site.staticNodes; omega
    rw [bseq,rowEq,h.2.2.1,h.2.2.2]
    refine ⟨?_,subs.2.1.trans load.1,subs.2.2.trans load.1,(Nat.le_add_left _ _).trans load.2⟩
    have hr := subs.1.trans load.1
    omega
  have hpub (f : N.Site → ℕ) (h : ∀ v ∈ sites, f v ≤ one false v) : (sites.map f).sum ≤ cost false := by
    simpa using ordered_sum_le N state false test sites nodup owned f 1 (fun v hv => by simpa using h v hv)
  have hrows := ordered_sum_le N state false test sites nodup owned (fun v => Directory.recordNodes (rs v)) 1026
    (fun v hv => (single v hv).1)
  have hblocks := hpub _ (fun v hv => (single v hv).2.1)
  have htables := hpub _ (fun v hv => (single v hv).2.2.1)
  have hvis : (sites.map (fun v => ((bs v).map fun b => b.copies*b.factors.length).sum)).sum ≤ cost true := by
    simpa using ordered_sum_le N state true test sites nodup owned _ 1 (fun v hv => by
      simpa only [one_mul] using (single v hv).2.2.2)
  exact ⟨(Directory.mergeSites_recordMass sites tables rs reports).le.trans (Nat.add_le_add_right hrows _),
    (Directory.mergeSites_boxMass sites tables rs reports).le.trans (Nat.add_le_add_right hblocks _),
    (Directory.mergeSites_storedMass sites tables rs reports).le.trans htables,
    (Directory.mergeSites_visitCount sites tables rs reports).le.trans hvis⟩

end Packing.Inherited

end BorderVNP
end Computability
end OAI
