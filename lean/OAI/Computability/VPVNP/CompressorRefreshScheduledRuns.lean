import OAI.Computability.VPVNP.CompressorRefreshLevelRecipe
import OAI.Computability.VPVNP.CompressorRecordRefreshBuild
import OAI.Computability.VPVNP.CompressorSourceWalk

/-!
# Source runs of the physical degree-refresh calendar

The external segments, internal term choice, selected supplies, expander
records and final lane-zero outputs run in order in the same memory. The
decomposition identifies every report of the complete refresh with the
corresponding finite recipe's source table, operand bank and tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords

open BurstRAM Schedule Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry

open SourceWalk (after_append)

namespace PortRefresh.Scheduled

open LevelRecipe NewSlots Allocation
open scoped Fin.CommRing

variable {w a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (c : DyadicRefreshChoice X E hdH conn F)
  (ties : Fin t ≃ Tie (2^a)) (old : IncidenceDirectory w) (start stride : ℕ)

/-- Compile the input and refreshed degree exponents, expander degree, tie count, record stride
and selector bit count into the stage recipe. -/
abbrev shape := (⟨a,a₀,dH,t,stride,F.selectorBits⟩ : LevelRecipe.Shape)
local notation "s" => shape (t := t) E hdH conn F stride
local notation "J" => Stage s
local notation "P" => Allocation.plan X a₀ dH t stride start
local notation "term" => TermWorker.motifPass F ties (2^a*dH)
local notation "publicData" => TermWorker.motifData F ties finProdFinEquiv.symm w

/-- Actual checked instruction budget of each worker. -/
def fuel {shape₀ : LevelRecipe.Shape} (hd : shape₀.dH+1 ≤ shape₀.degree) (termCap : ℕ) : Stage shape₀ → ℕ
  | .gather => 24
  | .bundles => 28
  | .offsets => 33
  | .demand _ => 26
  | .term => termCap
  | .supply => 34
  | .rom _ => 12
  | .slot j => 1+(code (kindOf ((refreshSlots hd).symm j))).length
  | .base => 29

/-- Actual per-block selection tapes for the term worker. Every other stage receives an empty
choice list for each cursor it scans. -/
def tapes (j : J) : List (List Bool) :=
  match j with
  | .term => List.ofFn (blockTapes E hdH conn F X c w)
  | _ => List.replicate (j.limit X start - j.first) []

/-- A report sequence from this recipe's actual table, at its declared
initial cursor and using the original admitted branch. -/
def Source (cap : ℕ) (j : J) (m : Memory w) (rs : List (Report w)) : Prop :=
  let data := fun z ↦ j.nativeBank hd E ties X start old publicData (Fin.cast (j.worker_params hd term) z)
  let M := ((j.worker hd term).table.instantiate w data).program
  runSegment M (fuel hd cap j) (some (NewSlots.word j.first)) m
    (tapes (w := w) X E hdH conn F c start stride j) = some rs

local notation "src" => Source X E hdH conn F hd c ties old start stride

private theorem demands (cap : ℕ) {ks : List (Fin t)} {m : Memory w} {rs}
    (h : DemandScan.Runs (DemandScan.words (r := 2^g) ties ((P).scratch w) (NewSlots.word (P).demand))
      (P).blocks ks m rs) : SourceWalk (src cap) (ks.map Stage.demand) m rs := by
  induction h with
  | nil => exact .done _
  | cons i hh ht ih => exact .next hh ih

private theorem slots (cap : ℕ) {ks : List (Fin (2^a₀))} {m : Memory w} {rs}
    (h : AllSlots.Runs (fun i ↦ kindOf ((refreshSlots hd).symm i))
      (fun i ↦ AllSlots.words (2^a) (2^g) ((P).inputs w) ((P).output w) ((refreshSlots hd).symm i))
      (P).sites ks m rs) : SourceWalk (src cap) (ks.map Stage.slot) m rs := by
  induction h with
  | nil => exact .done _
  | cons i hh ht ih => exact .next hh ih

private theorem rom (cap : ℕ) (is : List (Fin (2^a*dH))) (m : Memory w) :
    SourceWalk (src cap) (is.map Stage.rom) m (is.map (ExpanderROM.report E ((P).inputs w))) := by
  induction is generalizing m with
  | nil => exact .done _
  | cons i is ih =>
    change SourceWalk _ _ _ ([ExpanderROM.report E ((P).inputs w) i] ++ _)
    apply SourceWalk.next _ (ih _)
    change runSegment _ 12 (some (NewSlots.word i.val)) m (List.replicate (i.val+1-i.val) []) = _
    rw [show i.val+1-i.val = 1 by omega]
    simp only [List.replicate_succ,List.replicate_zero,runSegment,ExpanderROM.report]
    rfl

set_option maxHeartbeats 1400000 in
/-- The complete native refresh refines the fixed ordered recipe list. -/
theorem sources (cap : ℕ) (L : Allocation.PrepareLayout X old a₀ dH t stride start)
    (m : Memory w) (rs : List (Report w))
    (h : Build.Run X E hdH conn F hD hd c ties old start stride cap L m rs) :
    SourceWalk (src cap) (LevelRecipe.order s) m rs := by
  obtain ⟨pre,terms,post,rfl,prep,hrTerm,finish⟩ := h
  obtain ⟨rg,rd,re,ds,ext,demandsRun,_,rfl⟩ := prep
  obtain ⟨hg,hb,he,_⟩ := ext
  let m₀ := after (after (after m (eventLog rg)) (eventLog rd)) (eventLog re)
  let m₁ := after m₀ (eventLog ds)
  let m₂ := after m₁ (eventLog terms)
  simp only [after_append] at finish hrTerm
  obtain ⟨su,roms,os,bs,rfl,hs,hrom,ho,hbase⟩ := finish
  have hw₀ : SourceWalk (src cap) [.gather,.bundles,.offsets] m (rg++rd++re) := by
    rw [List.append_assoc]
    exact SourceWalk.next hg (SourceWalk.next hb (SourceWalk.singleton he))
  have hw₁ := demands X E hdH conn F hd c ties old start stride cap demandsRun
  have hwTerm : src cap .term m₁ terms := by
    have haddr : termAddresses (NewSlots.word (bits := w) (P).demand) (NewSlots.word (bits := w) (P).term)
        stride t = ![NewSlots.word (P).demand,NewSlots.word t,NewSlots.word (P).term,NewSlots.word stride] := by
      funext i; fin_cases i <;> apply Fin.ext <;> simp [termAddresses,NewSlots.word]
    let bank := publicData ![NewSlots.word (P).demand,NewSlots.word t,NewSlots.word (P).term,NewSlots.word stride]
    have sameBank : (fun z ↦ bank (Fin.cast ((.term : J).worker_params hd term) z)) = bank :=
      funext fun z ↦ congrArg bank (Fin.ext rfl)
    change runSegment ((term).table.instantiate w
      (fun z ↦ bank (Fin.cast ((.term : J).worker_params hd term) z))).program cap (some 0) m₁
        (List.ofFn (blockTapes E hdH conn F X c w)) = some terms
    have eqRun := congrArg (fun data : Fin (term).params → BurstRAM.Word w ↦
      runSegment ((term).table.instantiate w data).program cap (some 0) m₁
        (List.ofFn (blockTapes E hdH conn F X c w))) sameBank
    exact eqRun.trans (by simpa only [termRun,TermWorker.program,haddr,bank] using hrTerm)
  have hw₂ : SourceWalk (src cap) [.term,.supply] m₁ (terms++su) :=
    SourceWalk.next hwTerm (SourceWalk.singleton hs)
  have hrom' := ExpanderROM.schedule_run E ((P).inputs w) 0 (after m₂ (eventLog su)) (List.finRange (2^a*dH))
  have er : roms = (List.finRange (2^a*dH)).map (ExpanderROM.report E ((P).inputs w)) := Option.some.inj (hrom.symm.trans hrom')
  have hw₃ := rom X E hdH conn F hd c ties old start stride cap (List.finRange _) (after m₂ (eventLog su))
  rw [← er] at hw₃
  have hw₄ := slots X E hdH conn F hd c ties old start stride cap ho
  have hsize : BaseOutput.baseCount (dyadicRefreshNext X E hdH conn F hD hd c) =
      Fintype.card X.Base * 2^a * 2^a₀ := by
    change Fintype.card (X.Base × Fin (2^a)) * 2^a₀ = _
    simp only [Fintype.card_prod,Fintype.card_fin]
  rw [hsize] at hbase
  have hw₅ : SourceWalk (src cap) [.base] _ bs := SourceWalk.singleton hbase
  have htail := hw₃.append (hw₄.append hw₅)
  have hmiddle := hw₂.append (by simpa only [after_append] using htail)
  have hdem := hw₁.append hmiddle
  have whole := hw₀.append (by simpa only [after_append] using hdem)
  simpa only [LevelRecipe.order,List.append_assoc] using whole

end PortRefresh.Scheduled
end CompressorRecords

end

end VPVNP
end Computability
end OAI
