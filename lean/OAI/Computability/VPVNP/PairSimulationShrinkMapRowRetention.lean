import OAI.Computability.VPVNP.PairSimulationShrinkGatherSource
import OAI.Computability.VPVNP.PairTraversalResidentHandoff

/-!
# Retaining the shrinking map row on a chronological branch

The site counters, map IDs, first term words, and five header words read by the
shrinking map loop all lie between the level arena's base and the next level.
The later selected passes write outside this interval. The terminal prefix
preserves it as well.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords DescriptorSpace
open MotifGrid MotifBlocks MotifConversion MapResidentRows
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {w a g : ℕ} {X : State a (packingLaneBits a g)} {selection : X.ShrinkSelection B}
  {side : Bool} {m out : Memory w} {level term : Word w}

/-- Classical decidable equality on the compression state’s base vertices for retaining the
resident map rows across later passes. -/
noncomputable local instance rowRetentionDecidableBase : DecidableEq X.Base := Classical.decEq _

namespace MapRowSource

variable (R : MapRowSource X selection side m level term)

/-- The current allocation bounds the term array, both resident arrays, and
the complete group of header words consumed by the native reader. -/
structure InLevel (L : Layout) (j : ℕ) : Prop where
  head : level.val = levelStart L j
  headerEnd : level.val + 38 < levelStart L (j + 1)
  word : level.val + 38 < 2 ^ w
  firstStart : levelsBase L ≤ R.first
  rowsEnd : (ShrinkResidentLayout.layout X R.first).endAddr ≤ levelStart L (j + 1)
  termStart : levelsBase L ≤ term.val
  termEnd : term.val + (LocalHistory.shrinkMotifOrder X).length * 10 ≤ levelStart L (j + 1)

variable {L : Layout} {j : ℕ}

/-- A later worker that frames the allocated resident bank preserves every
site's counter and every ID in its ordered fiber. -/
theorem directory_of_frame (first : ℕ) (fit : (ShrinkResidentLayout.layout X first).endAddr < 2 ^ w)
    (directory : Directory X side ((ShrinkResidentLayout.layout X first).params a true w) m)
    (agree : ∀ x, first ≤ x → x < (ShrinkResidentLayout.layout X first).endAddr → out x = m x) :
    Directory X side ((ShrinkResidentLayout.layout X first).params a true w) out := by
  let D := ShrinkResidentLayout.layout X first
  let p := D.params a true w
  obtain ⟨_, _, _, _, countAt, capAt, rowAt⟩ :=
    ShrinkResidentLayout.frame X first true fit
  have ranges := D.ranges true
  have size : D.size true = D.sites * capacity a :=
    ShrinkResidentLayout.size_eq_rows X first true
  change ∀ x, D.first ≤ x → x < D.endAddr → out x = m x at agree
  obtain ⟨owner, counts, rows, stop⟩ := ranges
  constructor
  · intro site
    let i := siteIndex X site
    have index : i.val < D.sites := i.isLt
    have atCount : out ((p 3).val + i.val) = m ((p 3).val + i.val) := by
      change (p 3).val = D.counts true at countAt
      rw [countAt]
      exact agree _ (by omega) (by omega)
    exact (congrArg Fin.val atCount).trans (directory.count site)
  · intro site i
    let s := siteIndex X site
    have siteFits : s.val + 1 ≤ D.sites := s.isLt
    have width : i.val < capacity a := i.isLt.trans_eq (length_eq X side site)
    have range := Nat.mul_le_mul_right (capacity a) siteFits
    rw [Nat.succ_mul] at range
    have atRow : out ((p 5).val + s.val * (p 4).val + i.val) =
        m ((p 5).val + s.val * (p 4).val + i.val) := by
      change (p 5).val = D.rows true at rowAt
      change (p 4).val = capacity a at capAt
      rw [rowAt, capAt]
      exact agree _ (by omega) (by omega)
    exact atRow.trans (directory.idAt site i)

/-- Carry the count and ID fibers, selected term certificate and published
layout through an update that preserves the completed level. -/
noncomputable def transport (bounds : R.InLevel L j)
    (agree : ∀ x, levelsBase L ≤ x → x < levelStart L (j + 1) → out x = m x) :
    MapRowSource X selection side out level term := by
  refine { R with rows := ?_, retained := ?_, layout := ?_ }
  · exact directory_of_frame R.first R.fit R.rows fun x lo hi =>
      agree x (bounds.firstStart.trans lo) (hi.trans_le bounds.rowsEnd)
  · intro x
    have before := (ordinal X x).isLt
    have last := bounds.termEnd
    exact (agree _ (bounds.termStart.trans (Nat.le_add_right ..)) (by omega)).trans (R.retained x)
  · have hw := bounds.word
    have add : (level + 38).val = level.val + 38 := by
      change (level.val + (38 % 2 ^ w)) % 2 ^ w = _
      rw [Nat.mod_eq_of_lt (by omega : 38 < 2 ^ w), Nat.mod_eq_of_lt hw]
    have lowHead : levelsBase L ≤ level.val := bounds.head ▸ Nat.le_add_right ..
    exact (agree _ (add ▸ (lowHead.trans (Nat.le_add_right ..))) (add ▸ bounds.headerEnd)).trans
      R.layout

/-- The same level frame preserves the four consecutive descriptor operands
read before any map occurrence is dispatched. -/
theorem published (bounds : R.InLevel L j) {counts ids : Word w}
    (pub : MapResidentInputs.Published m level counts ids term 10)
    (agree : ∀ x, levelsBase L ≤ x → x < levelStart L (j + 1) → out x = m x) :
    MapResidentInputs.Published out level counts ids term 10 := by
  apply pub.retain
  intro o _ hi
  have lo : levelsBase L ≤ level.val := bounds.head ▸ Nat.le_add_right ..
  have endHead := bounds.headerEnd
  exact agree _ (lo.trans (Nat.le_add_right ..)) (by omega)

end MapRowSource
end PairSimulation.ShrinkMapImage.Registers

namespace CompressorRecords.SelectedDirectoryHistory

open BurstRAM Compression DescriptorSpace PairSimulation.LocalHistory

variable {w n : ℕ} {src : Fin n → Memory w → List (Report w) → Prop} {L : Layout}

private theorem later_frames {js : List (Fin n)} {m : Memory w} {rs : List (Report w)}
    (walk : SourceWalk src js m rs)
    (writes : ∀ i u logs, src i u logs → SourceTransport.Writes
      (fun x => x < levelsBase L ∨ levelStart L i.val ≤ x) (eventLog logs))
    {first : ℕ} (later : ∀ i ∈ js, first ≤ i.val) :
    ∀ x, levelsBase L ≤ x → x < levelStart L first → after m (eventLog rs) x = m x := by
  induction walk with
  | done => exact fun _ _ _ => rfl
  | @next i is m xs ys head tail ih =>
    intro x low high
    have upper := high.trans_le (levelStart_mono L (later i List.mem_cons_self))
    rw [SourceWalk.after_append, ih (fun k hk => later k (List.mem_cons_of_mem i hk)) x low high]
    exact SourceTransport.after_outside m (writes i m xs head) (by omega)

private theorem cut {J : Type*} {source : J → Memory w → List (Report w) → Prop}
    (pre : List J) (j : J) (post : List J) {m : Memory w} {rs : List (Report w)}
    (walk : SourceWalk source (pre ++ j :: post) m rs) :
    ∃ xs ys zs, rs = xs ++ ys ++ zs ∧ SourceWalk source pre m xs ∧
      source j (after m (eventLog xs)) ys ∧
      SourceWalk source post (after (after m (eventLog xs)) (eventLog ys)) zs := by
  induction pre generalizing m rs with
  | nil =>
    cases walk with
    | next head tail => exact ⟨[], _, _, rfl, .done _, head, tail⟩
  | cons k ks ih =>
    cases walk with
    | @next _ _ _ hs ts h tail =>
      obtain ⟨xs, ys, zs, rfl, before, sel, rest⟩ := ih tail
      refine ⟨hs ++ xs, ys, zs, by simp only [List.append_assoc], .next h before, ?_, ?_⟩
      · rwa [SourceWalk.after_append]
      · rwa [SourceWalk.after_append]

/-- Cut the chronological run at any selected level. The final memory equals
that packet's actual output at every address in the completed level region.
The source may carry additional witnesses specific to a shrinking packet. -/
theorem packet_retained (j : Fin n) {m : Memory w} {rs : List (Report w)}
    (walk : SourceWalk src (List.finRange n) m rs)
    (writes : ∀ i u logs, src i u logs → SourceTransport.Writes
      (fun x => x < levelsBase L ∨ levelStart L i.val ≤ x) (eventLog logs)) :
    ∃ pre visit rest, rs = pre ++ visit ++ rest ∧
      SourceWalk src ((List.finRange n).take j.val) m pre ∧
      src j (after m (eventLog pre)) visit ∧
      SourceWalk src ((List.finRange n).drop (j.val + 1))
        (after (after m (eventLog pre)) (eventLog visit)) rest ∧
      ∀ x, levelsBase L ≤ x → x < levelStart L (j.val + 1) →
        after m (eventLog rs) x = after (after m (eventLog pre)) (eventLog visit) x := by
  let all := List.finRange n
  have live : j.val < all.length := by simp [all]
  have decomp : all.take j.val ++ j :: all.drop (j.val + 1) = all := by
    have entry : all[j.val] = j := Fin.ext (by simp [all])
    have tail := List.drop_eq_getElem_cons live
    rw [entry] at tail
    rw [← tail, List.take_append_drop]
  obtain ⟨pre, visit, rest, logs, before, own, tail⟩ :=
    cut (all.take j.val) j (all.drop (j.val + 1)) (by rw [decomp]; exact walk)
  refine ⟨pre, visit, rest, logs, before, own, tail, ?_⟩
  rw [logs, SourceWalk.after_append, SourceWalk.after_append]
  apply later_frames tail writes
  intro i hi
  obtain ⟨k, hk, eq⟩ := List.mem_iff_getElem.mp hi
  have idx := congrArg Fin.val eq
  simp only [all, List.getElem_drop, List.getElem_finRange] at idx
  change j.val + 1 + k = i.val at idx
  omega

variable {k A : Type*} [_root_.Field k] [CommRing A] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → A} {hf : B.IsSolution f}
variable {T d : ℕ} {hT : T * S.laneBits ≤ d} {X : State (S.degreeExponent 0) d}
variable {z : (B.execute f hf T hT X).Choices}
local notation "vs" => executeLevels B f hf T hT X z
local notation "emit" => Source (B := B) (f := f) (hf := hf) (z := z) L

/-- Every packet of the selected directory walk already has the required
write bound, including its low scheduler updates. -/
theorem selected_packet_retained (j : Fin (vs).length) {m : Memory w} {rs : List (Report w)}
    (walk : SourceWalk emit (List.finRange (vs).length) m rs) :
    ∃ pre visit rest, rs = pre ++ visit ++ rest ∧
      SourceWalk emit ((List.finRange (vs).length).take j.val) m pre ∧
      emit j (after m (eventLog pre)) visit ∧
      SourceWalk emit ((List.finRange (vs).length).drop (j.val + 1))
        (after (after m (eventLog pre)) (eventLog visit)) rest ∧
      ∀ x, levelsBase L ≤ x → x < levelStart L (j.val + 1) →
        after m (eventLog rs) x = after (after m (eventLog pre)) (eventLog visit) x :=
  packet_retained j walk fun _ _ _ h => h.2

end CompressorRecords.SelectedDirectoryHistory

namespace PairSimulation.ShrinkMapImage.Registers.MapRowSource

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords DescriptorSpace
open MotifGrid MotifBlocks MotifConversion
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {w a g : ℕ} {X : State a (packingLaneBits a g)} {selection : X.ShrinkSelection B}
  {side : Bool} {level term : Word w} {L : Layout} {n : ℕ}

/-- A producing packet supplies the map-row certificate in its own post-memory.
Cutting the full walk at that packet and replaying the remaining passes carries
the certificate and its scanner operands to the last memory of the branch. -/
theorem afterWalk {src : Fin n → Memory w → List (Report w) → Prop} (j : Fin n)
    {m : Memory w} {rs : List (Report w)} (walk : SourceWalk src (List.finRange n) m rs)
    (writes : ∀ i u logs, src i u logs → SourceTransport.Writes
      (fun x => x < levelsBase L ∨ levelStart L i.val ≤ x) (eventLog logs))
    (first : ℕ)
    (produced : ∀ u visit, src j u visit →
      let out := after u (eventLog visit)
      let p := (ShrinkResidentLayout.layout X first).params a true w
      ∃ R : MapRowSource X selection side out level term, R.first = first ∧ R.InLevel L j.val ∧
        MapResidentInputs.Published out level (p 3) (p 5) term 10) :
    let out := after m (eventLog rs)
    let p := (ShrinkResidentLayout.layout X first).params a true w
    ∃ R : MapRowSource X selection side out level term, R.first = first ∧ R.InLevel L j.val ∧
      MapResidentInputs.Published out level (p 3) (p 5) term 10 := by
  obtain ⟨pre, visit, _, _, _, own, _, agree⟩ :=
    SelectedDirectoryHistory.packet_retained j walk writes
  obtain ⟨R, atFirst, bounds, pub⟩ := produced _ visit own
  exact ⟨R.transport bounds agree, atFirst, ⟨bounds.head, bounds.headerEnd, bounds.word,
    bounds.firstStart, bounds.rowsEnd, bounds.termStart, bounds.termEnd⟩,
    R.published bounds pub agree⟩

end PairSimulation.ShrinkMapImage.Registers.MapRowSource

namespace PairSimulation.TraversalResidentHandoff.Fields

open BurstRAM Compression CompressorRecords DescriptorSpace

/-- At the physical prefix exit, every map-row operand of a completed pass
still has its calendar value. The prefix table lies in the final level. -/
theorem before_final_level {w a g : ℕ} {L : Layout} {last j : ℕ} {tab : Fin L.shape.tables}
    {A : TerminalBootstrap.Header L last} {cap H : ℕ} {Y : State a g}
    {pub : Fin 11 → Word w} {calendar out : Memory w}
    (fields : Fields L last tab A cap H Y pub calendar out) (earlier : j < last) :
    ∀ x, levelsBase L ≤ x → x < levelStart L (j + 1) → out x = calendar x :=
  fun x _ hx => fields.levelFrame x
    ((hx.trans_le (levelStart_mono L earlier)).trans_le (Nat.le_add_right ..))

end PairSimulation.TraversalResidentHandoff.Fields

end VPVNP
end Computability
end OAI
