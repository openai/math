import OAI.Computability.BorderVNP.CellPacketGeometryRecordPins
import OAI.Computability.BorderVNP.CellPacketGeometrySiteSplice

/-! # Complete site-major sparse source frame for the final geometry pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open ParseBatchSort Packing.BankPacket Packing.Word VPVNP.VerifierNetwork SiteWords
variable {s C k w q b : ℕ} {σ E I Orig : Type} [Fintype σ] [Fintype E] [Fintype I]

private noncomputable def withAnchors (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) :
    Frame σ (SiteSort.Input T.atoms.length T.chunkLabels.length T.recordSlots.length q k w T.Fields) :=
  (Crossing.parallelFrame (T.sourcePins up) anchors).select (Sum.map id (fun z => (T.recordSlots.get z.1,z.2)))

/-- The static source frame now includes the additional stable sort by real final
site ID. The source layout, capacity and selection pins are fixed once. -/
noncomputable def Template.orderedPins (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C)
    (fit : T.recordSlots.length ≤ 2^b) (pad : s < 2^q) :
    Frame σ (Schema.Pins T.atoms.length T.chunkLabels.length k w T.Fields) :=
  (SiteSort.frame (T.recordRoom baseOwner) fit ⟨s,pad⟩).subst (withAnchors T up anchors)

/-- Incremental cost beyond the live source pins and the actual site-anchor frame. -/
theorem Template.orderedPins_size (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C)
    (fit : T.recordSlots.length ≤ 2^b) (pad : s < 2^q) :
    (T.orderedPins up anchors baseOwner fit pad).size ≤ (T.sourcePins up).size+anchors.size+
      2^b*(q+(w+k))+(sortedFrame b q (w+k)).size := by
  have h := SiteSort.frame_size (M := T.chunkLabels.length) (k := k) (w := w) (E := T.Fields)
    (T.recordRoom baseOwner) fit ⟨s,pad⟩
  simp only [Template.orderedPins,Frame.subst_size,withAnchors,Frame.select_size,Crossing.parallelFrame_size]
  omega

/-- Each physical word is now the word of the true final site-major directory.
Only the original public numerical fields, real site ID pins and live cell
labels are needed. The record block may contain repeated equal words. -/
theorem Template.orderedPins_values (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C)
    (fit : T.recordSlots.length ≤ 2^b) (pad : s < 2^q) (wide : 2^b ≤ 2^(w+k))
    (x : σ → Bool) (owner : Fin s → Fin C) (anchor : Fin s → Fin s)
    (linked : ∀ i, owner (anchor i) = owner i)
    (real : ∀ i, value (fun j => anchors.eval x (i,j)) = (anchor i).val) :
    let g := up.eval x
    let args := fun e => value fun j => g (.inl (.inr (.inl (e,j))))
    let fields := fun i e => value fun j => g (.inr (i,e,j))
    let D := T.directory owner args fields
    let G := D.regroup anchor
    let f := (T.orderedPins up anchors baseOwner fit pad).eval x
    (∀ i, value (fun j => g (.inl (.inl (i,j)))) = (owner i).val) → C < 2^k →
    (∀ c, (D.cellBoxes c).length < 2^w) → (∀ c, (D.cellRecords c).length < 2^w) →
    (∀ z : T.RowPin, ((tape (T.format z.1))[z.2.val]).Fits w (fields z.1)) →
    (∀ i : Fin T.atoms.length, ∀ n, T.atoms[i.val].2 = .literal n → n < 2^w) →
    (∀ i : Fin T.atoms.length, (G.words[i.val]?).map (fun z => (z.1.val,z.2)) = some (SiteSort.pair f i)) ∧
      ∀ z, f (.inr z) = (T.sourcePins up).eval x (.inr z) := by
  intro g args fields D G f keys keysFit boxes rows fits literals
  let data := (withAnchors T up anchors).eval x
  let pre := D.headers++D.boxRows++D.counts
  let raw := D.recordPieces anchor
  have left (z) : data (.inl z) = (T.sourcePins up).eval x z := by simp [data,withAnchors]
  have right (i : Fin T.recordSlots.length) (j) :
      data (.inr (i,j)) = anchors.eval x (T.recordSlots.get i,j) := by simp [data,withAnchors]
  have trueWord := (T.exists_liveFrame up T.chunkLabels.get).choose_spec.2 x owner keys keysFit boxes rows fits literals
  have nums (i : Fin T.atoms.length) :
      (pre++raw.map Prod.snd++D.reportRows)[i.val]?.map (fun z => (z.1.val,z.2)) =
        some (SiteSort.pair (fun z => data (.inl z)) i) := by
    simp only [raw,D.recordPieces_words,pre,SiteSort.pair,left]
    exact trueWord.1 i
  have ids (i : Fin T.recordSlots.length) : (raw[i.val]?).map (fun z => z.1.val) =
      some (value fun j => data (.inr (i,j))) := by
    have key := congrArg (fun ys : List (Fin s) => ys[i.val]?) (T.recordSlots_keys (cells := owner) anchor args fields)
    have bound : i.val < raw.length := (T.recordSlots_length (owner := owner) anchor args fields).symm ▸ i.isLt
    change (raw[i.val]?).map _ = _
    change (T.recordSlots.map anchor)[i.val]? = (raw.map Prod.fst)[i.val]? at key
    simp only [List.getElem?_map,List.getElem?_eq_getElem i.isLt,List.getElem?_eq_getElem bound,Option.map_some,
      Option.some.injEq] at key
    simp only [List.getElem?_eq_getElem bound,Option.map_some,right,real,List.get_eq_getElem,key]
  obtain ⟨ordered,rest⟩ := SiteSort.splice_values pre D.reportRows raw (T.recordStart_eq owner args fields)
    (T.recordSlots_length anchor args fields) (T.recordRoom baseOwner) fit pad data wide nums ids
  obtain ⟨headers,boxRows,counts,report⟩ := D.regroup_sections anchor rfl linked
  have words : pre++((List.finRange s).flatMap (fun a => raw.filterMap (fun z => if z.1=a then some z.2 else none)))++
      D.reportRows = G.words := by
    rw [D.recordPieces_sorted anchor rfl linked]
    simp only [G,Directory.words,headers,boxRows,counts,report,pre]
  have ef : f = (SiteSort.frame (T.recordRoom baseOwner) fit ⟨s,pad⟩).eval data := by
    funext z
    exact Frame.subst_eval _ _ _ _
  rw [ef]
  refine ⟨?_,fun z => (rest z).trans (left (.inr z))⟩
  intro i
  have read := ordered i
  rw [words] at read
  exact read

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
