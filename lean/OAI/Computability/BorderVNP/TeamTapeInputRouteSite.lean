import OAI.Computability.BorderVNP.TeamTapeInputRouteGeometry
import OAI.Computability.BorderVNP.TeamTapeSortingLayout

/-! # A fully populated physical team sorting bank from the two retained bit streams

The public literal supplies the virtual identifier; the interior stream supplies the links.
The record array is the actual closed buffer on the real block and the all-empty encoding
on a padding block. The resulting bank is exactly the one on which the sorter's time and
count theorems apply.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape RAMLayout RAMSerialization RAMBoundary TeamTapeSorting
open RAMTape.Boundary (recordBytes blockBytes)

variable {d e w : ℕ}

/-- Bank of public sorter geometry immediately before the message fields are routed. -/
theorem installed_raw (lane : Bool) (H w : ℕ) (v : Word d) (tail : List Bool) (s : Stacks Port)
    (hz : ∀ i, s (.post lane i) = []) :
    installed lane w H v tail s ∘ Port.post lane =
      SitePost.rawBank d w (4*H) (wordBits v) (blockContents lane (s closedBlock)) [] [] [] [] := by
  funext i
  rcases i with (c | (((r|z)|o)|u)) | extra <;> cases lane <;>
    first | (cases c <;> first | rfl | exact hz _) | (cases r <;> first | rfl | exact hz _) |
      (cases z <;> first | rfl | exact hz _) | (cases o <;> first | rfl | exact hz _) |
      (cases u <;> rfl) | (cases extra <;> first | rfl | exact hz _)

/-- Stage one virtual bank, reading its index from the literal and its link bytes from
the interior tape. This is a single physical table shared by all widths and indices. -/
def site (lane : Bool) : FiniteRoutine Port := (geometry lane).followedBy (row lane)

/-- Physical poststate of one complete bank loader. -/
def siteOutput (lane : Bool) (a : Fields d e w) (v : Word d) (tail rest : List Bool)
    (s : Stacks Port) : Stacks Port :=
  routed lane a v rest (installed lane w (2^e) v tail s)

/-- Both input pointers advance and no other public geometry or scratch changes. -/
theorem siteOutput_frame (lane : Bool) (a : Fields d e w) (v : Word d) (tail rest : List Bool)
    (s : Stacks Port) :
    let t := siteOutput lane a v tail rest s
    t metadata = tail ∧ t source = rest ∧ t widthSource = s widthSource ∧ t bucket = s bucket ∧
      t .suffixSize = s .suffixSize ∧ t closedBlock = s closedBlock ∧
      (∀ p, t (.work p) = s (.work p)) ∧ ∀ p, t (.post (!lane) p) = s (.post (!lane) p) := by
  intro t
  have hx := routed_frame lane a v rest (installed lane w (2^e) v tail s)
  refine ⟨?_,hx.1,hx.2.1,?_,hx.2.2.1,?_,fun p => hx.2.2.2 p,?_⟩
  · exact (routed_other lane a v rest _ _ (by decide) (by simp) (by simp) (by simp)).trans
      (by simp [installed])
  · exact routed_other lane a v rest _ _ (by decide) (by simp) (by simp) (by simp)
  · exact routed_other lane a v rest _ _ (by decide) (by simp) (by simp) (by simp)
  · intro p
    have h := routed_other lane a v rest (installed lane w (2^e) v tail s) (.post (!lane) p)
      (by simp) (by cases lane <;> simp) (by cases lane <;> simp) (by cases lane <;> simp)
    exact h.trans (by cases lane <;> simp [installed])

/-- Complete deterministic virtual-site loading, with the literal and interior inputs
still containing all their unused suffixes. -/
theorem site_runs (lane : Bool) (a : Fields d e w) (v : Word d) (s : Stacks Port) (tail rest : List Bool)
    (hid : s metadata = Evaluator.InputBank.fieldBits (wordBits v) ++ tail)
    (hin : s source = rowBits a v ++ rest) (hw : (s widthSource).length = w)
    (hH : (s bucket).length = 2^e) (hc : (s .suffixSize).length = comparisonSize d e w)
    (hcount : s (.work .count) = []) (ht : s (.work .tmp) = []) (hz : ∀ i, s (.post lane i) = []) :
    (site lane).Runs (geometryTime d w (2^e) (s closedBlock).length + rowTime w (comparisonSize d e w))
      s (siteOutput lane a v tail rest s) := by
  have geom := geometry_runs lane w (2^e) v s tail hid hw hH ht hz
  have links := row_runs lane a v (installed lane w (2^e) v tail s) rest hin hw hc hcount ht
  exact geom.followedBy links

/-- The two raw routed endpoint words and the complete padded block occupy the very ports
used by the original physical post-pass theorem. -/
theorem siteOutput_raw (lane : Bool) (a : Fields d e w) (v : Word d) (s : Stacks Port)
    (tail rest : List Bool) (hz : ∀ i, s (.post lane i) = []) :
    siteOutput lane a v tail rest s ∘ Port.post lane = SitePost.rawBank d w (4*2^e)
      (wordBits v) (blockContents lane (s closedBlock)) (comparisonBits a v) []
      (recordBytes (incoming a v)) (recordBytes (outgoing a v)) :=
  routed_post_bank lane a v rest _ _ _ _ _ (installed_raw lane (2^e) w v tail s hz)

private theorem vacant_bytes (hw : 2 ≤ w) :
    blockBytes (List.ofFn (SortReplay.emittedBlock hw e [])) =
      List.replicate (blockBits (2^e) w) false := by
  rw [SortReplay.emittedBlock_bytes]
  apply List.ext_getElem
  · simp [blockBits]
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_replicate]
    obtain ⟨⟨j,t⟩,he⟩ := finProdFinEquiv.surjective (⟨i,by simpa using hi⟩ : Fin ((4*2^e*5)*w))
    rw [← he, Format.encode, arrayBits_at]
    change RAMSerialization.wordBits w (0 : Word w) t = false
    exact wordBits_zero t

/-- The primary bank carries the physically closed input records. The padded virtual bank
contains canonical empty slots even when the primary block has nonzero records. -/
theorem siteOutput_prestate (hw : 2 ≤ w) (lane : Bool) (a : Fields d e w) (v : Word d)
    (s : Stacks Port) (tail rest : List Bool) (rs : List (WordRecord w))
    (hb : s closedBlock = List.ofFn ((blockFormat (2^e) hw).encode (RecordBuffer.slots (2^e) rs)))
    (hz : ∀ i, s (.post lane i) = []) :
    siteOutput lane a v tail rest s ∘ Port.post lane =
      SitePost.prestate v (incoming a v) (outgoing a v)
        (SortReplay.emittedBlock hw e (if lane then [] else rs), []) (comparisonBits a v) := by
  rw [siteOutput_raw _ _ _ _ _ _ hz, SitePost.prestate_eq_raw]
  refine congrArg₂ (fun slots bytes => SitePost.rawBank d w slots (wordBits v) bytes (comparisonBits a v) []
    (recordBytes (incoming a v)) (recordBytes (outgoing a v))) (record_width e).symm ?_
  cases lane with
  | false => simp [blockContents,hb,SortReplay.emittedBlock_bytes]
  | true => simp [blockContents,hb,vacant_bytes,blockBits]

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI
