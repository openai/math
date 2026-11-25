import OAI.Computability.BorderVNP.TeamTapeInputRouteCut

/-! # Extracting the Batcher and boundary fields of the virtual blocks at a real owner

The comparison suffix has exactly forty bits per bucket unit, word bit, and cross-site
sorting layer. The two boundary records each have five words. Absent boundaries use the
canonical zero clamp. All supplied link bits are data for the actual post-pass, including
malformed encodings. A real owner with two virtual blocks uses the same cutter twice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape RAMLayout RAMBoundary TeamTapeSorting
open RAMTape.Boundary (recordBytes)

variable {d e w : ℕ}

/-- Comparator suffix in the exact layer/direction/record/bit order inspected by SitePost. -/
def comparisonBits (a : Fields d e w) (v : Word d) : List Bool :=
  (List.ofFn (incidentBits (embedFields a) v)).drop (16*w)

/-- Public size of the comparison payload, in bits. -/
def comparisonSize (d e w : ℕ) : ℕ := 40*2^e*w*(d+1).choose 2

@[simp] theorem comparisonBits_length (a : Fields d e w) (v : Word d) :
    (comparisonBits a v).length = comparisonSize d e w := by
  simp [comparisonBits, width_eq, comparisonSize]

/-- Serialized virtual-block link segment cut from the owner's interior stream. -/
def rowBits (a : Fields d e w) (v : Word d) : List Bool :=
  recordBytes (incoming a v) ++ (recordBytes (outgoing a v) ++ comparisonBits a v)

@[simp] theorem rowBits_length (a : Fields d e w) (v : Word d) :
    (rowBits a v).length = 10*w + comparisonSize d e w := by simp [rowBits]; omega

/-- Consume precisely one virtual block's routing segment. -/
def row (lane : Bool) : FiniteRoutine Port :=
  ((take lane .previous).followedBy (take lane .sent)).followedBy (take lane .comparisons)

/-- All time for the physical field cutters, including formation of their unary counters. -/
def rowTime (w L : ℕ) := 100*w+10*L+31

/-- The source advances, the three post-pass ports receive their bit streams, and all
other stacks keep their exact contents. -/
def routed (lane : Bool) (a : Fields d e w) (v : Word d) (rest : List Bool) (s : Stacks Port) : Stacks Port :=
  let prev := recordBytes (incoming a v)
  let sent := recordBytes (outgoing a v)
  let cmp := comparisonBits a v
  let x := putField s lane .previous prev (sent ++ (cmp ++ rest))
  let y := putField x lane .sent sent (cmp ++ rest)
  putField y lane .comparisons cmp rest

/-- Starting from any raw assignment, this virtual site receives exactly its predecessor,
successor and comparator payloads. A trailing second virtual block or any other fields
remain available to the owner's continuation. -/
theorem row_runs (lane : Bool) (a : Fields d e w) (v : Word d) (s : Stacks Port) (rest : List Bool)
    (hin : s source = rowBits a v ++ rest) (hw : (s widthSource).length = w)
    (hc : (s .suffixSize).length = comparisonSize d e w) (hmarks : s (.work .count) = [])
    (ht : s (.work .tmp) = []) :
    (row lane).Runs (rowTime w (comparisonSize d e w)) s (routed lane a v rest s) := by
  let prev := recordBytes (incoming a v)
  let sent := recordBytes (outgoing a v)
  let cmp := comparisonBits a v
  let x := putField s lane .previous prev (sent ++ (cmp ++ rest))
  let y := putField x lane .sent sent (cmp ++ rest)
  have h₁ := take_runs lane .previous s prev (sent ++ (cmp ++ rest))
    (by simpa [rowBits,prev,sent,cmp,List.append_assoc] using hin)
    (by simp [copies,template,prev,hw]) hmarks ht
  have h₂ := take_runs lane .sent x sent (cmp ++ rest)
    (by simp [x,putField]) (by simp [copies,template,x,putField,sent,hw])
    (by simpa [x,putField] using hmarks) (by simpa [x,putField] using ht)
  have h₃ := take_runs lane .comparisons y cmp rest
    (by simp [y,putField]) (by simp [copies,template,y,x,putField,cmp,hc])
    (by simpa [y,x,putField] using hmarks) (by simpa [y,x,putField] using ht)
  have h := (h₁.followedBy h₂).followedBy h₃
  simp only [prev,sent,cmp, Boundary.length_recordBytes,comparisonBits_length,copies] at h
  convert h using 1 <;> first | rfl | (unfold rowTime; omega)

/-- The source and public layout after routing. -/
theorem routed_frame (lane : Bool) (a : Fields d e w) (v : Word d) (rest : List Bool) (s : Stacks Port) :
    routed lane a v rest s source = rest ∧ routed lane a v rest s widthSource = s widthSource ∧
    routed lane a v rest s .suffixSize = s .suffixSize ∧
    ∀ p, routed lane a v rest s (.work p) = s (.work p) := by simp [routed, putField]

/-- Each named sorting port receives exactly its field. These equations allow the verifier
to identify its initial bank after a raw extraction, even when boundary tags are malformed. -/
theorem routed_fields (lane : Bool) (a : Fields d e w) (v : Word d) (rest : List Bool) (s : Stacks Port) :
    let r := routed lane a v rest s
    r (.post lane SitePost.previousPort) = recordBytes (incoming a v) ++ s (.post lane SitePost.previousPort) ∧
    r (.post lane SitePost.sentPort) = recordBytes (outgoing a v) ++ s (.post lane SitePost.sentPort) ∧
    r (.post lane SitePost.incidentPort) = comparisonBits a v ++ s (.post lane SitePost.incidentPort) := by
  have h₁ : SitePost.incidentPort ≠ SitePost.previousPort := by decide
  have h₂ : SitePost.incidentPort ≠ SitePost.sentPort := by decide
  have h₃ : SitePost.sentPort ≠ SitePost.previousPort := by decide
  simp [routed, putField, Field.sink, h₁, h₂, h₃, h₁.symm, h₂.symm, h₃.symm]

/-- If two virtual blocks share an owner, one table dispatches their separate field banks
in succession. -/
def twoRows : FiniteRoutine Port := (row false).followedBy (row true)

/-- The two fields of each boundary and all Batcher records reach the correct virtual banks
with the same uniform clock, leaving any unrelated routing suffix in place. -/
theorem twoRows_runs (a : Fields d e w) (first second : Word d) (s : Stacks Port) (rest : List Bool)
    (hin : s source = rowBits a first ++ (rowBits a second ++ rest)) (hw : (s widthSource).length = w)
    (hc : (s .suffixSize).length = comparisonSize d e w) (hmarks : s (.work .count) = [])
    (ht : s (.work .tmp) = []) :
    twoRows.Runs (2*rowTime w (comparisonSize d e w)) s
      (routed true a second rest (routed false a first (rowBits a second ++ rest) s)) := by
  have h₁ := row_runs false a first s _ hin hw hc hmarks ht
  obtain ⟨hsource,hwidth,hsize,hwork⟩ := routed_frame false a first (rowBits a second ++ rest) s
  have h₂ := row_runs true a second _ rest hsource (hwidth ▸ hw) (hsize ▸ hc)
    ((hwork .count).trans hmarks) ((hwork .tmp).trans ht)
  simpa only [twoRows, two_mul] using h₁.followedBy h₂

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI
