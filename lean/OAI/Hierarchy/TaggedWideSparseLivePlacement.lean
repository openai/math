import OAI.Hierarchy.TaggedWireNamedPlaces
import OAI.Hierarchy.TaggedWideSparseParallelPrefix

namespace OAI
/-! # Equality of chronological and dense named bit placements on live parallel rows -/

noncomputable section
namespace Hierarchy.WireTelescope.NamedAperture
open LinearAlgebra.SpectralBooks ChordGraph CalendarTape AdaptiveProbe
open scoped Classical BigOperators
variable {K n m : ℕ} (a : Fin n→Chord K) (b : Fin m→Chord K)
    (amt : Fin n→ℕ) (mass : Fin m→ℕ) (row : Fin n↪Fin m)
    (counts : ∀i, mass (row i)=amt i)
    (absent : ∀i, i∉Set.range row→mass i=0)
    (chord : ∀i,0<amt i→b (row i)=a i)
    (before : ∀i j,0<amt i→0<amt j→a i=a j→(i<j ↔ row i<row j))

include counts absent chord before in
/-- Zero-width and nonparallel rows do not contribute to the bit's chord offset. -/
theorem sparse_offset (i:Fin n) (hi:0<amt i) :
    TaggedShorterCommonScan.earlier (key a) amt i.val (key a i)=
      TaggedShorterCommonScan.earlier (key b) mass (row i).val (key b (row i)) :=
  TaggedShorterReportedRank.sparse_parallel_prefix (key a) (key b) amt mass row counts absent
    (fun j h=>congrArg (Fintype.equivFin _) (chord j h))
    (fun j k hj hk eq=>before j k hj hk ((Fintype.equivFin _).injective eq)) i hi

private theorem move_sides {A B : Widths K} (same:A=B)
    (x : Σe:Chord K,Fin (A e)) (y : Σe:Chord K,Fin (B e))
    (ch:x.1=y.1) (bit:x.2.val=y.2.val) (s:Bool) :
    transport same (sides A (x,s))=sides B (y,s) := by
  subst B
  have eq : x=y := by
    rcases x with ⟨x,u⟩
    rcases y with ⟨y,v⟩
    obtain rfl : x=y := ch
    rw [show u=v from Fin.ext bit]
  cases eq
  rfl

include absent chord before in
theorem sparse_half (widths : installedWidths a amt=installedWidths b mass)
    (x : Bundle amt) (s : Bool) :
    let y : Bundle mass := ⟨row x.1,x.2.cast (counts x.1).symm⟩
    transport widths (halfBits a amt (x,s))=halfBits b mass (y,s) := by
  intro y
  have live : 0<amt x.1 := Nat.zero_lt_of_lt x.2.isLt
  refine move_sides widths (chordBits a amt x) (chordBits b mass y) ?_ ?_ s
  · exact (chord_at a amt x).trans ((chord x.1 live).symm.trans (chord_at b mass y).symm)
  · rw [offset,offset]
    exact congrArg (·+x.2.val) (sparse_offset a b amt mass row counts absent chord before x.1 live)

private theorem namedBit_ext {H : Type} {cap : H→ℕ} {x y : Σu,Fin (cap u)}
    (same : x.1=y.1) (bit : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨x,i⟩
  rcases y with ⟨y,j⟩
  obtain rfl : x=y := same
  rw [show i=j from Fin.ext bit]

include absent chord before in
/-- Every live original row has its own named bit location, even on repeated chords. -/
theorem sparse_place {H : Type} (port : Fin n×Bool↪H) (livePort : LiveEnd mass↪H)
    (cap:H→ℕ) (room:∀i s, amt i≤cap (port (i,s))) (liveRoom:∀r,mass r.val.1≤cap (livePort r))
    (names:∀i (h:0<amt i) s,port (i,s)=livePort ⟨(row i,s),by simpa [counts] using h⟩)
    (widths : installedWidths a amt=installedWidths b mass) :
    place a amt port cap room =
      (transport widths).toEmbedding.trans (livePlace b mass livePort cap liveRoom) := by
  apply Function.Embedding.ext
  intro v
  obtain ⟨⟨x,s⟩,rfl⟩:=(halfBits a amt).surjective v
  simp only [Function.Embedding.trans_apply,Equiv.coe_toEmbedding]
  rw [read,sparse_half a b amt mass row counts absent chord before widths]
  simp only [livePlace,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Equiv.symm_apply_apply]
  exact namedBit_ext (names x.1 (Nat.zero_lt_of_lt x.2.isLt) s) rfl

end Hierarchy.WireTelescope.NamedAperture
end

end OAI
