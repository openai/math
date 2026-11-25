import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHalo
import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHaloOrdinals

/-! # Linear register execution on lexicographically addressed records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryHalo
open IntegerMultiplication Code CommonRegisters Space BoxMaskedRecords

private theorem stream_size {s : Shape} {w width : ℕ} (f : Addr s w → Tree) (hf : ∀ x, size (f x) ≤ width) :
    ∀ z ∈ stream f, size z ≤ width := by
  intro z hz
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
  exact hf _

/-- The same two commands implement extension and restriction for every shape.
All record trees, including the filling record, may vary with the input.
The caller's parked data contribute additively to the visited-cell fence. -/
theorem stream_commands : ∃ R : ℕ, ∃ grow crop : Cmd, ∃ C : ℕ,
    Within R grow ∧ Within R crop ∧ ∀ (s : Shape) (hs : Good s) (w : ℕ) (fill : Tree),
    size fill ≤ w → ∀ env r base, DeckCap base r →
    let time := C * (scanVolume s.volume w + 1)
    (∀ f : Addr s s.D → Tree, (∀ x, size (f x) ≤ w) →
      BoundedFits env grow (pile 0 (send (s.header,stream f,fill)) r)
        (pile 0 (send (stream (padded fill f))) r) time (base+time) time) ∧
    (∀ g : Addr s s.E → Tree, (∀ x, size (g x) ≤ w) →
      BoundedFits env crop (pile 0 (send (s.header,stream g)) r)
        (pile 0 (send (stream (g ∘ embed hs.hDE))) r) time (base+time) time) := by
  obtain ⟨R,cmd,C,h⟩ := linear_commands
  refine ⟨R,cmd true,cmd false,C,(h true).1,(h false).1,?_⟩
  intro s hs w fill hfill env r base hr
  constructor
  · intro f hf
    have nd : (stream f).length ≤ s.volume := by
      simp only [stream,List.length_ofFn,Shape.volume]
      gcongr <;> exact hs.hDE
    let q : Packet := ⟨s,hs,w,stream f,fill,nd,stream_size f hf,hfill⟩
    have run := (h true).2 q env r base hr
    simpa only [input,output,ite_true, cost,q, expandWith_stream hs.hDE] using run
  · intro g hg
    let q : Packet := ⟨s,hs,w,stream g,fill,(by simp [stream,Shape.volume]),stream_size g hg,hfill⟩
    have run := (h false).2 q env r base hr
    simpa only [input,output,Bool.false_eq_true,ite_false,cost,q,compress_stream hs.hDE] using run

end BinaryHalo

end NearSquareRoot
end Computability
end OAI
