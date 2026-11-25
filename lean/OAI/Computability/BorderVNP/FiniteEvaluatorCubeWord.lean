import OAI.Computability.BorderVNP.FiniteEvaluatorCellWeight
import OAI.Computability.VPVNP.RAMTapeWordSlice

/-! # One fixed deck word for each selected cube field element

A deck entry encodes one binary count digit for every field element. Exactly one
digit is set. A sufficiently wide physical word is the complete compact packet,
including its terminator, so the same scalar routine used at cells can multiply
one actual selected cube entry in a single word read.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeWord

open VPVNP BurstRAM RoutingISA FiniteScalarRounds FiniteScalarLibrary FieldProcessor
open scoped BigOperators Classical
open private frame_length from OAI.Computability.BorderVNP.RoutingISACompactFrame

variable {F : Type*} [Field F] [Fintype F]

/-- The single count digit of the selected field element. -/
noncomputable def indicator (v : F) : Index F → Fin 1 → Bool := fun i _ => decide (i = Fintype.equivFin F v)

/-- Integer stored in the common fixed cube table. It is independent of the
runtime RAM word width, number of packets, and batch size. -/
noncomputable def encode (v : F) : ℕ := TapeWord.value (CompactFrame.frameBits (stream F (indicator v)))

omit [Field F] in
/-- The fixed deck word uses no more than the framed single row of field IDs. -/
theorem encode_lt (v : F) : encode v < 2^(2*Fintype.card F+1) := by
  simpa only [encode,frame_length,stream_length,one_mul] using TapeWord.value_lt (CompactFrame.frameBits (stream F (indicator v)))

/-- The scalar product represented by the one count digit is the actual field value. -/
theorem indicator_value (v : F) :
    (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (List.ofFn (indicator v i))) = v := by
  rw [Finset.prod_eq_single (Fintype.equivFin F v)]
  · simp [indicator,List.ofFn_succ,FieldPowers.digits]
  · intro j _ ne
    simp [indicator,ne,List.ofFn_succ,FieldPowers.digits]
  · simp

omit [Field F] in
/-- A word fetched from the actual field deck is exactly the complete physical
packed argument expected by the private scalar routine. -/
theorem pack_eq {w : ℕ} (v : F) (word : Word w) (wide : 2*Fintype.card F<w) (read : word.val = encode v) :
    CompactFrame.pack w (stream F (indicator v)) = [word] := by
  let xs := stream F (indicator v)
  have hlen : xs.length=Fintype.card F := by simp only [xs,stream_length,one_mul]
  have hw : 0<w := by omega
  have len : (CompactFrame.pack w xs).length=1 := by
    rw [CompactFrame.length_pack,← CompactFrame.wordCount,CompactFrame.wordCount_terminator hw,hlen,Nat.div_eq_of_lt wide]
  obtain ⟨u,hu⟩ := List.length_eq_one_iff.mp len
  have hb := CompactFrame.inputBits_pack hw xs
  rw [hu] at hb
  have actual : TeamPrivateCall.inputBits [u] = wordBits u := by
    simp [TeamPrivateCall.inputBits,wordBits,LiveHeader.testBit_wordBits]
  rw [actual] at hb
  have vEq := congrArg TapeWord.value hb
  simp only [TapeWord.value_wordBits,TapeWord.value_append,TapeWord.value_zeros,Nat.mul_zero,Nat.add_zero] at vEq
  have eq : u=word := Fin.ext (vEq.trans read.symm)
  change CompactFrame.pack w xs = [word]
  rw [hu,eq]

variable {w m : ℕ} {Q : Type}

/-- At this physical one-word call the only admitted private script is empty.
The true terminal contributes exactly the field scalar, including zero. -/
theorem returned (lib : Fin 8 → TeamSite.Macro Q (Option Bool) m AlphabetWidth)
    (old : FieldProcessor.Returns Q (Option Bool) F m 8) (v : F) (word : Word w) (event : TeamRAM.Event w)
    (wide : 2*Fintype.card F<w) (read : word.val = encode v) (words : event.old=[word]) (fuel : ℕ)
    (clock : 2*Fintype.card F<fuel) :
    (∀ bs, TeamSiteEvents.macros (combine F lib) fuel 1 [word] bs = if bs.isEmpty then some .plus else none) ∧
    FieldProcessor.returned (combine F lib 1) (returns F lib old 1) fuel event =
      if event.choices.isEmpty then some v else none := by
  have packet := pack_eq v word wide read
  have hw : 0<w := by omega
  have bound : 2*1*Fintype.card F < fuel := by simpa using clock
  constructor
  · intro bs
    rw [← packet]
    exact macro_one F lib (indicator v) hw fuel bound bs
  · rw [scalar_return F lib old (indicator v) hw event fuel (words.trans packet.symm) bound,indicator_value]

end FiniteEvaluator.CubeWord

end BorderVNP
end Computability
end OAI
