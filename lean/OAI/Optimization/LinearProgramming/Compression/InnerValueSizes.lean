import OAI.Optimization.LinearProgramming.Compression.InnerSessionTransport
import OAI.Optimization.LinearProgramming.Compression.InnerPackets
import OAI.Optimization.LinearProgramming.Games.RecoveryMachineHeight

/-! Output size of the normalized rounding vector and of the reduced tagged result in
the very same codes consumed by the subprograms. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec Lattice.Bit ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Polynomial

theorem sessionOutputLength {I C : Type} {ei : I → Word} {ec : C → Word} {f : I ⊕ (Word × C) → WireAction C}
    {o L s h w h' k} (r : WordDialogue.Session ei ec f o L s h w h' k) : w.length≤L := by
  induction r with
  | done _ _ h => exact h
  | query _ _ _ _ _ ih => exact ih

private theorem intRow_len (zs : Ints) : (intRowCode zs).length ≤ 4*(Driver.signPacket zs).length+1 := by
  induction zs with
  | nil => decide
  | cons z zs ih =>
    change (listCode intCode (z::zs)).length ≤ 4*(Driver.signedField z ++ Driver.signPacket zs).length+1
    rw [listCode_length_cons,Games.RecoveryMachine.int_length,List.length_append]
    simp only [Driver.signedField,List.length_cons,Contraction.encodeNat_length]
    unfold intRowCode at ih
    omega

noncomputable def normalizedBound : Polynomial ℕ := (4*X+1)+normalizeRowP.bound.comp (4*X+1)

theorem normalized_length {z : Ints} {L : ℕ} (h : (Driver.signPacket z).length≤L) :
    (Projector.rowCode (normalizeRow z)).length ≤ normalizedBound.eval L := by
  have hi : (intRowCode z).length ≤ 4*L+1 := (intRow_len z).trans (by omega)
  have hm := Procedure.eval_nat_mono normalizeRowP.bound hi
  have ho := normalizeRowP.output_length_le z
  simpa [normalizedBound] using (ho.trans (Nat.add_le_add hi hm))

private theorem memberRat_length {xs : Rats} {q : ℚ} (hq : q∈xs) : (ratCode q).length≤(Projector.rowCode xs).length := by
  induction xs with
  | nil => simp at hq
  | cons a xs ih =>
    change _ ≤ (listCode ratCode (a::xs)).length
    rw [listCode_length_cons]
    rcases List.mem_cons.mp hq with rfl|h
    · omega
    · have hb := ih h; unfold Projector.rowCode at hb; omega

private theorem readRat_length (xs : Rats) (i : ℕ) : (ratCode (Lattice.Bit.readAt 0 xs i)).length≤(Projector.rowCode xs).length+10 := by
  by_cases hi : i<xs.length
  · have h : Lattice.Bit.readAt 0 xs i=xs[i] := by simp [Lattice.Bit.readAt,hi]
    rw [h]
    exact (memberRat_length (List.getElem_mem hi)).trans (by omega)
  · have h : Lattice.Bit.readAt 0 xs i=0 := by simp [Lattice.Bit.readAt,List.drop_eq_nil_of_le (Nat.le_of_not_gt hi)]
    rw [h]
    have small : (ratCode (0:ℚ)).length≤10 := by decide
    omega

noncomputable def returnBound : Polynomial ℕ := X+someWordP.bound+affineResultP.bound+10

theorem combined_length (x : Input) (gamma : Rats) (out : GraphResult) (G : ℕ)
    (hG : (graphResultCode out).length≤G) :
    (outputWord (combinedAnswer x gamma out)).length ≤ returnBound.eval
      (max (2*(Projector.rowCode gamma).length+1+G) ((inputCode x).length+(Projector.rowCode gamma).length+10)) := by
  let a := max (2*(Projector.rowCode gamma).length+1+G) ((inputCode x).length+(Projector.rowCode gamma).length+10)
  have hL := Nat.le_max_left (2*(Projector.rowCode gamma).length+1+G) ((inputCode x).length+(Projector.rowCode gamma).length+10)
  have hR := Nat.le_max_right (2*(Projector.rowCode gamma).length+1+G) ((inputCode x).length+(Projector.rowCode gamma).length+10)
  by_cases h : x.2.1=true
  · let q := Lattice.Bit.readAt 0 gamma x.2.2
    have hl : (ratCode q).length≤a := (readRat_length gamma x.2.2).trans (by dsimp [a];omega)
    have hm : someWordP.bound.eval (ratCode q).length ≤ someWordP.bound.eval a := Procedure.eval_nat_mono _ hl
    have ho : (outputWord (some q)).length ≤ (ratCode q).length+someWordP.bound.eval (ratCode q).length :=
      someWordP.output_length_le q
    simp only [combinedAnswer,h,↓reduceIte]
    change (outputWord (some q)).length≤returnBound.eval a
    simp only [returnBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
    omega
  · let args : Rats × GraphResult := (gamma,out)
    have hl : (prodCode Projector.rowCode graphResultCode args).length≤a := by
      simp [args,prodCode,pairBits_length,a];omega
    have hm : affineResultP.bound.eval (prodCode Projector.rowCode graphResultCode args).length ≤
        affineResultP.bound.eval a := Procedure.eval_nat_mono _ hl
    have ho : (outputWord (affineResult gamma out)).length ≤ (prodCode Projector.rowCode graphResultCode args).length+
        affineResultP.bound.eval (prodCode Projector.rowCode graphResultCode args).length := affineResultP.output_length_le args
    simp only [combinedAnswer,h]
    change (outputWord (affineResult gamma out)).length≤returnBound.eval a
    simp only [returnBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
    omega

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
