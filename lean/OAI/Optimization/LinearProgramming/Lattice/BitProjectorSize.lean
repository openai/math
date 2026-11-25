import OAI.Optimization.LinearProgramming.Lattice.BitProjectorData
import OAI.Optimization.LinearProgramming.Lattice.ProjectionGram
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingBounds

/-! A polynomially clocked Boolean-stack projector for independent integer directions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Projector

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.PriceGame.Control.Wire (list_le rat_length listBound)
open WithLp

/-- The dimension is unary; its length is paid by every encoded input, including the
empty list of previously accumulated directions. -/
def input {p : ℕ} (zs : List (Fin p → ℤ)) : Arg := (p,zs.map List.ofFn)

private theorem iterate_rows {p : ℕ} (todo done : List (Fin p → ℤ)) (k : ℕ) :
    (next^[k]) (todo.map List.ofFn,pack (rationalResidualMatrix done)) =
      ((todo.drop k).map List.ofFn,pack (rationalResidualMatrix ((todo.take k).reverse ++ done))) := by
  induction k generalizing todo done with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases todo with
    | nil =>
      simpa [next] using ih [] done
    | cons z zs =>
      change (next^[k]) (zs.map List.ofFn,step (pack (rationalResidualMatrix done)) (List.ofFn z)) = _
      rw [step_pack]
      change (next^[k]) (zs.map List.ofFn,pack (rationalResidualMatrix (z::done))) = _
      simpa [List.reverse_cons,List.append_assoc] using ih zs (z::done)

theorem next_input_iterate {p : ℕ} (zs : List (Fin p → ℤ)) (k : ℕ) :
    (next^[k]) (start (input zs)) =
      ((zs.reverse.drop k).map List.ofFn,pack (rationalResidualMatrix (zs.drop (zs.length-k)))) := by
  change (next^[k]) ((zs.map List.ofFn).reverse,ident p) = _
  rw [← List.map_reverse,ident_pack]
  change (next^[k]) (zs.reverse.map List.ofFn,pack (rationalResidualMatrix [])) = _
  rw [iterate_rows]
  simp [List.take_reverse]

private theorem independent_drop {p : ℕ} (zs : List (Fin p → ℤ))
    (h : LinearIndependent ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))))
    (k : ℕ) : LinearIndependent ℝ (fun i : Fin (zs.drop k).length =>
      toLp 2 (realCoordinates ((zs.drop k).get i))) := by
  let idx : Fin (zs.drop k).length → Fin zs.length := fun i =>
    ⟨k+i.val,by
      have hi := i.isLt
      have hl : (zs.drop k).length = zs.length-k := by simp
      omega⟩
  have inj : Function.Injective idx := by
    intro i j hij
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val hij))
  have he : (fun i : Fin (zs.drop k).length => toLp 2 (realCoordinates ((zs.drop k).get i))) =
      (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))) ∘ idx := by
    funext i
    simp [idx,List.get_eq_getElem]
  rw [he]
  exact h.comp idx inj

private theorem pack_word {p W : ℕ} (A : Matrix (Fin p) (Fin p) ℚ)
    (hc : ∀ i j, (ratCode (A i j)).length ≤ W) :
    (tableCode (pack A)).length ≤ listBound p (listBound p W) := by
  apply list_le _ _ (by simp)
  intro row hrow
  change row ∈ List.ofFn (fun i => List.ofFn (A i)) at hrow
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
  apply list_le _ _ (by simp)
  intro a ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  exact hc i j

/-- A fixed polynomial covering the pending integer packet, projector matrix, row frames,
and both binary parts of all of its normalized rational entries. -/
noncomputable def space : Polynomial ℕ :=
  let x : Polynomial ℕ := Polynomial.X
  let bound := 7+3*((2*x + 2*(x+1))*x+1)
  let row := x*(2*bound+2)+1
  let matrix := x*(2*row+2)+1
  let pending := x*(2*x+2)+1
  2*pending+1+matrix

private def wordBudget (w : ℕ) : ℕ :=
  2*listBound w w + 1 + listBound w (listBound w (7+3*((2*w+2*(w+1))*w+1)))

private theorem eval_space (w : ℕ) : space.eval w = wordBudget w := by
  simp [space,wordBudget,listBound]

private theorem listBound_mono {n n' w w' : ℕ} (hn : n ≤ n') (hw : w ≤ w') :
    listBound n w ≤ listBound n' w' := by
  unfold listBound
  gcongr

private theorem input_bounds {p : ℕ} (zs : List (Fin p → ℤ)) :
    p ≤ (argCode (input zs)).length ∧ (intMatrixCode ((input zs).2)).length ≤ (argCode (input zs)).length := by
  simp only [argCode,input,prodCode,pairBits_length,unaryCode,List.length_replicate]
  omega

private theorem input_coordinate {p : ℕ} {zs : List (Fin p → ℤ)} {z : Fin p → ℤ}
    (hz : z ∈ zs) (i : Fin p) : (z i).natAbs ≤ 2^(argCode (input zs)).length := by
  have hz' : List.ofFn z ∈ (input zs).2 := List.mem_map.mpr ⟨z,hz,rfl⟩
  have hi : z i ∈ List.ofFn z := List.mem_ofFn.mpr ⟨i,rfl⟩
  have hlen := (code_le_of_mem intCode hi).trans ((code_le_of_mem intRowCode hz').trans (input_bounds zs).2)
  have hc : (intCode (z i)).length = (z i).natAbs.size+3 := by
    simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
    omega
  rw [hc] at hlen
  exact (Nat.size_le.mp (by omega : (z i).natAbs.size ≤ (argCode (input zs)).length)).le

/-- The complete input cost of the uniform projector is polynomial in the dimension
and the maximum binary length of an integer direction. -/
theorem input_word_bound {p D : ℕ} (zs : List (Fin p → ℤ)) (hlen : zs.length ≤ p)
    (hD : ∀ z ∈ zs, ∀ i, (z i).natAbs ≤ D) :
    (argCode (input zs)).length ≤ 2*p+1 + listBound p (listBound p (D.size+3)) := by
  have hm : (intMatrixCode (zs.map List.ofFn)).length ≤ listBound p (listBound p (D.size+3)) := by
    apply list_le _ _ (by simpa using hlen)
    intro row hr
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    apply list_le _ _ (by simp)
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    have hh := Nat.size_le_size (hD z hz i)
    simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len] at *
    omega
  simp only [argCode,input,prodCode,pairBits_length,unaryCode,List.length_replicate]
  omega

/-- Every ordinary iterate fits the unary word guard. The Gram-minor estimate is
applied anew to each actual suffix of the original rows. -/
theorem next_input_fits {p : ℕ} (zs : List (Fin p → ℤ))
    (hli : LinearIndependent ℝ (fun i : Fin zs.length => toLp 2 (realCoordinates (zs.get i))))
    (k : ℕ) : (workCode ((next^[k]) (start (input zs)))).length ≤ space.eval (argCode (input zs)).length := by
  let w := (argCode (input zs)).length
  have hp : p ≤ w := (input_bounds zs).1
  have hn : zs.length ≤ p := by simpa using hli.fintype_card_le_finrank
  let old := zs.drop (zs.length-k)
  have hold : old.length ≤ p := (by simp [old] : old.length ≤ zs.length).trans hn
  have hrows : ∀ z ∈ old, ∀ i, (z i).natAbs ≤ 2^w := fun _ hz i =>
    input_coordinate (List.mem_of_mem_drop hz) i
  have hLI := independent_drop zs hli (zs.length-k)
  let bound := 7+3*((2*w+2*(w+1))*w+1)
  have hcell (i j : Fin p) : (ratCode (rationalResidualMatrix old i j)).length ≤ bound := by
    have h := rationalResidualMatrix_entry_size old hold hrows hLI i j
    simp only [Nat.size_pow] at h
    have hb : (2*p+2*(w+1))*p ≤ (2*w+2*(w+1))*w := by gcongr
    rw [rat_length]
    dsimp [bound]
    omega
  have hmat : (tableCode (pack (rationalResidualMatrix old))).length ≤ listBound w (listBound w bound) :=
    (pack_word _ hcell).trans (listBound_mono hp (listBound_mono hp le_rfl))
  have hpends : ((zs.reverse.drop k).map List.ofFn).length ≤ w := by
    simp; omega
  have hpend : (intMatrixCode ((zs.reverse.drop k).map List.ofFn)).length ≤ listBound w w := by
    apply list_le _ _ hpends
    intro row hr
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    have hz' : z ∈ zs := List.mem_reverse.mp (List.mem_of_mem_drop hz)
    exact (code_le_of_mem intRowCode (List.mem_map.mpr ⟨z,hz',rfl⟩)).trans (input_bounds zs).2
  rw [next_input_iterate,eval_space]
  change (prodCode intMatrixCode tableCode ((zs.reverse.drop k).map List.ofFn,pack (rationalResidualMatrix old))).length ≤ _
  simp only [prodCode,pairBits_length,wordBudget]
  change 2*(intMatrixCode ((zs.reverse.drop k).map List.ofFn)).length+
      (tableCode (pack (rationalResidualMatrix old))).length+1 ≤ 2*listBound w w+1+listBound w (listBound w bound)
  omega

end Projector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
