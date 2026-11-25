import OAI.Optimization.LinearProgramming.Lattice.BitDriverRows

/-! Bit-length bound for Horner's vector recurrence at every prefix of the digit list. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Horner
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev FoldState := ℤ × List ℤ
def foldStateCode := prodCode intCode intRowCode

def step (B : ℤ) (v d : List ℤ) : List ℤ := Driver.combineRows ((B,-1),(v,d))
def push (x : List ℤ × FoldState) : FoldState := (x.2.1,step x.2.1 x.2.2 x.1)

private theorem signed_length (z : ℤ) : (intCode z).length = z.natAbs.size+3 := by
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
  omega

private theorem update_length (B x d : ℤ) : (intCode (B*x+d)).length ≤
    (intCode B).length+(intCode x).length+(intCode d).length+1 := by
  have hle := bits_length_mono (Int.natAbs_add_le (B*x) d)
  have hadd := bits_length_add (B*x).natAbs d.natAbs
  have hmul := bits_length_mul B.natAbs x.natAbs
  simp only [signed_length,Int.natAbs_mul,Nat.size_eq_bits_len] at *
  omega

private theorem get_length (xs : List ℤ) (i H : ℕ) (hH : 3 ≤ H)
    (hxs : ∀ z∈xs, (intCode z).length ≤ H) : (intCode (readAt 0 xs i)).length ≤ H := by
  by_cases hi : i < xs.length
  · have he : readAt 0 xs i = xs[i] := by simp [readAt,hi]
    rw [he]
    exact hxs _ (List.getElem_mem hi)
  · have he : xs.drop i = [] := List.drop_eq_nil_iff.mpr (by omega)
    simpa only [readAt,he,List.headD_nil,signed_length,Int.natAbs_zero,Nat.size_zero,Nat.zero_add] using hH

private theorem step_length (B : ℤ) (x d : List ℤ) : (step B x d).length=x.length := by
  simp [step,Driver.combineRows]

private theorem step_width (B : ℤ) (x d : List ℤ) (H C : ℕ) (hH : 3 ≤ H) (hC : 3 ≤ C)
    (hB : (intCode B).length ≤ C) (hx : ∀ z∈x, (intCode z).length ≤ H)
    (hd : ∀ z∈d, (intCode z).length ≤ C) (z : ℤ) (hz : z∈step B x d) :
    (intCode z).length ≤ H+(2*C+2) := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
  change (intCode (B*readAt 0 x j - (-1)*readAt 0 d j)).length ≤ _
  rw [neg_one_mul,sub_neg_eq_add]
  have hw := update_length B (readAt 0 x j) (readAt 0 d j)
  have h1 := get_length x j H hH hx
  have h2 := get_length d j C hC hd
  omega

theorem fold_state (B : ℤ) (v : List ℤ) (rs : IntMatrix) :
    rs.foldl (fun s r => push (r,s)) (B,v) = (B,rs.foldl (step B) v) := by
  induction rs generalizing v with
  | nil => rfl
  | cons r rs ih => exact ih (step B v r)

private theorem fold_width (B : ℤ) (C : ℕ) (hC : 3 ≤ C) (hB : (intCode B).length ≤ C)
    (rs : IntMatrix) (v : List ℤ) (H : ℕ) (hH : 3 ≤ H) (hv : ∀ z∈v, (intCode z).length ≤ H)
    (hr : ∀ r∈rs, ∀ z∈r, (intCode z).length ≤ C) :
    (rs.foldl (step B) v).length = v.length ∧
      ∀ z∈rs.foldl (step B) v, (intCode z).length ≤ H+rs.length*(2*C+2) := by
  induction rs generalizing v H with
  | nil => exact ⟨rfl,by simpa using hv⟩
  | cons row rs ih =>
    obtain ⟨hl,hz⟩ := ih (step B v row) (H+(2*C+2)) (by omega)
      (step_width B v row H C hH hC hB hv (hr row (by simp)))
      (fun r h => hr r (by simp [h]))
    refine ⟨hl.trans (step_length B v row), ?_⟩
    intro z hm
    have hz' := hz z hm
    simpa only [List.length_cons,Nat.succ_mul,add_assoc,add_left_comm,add_comm] using hz'

/-- All intermediate words of the packed-state digit fold fit a fixed cubic in the original
word length. This holds also for ragged rows and arbitrary initial accumulators. -/
theorem prefix_words (rs : IntMatrix) (s : FoldState) (i : ℕ) :
    (foldStateCode ((rs.take i).foldl (fun s r => push (r,s)) s)).length ≤
      (Polynomial.C 32 * (Polynomial.X+3)^3 : Polynomial ℕ).eval
        ((intMatrixCode rs).length + (foldStateCode s).length) := by
  rcases s with ⟨B,v⟩
  let N := (intMatrixCode rs).length + (foldStateCode (B,v)).length
  let C := N+3
  let out := (rs.take i).foldl (step B) v
  have hB : (intCode B).length ≤ N := by dsimp [N,foldStateCode,prodCode]; rw [pairBits_length]; omega
  have hV : (intRowCode v).length ≤ N := by dsimp [N,foldStateCode,prodCode]; rw [pairBits_length]; omega
  have hRs : (intMatrixCode rs).length ≤ N := Nat.le_add_right ..
  have hC : 3 ≤ C := by dsimp [C]; omega
  have hv (z : ℤ) (hz : z∈v) : (intCode z).length ≤ C :=
    (code_le_of_mem intCode hz).trans (hV.trans (Nat.le_add_right ..))
  have hr (r) (h : r∈rs.take i) (z : ℤ) (hz : z∈r) : (intCode z).length ≤ C :=
    (code_le_of_mem intCode hz).trans
      ((code_le_of_mem intRowCode (List.mem_of_mem_take h)).trans (hRs.trans (Nat.le_add_right ..)))
  obtain ⟨hout,hw⟩ := fold_width B C hC (hB.trans (Nat.le_add_right ..)) (rs.take i) v C hC hv hr
  have ht : (rs.take i).length ≤ rs.length := by simp
  have hk : (rs.take i).length ≤ N := ht.trans ((list_length_le_code intRowCode rs).trans hRs)
  have hwidth (z : ℤ) (hz : z∈out) : (intCode z).length ≤ 4*(N+3)^2 := by
    have hs := (hw z hz).trans (Nat.add_le_add_left (Nat.mul_le_mul_right (2*C+2) hk) C)
    dsimp [C] at hs
    nlinarith
  have hlen : out.length ≤ N := hout.le.trans ((list_length_le_code intCode v).trans hV)
  have hsize : (intRowCode out).length ≤ N*(2*(4*(N+3)^2)+2)+1 := by
    have hu := listCode_length_map_bound intCode id out (4*(N+3)^2) hwidth
    simpa [intRowCode] using hu.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) _)
  rw [fold_state]
  change (foldStateCode (B,out)).length ≤ (Polynomial.C 32 * (Polynomial.X+3)^3 : Polynomial ℕ).eval N
  simp only [foldStateCode,prodCode,pairBits_length,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  nlinarith

end Horner
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
