import OAI.Hierarchy.DescentBinaryPolynomial

namespace OAI
/-! # Canonical positive binary indices for the finite-field multiplier search -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBinaryField

/-- The little-endian coefficient word represented by the binary loop counter. -/
def seedCode {k : ℕ} (x : Bits k) : Fin (2^k) := finFunctionFinEquiv x

private theorem readWord {k : ℕ} (i : Fin (2^k)) :
    storedWord k i=(finFunctionFinEquiv (m:=2) (n:=k)).symm i := by
  funext j
  exact Vector.getElem_ofFn j.isLt

@[simp] theorem seedCode_read {k : ℕ} (i : Fin (2^k)) : seedCode (storedWord k i)=i := by
  rw [seedCode,readWord,Equiv.apply_symm_apply]

private theorem code_zero (k : ℕ) : (seedCode (0 : Bits k)).val=0 := by
  change (finFunctionFinEquiv (fun _ : Fin k=>(0 : Fin 2))).val=0
  rw [finFunctionFinEquiv_apply]
  simp

def seedAt (k : ℕ) (i : Fin (2^k-1)) : Nonzero k :=
  let idx : Fin (2^k) := ⟨i.val+1,by have := i.isLt;omega⟩
  ⟨storedWord k idx,fun equal=>by
    have h := congrArg (fun x : Bits k=>(seedCode x).val) equal
    rw [seedCode_read,code_zero] at h
    exact Nat.succ_ne_zero i.val h⟩

/-- The order is the exact integer sequence `1,2,...,2^k-1`; this fixes every equal-score tie. -/
def nonzeroWords (k : ℕ) : List (Nonzero k) := List.ofFn (seedAt k)

theorem seedAt_code {k : ℕ} (i : Fin (2^k-1)) : (seedCode (seedAt k i).val).val=i.val+1 :=
  congrArg Fin.val (seedCode_read _)

@[simp] theorem length_nonzeroWords (k : ℕ) : (nonzeroWords k).length=2^k-1 := List.length_ofFn

theorem nonzeroWords_length (k : ℕ) : (nonzeroWords k).length≤2^k := (length_nonzeroWords k).le.trans (Nat.sub_le _ _)

@[simp] theorem mem_nonzeroWords {k : ℕ} (μ : Nonzero k) : μ∈nonzeroWords k := by
  have positive : 0<(seedCode μ.val).val := Nat.pos_of_ne_zero fun h=>μ.property <|
    (finFunctionFinEquiv (m:=2) (n:=k)).injective (Fin.ext (h.trans (code_zero k).symm))
  let i : Fin (2^k-1) := ⟨(seedCode μ.val).val-1,by have := (seedCode μ.val).isLt;omega⟩
  apply List.mem_ofFn.mpr
  refine ⟨i,Subtype.ext ((finFunctionFinEquiv (m:=2) (n:=k)).injective (Fin.ext ?_))⟩
  change (seedCode (seedAt k i).val).val=(seedCode μ.val).val
  rw [seedAt_code]
  dsimp only [i];omega

end Hierarchy.DescentColonies

end OAI
