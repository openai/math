import OAI.Computability.BorderVNP.CellScanCost
import OAI.Computability.BorderVNP.CellDirectoryInputSize
import OAI.Computability.BorderVNP.CellDirectoryLiteralLoops
import OAI.Computability.BorderVNP.CellDirectoryBudget

/-! # Quantitative cost of the actual generator and interpreter on one cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro CellMacro.Generator

/-- Elementary private steps after loading the compact program, including the reversal
that puts the emitted bytecode into the order expected by the interpreter. -/
noncomputable def generatedWork (s : Stmt) :=
  scanCost (jobs (clocks 8) 8 s []) + (2*work s []+1) + budget (s.expand [])

private theorem field_scale (D : Directory) (p M E : ℕ)
    (h : D.CompactFields p (4*(M+E+1)^3)) :
    (D.program p).field ≤ (10000*6^3)*(M+E+1)^9 := by
  let x := M+E+1
  have h1 : 1 ≤ x^3 := Nat.one_le_pow _ _ (by dsimp [x]; omega)
  have hu : 4*x^3+2 ≤ 6*x^3 := by omega
  apply (D.program_field_le p h).trans
  calc 10000*(4*x^3+2)^3 ≤ 10000*(6*x^3)^3 := by gcongr
       _ = _ := by rw [mul_pow,← pow_mul]; exact (Nat.mul_assoc ..).symm

private theorem trip_product (a p x : ℕ) :
    (a*x^9)^3*(p*x^2) = a^3*p*x^29 := by ring

private theorem runtime_product (a b x l : ℕ) :
    1000*(a*(x^2*l))*(b*x^30) = (1000*a*b)*x^32*l := by ring

/-- A fixed power of the binary input width bounds all expression calls. The physical
local load and delivered bits enter with degree at most 32, including private loop scans
and signed interpretation. -/
theorem directory_runtime_polynomial (A : ℕ) :
    ∃ C k : ℕ, 0 < k ∧ ∀ n M E p : ℕ, M ≤ n → E ≤ n → ∀ D : Directory,
      D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
      D.records.length ≤ 4*(M+E+1)^3 → D.reportedCounts.length ≤ 4*(M+E+1)^3 →
      generatedWork (D.program p) ≤ C*(M+E+1)^32*(n.size+1)^k := by
  let f := 10000*6^3
  let g := f*2^9
  obtain ⟨T,k,_,hk,vis⟩ := visitClock_polynomial_fields 8 3 2 g 9 g 9
  obtain ⟨P,_,syntaxBound⟩ := uniform_program_input_size A
  let V := P+T+7*(g.size+9)+4
  let W := 30000*6^10
  let Z := (f+2)^3*P+W
  refine ⟨1000*V*Z+7*W+3,k,hk,fun n M E p hMn hEn D st hf hr hg => ?_⟩
  let s := D.program p
  let x := M+E+1
  let L := n.size+1
  have hx : 1 ≤ x := by dsimp [x]; omega
  have hL : 1 ≤ L := by dsimp [L]; omega
  have powx (j : ℕ) : 1 ≤ x^j := Nat.one_le_pow j x hx
  have powL : 1 ≤ L^k := Nat.one_le_pow k L hL
  have Lk : L ≤ L^k := by simpa only [pow_one] using Nat.pow_le_pow_right hL hk
  have hfield : s.field ≤ f*x^9 := field_scale D p M E hf
  have hglobal : s.field ≤ g*(n+2)^9 := by
    apply hfield.trans
    have hx' : x ≤ 2*(n+2) := by dsimp [x]; omega
    calc f*x^9 ≤ f*(2*(n+2))^9 := by gcongr
         _ = _ := by rw [mul_pow]; exact (Nat.mul_assoc ..).symm
  have hsize : s.field.size ≤ (g.size+9)*L := by
    have hh := size_of_polynomial_field hglobal
    change s.field.size ≤ g.size+9*L at hh
    rw [Nat.add_mul]
    exact hh.trans (Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hL) _)
  have hvisit : (visitClock 8 3).eval (visitWidth s.field s.field s.lexical) ≤ T*L^k := by
    apply ((visitClock 8 3).monotone ?_).trans (vis n s.field s.field hglobal hglobal)
    have hh := D.program_lexical_le p
    change 1+s.field.size+s.field.size+s.lexical ≤ 1+s.field.size+s.field.size+2
    exact Nat.add_le_add_left hh _
  obtain ⟨hm,hs⟩ := syntaxBound n M E p D hMn hEn st hf
  have hxM : M+1 ≤ x := by dsimp [x]; omega
  have hmass : s.mass ≤ P*x^2 := hm.trans (by gcongr)
  let t := x^2*L^k
  have ht : 1 ≤ t := one_le_mul_of_one_le_of_one_le (powx 2) powL
  have hLt : L^k ≤ t := by dsimp [t]; exact Nat.le_mul_of_pos_left _ (powx 2)
  have hser : (serialized 8 s).length ≤ P*t := hs.trans (by dsimp [t]; rw [← Nat.mul_assoc]; gcongr)
  have hvt := hvisit.trans (Nat.mul_le_mul_left T hLt)
  have hst := hsize.trans (Nat.mul_le_mul_left _ (Lk.trans hLt))
  have hunit : visitSize 8 3 s.field s.lexical (serialized 8 s).length ≤ V*t := by
    dsimp only [visitSize,V]
    simp only [Nat.add_mul,Nat.mul_assoc] at hst ⊢
    omega
  have hu : 4*x^3+2 ≤ 6*x^3 := by have := powx 3; omega
  have he : work s [] ≤ W*x^30 := by
    apply (D.program_work_polynomial p [] _ hf hr hg).trans
    calc 30000*(4*x^3+2)^10 ≤ 30000*(6*x^3)^10 := by gcongr
         _ = _ := by rw [mul_pow,← pow_mul]; exact (Nat.mul_assoc ..).symm
  have hf' : s.field+2 ≤ (f+2)*x^9 := by rw [Nat.add_mul]; have := powx 9; omega
  have htrip : (s.field+2)^3*s.mass ≤ (f+2)^3*P*x^30 := by
    calc _ ≤ ((f+2)*x^9)^3*(P*x^2) := Nat.mul_le_mul (Nat.pow_le_pow_left hf' 3) hmass
         _ = (f+2)^3*P*x^29 := trip_product (f+2) P x
         _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (show 29 ≤ 30 by decide))
  have hchildren : (s.field+2)^3*s.mass+work s [] ≤ Z*x^30 := by
    rw [show Z*x^30 = (f+2)^3*P*x^30 + W*x^30 from Nat.add_mul ..]
    exact Nat.add_le_add htrip he
  have hscan := scanCost_le s 8 3 (D.program_fitsDepth p) (D.program_literalLoops p)
  have hrun : scanCost (jobs (clocks 8) 8 s []) ≤ (1000*V*Z)*x^32*L^k := by
    apply hscan.trans
    calc 1000*visitSize 8 3 s.field s.lexical (serialized 8 s).length*
          ((s.field+2)^3*s.mass+work s []) ≤ 1000*(V*t)*(Z*x^30) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hunit) hchildren
         _ = _ := runtime_product V Z x (L^k)
  let u := x^32*L^k
  have huu : 1 ≤ u := one_le_mul_of_one_le_of_one_le (powx 32) powL
  have he' : work s [] ≤ W*u := he.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right hx
    (show 30 ≤ 32 by decide)).trans (Nat.le_mul_of_pos_right _ powL)))
  have hb : budget (s.expand []) ≤ 5*work s []+2 := budget_le _
  change scanCost (jobs (clocks 8) 8 s []) + (2*work s []+1) + budget (s.expand []) ≤
    (1000*V*Z+7*W+3)*x^32*L^k
  rw [Nat.mul_assoc,show x^32*L^k = u from rfl,Nat.add_mul,Nat.add_mul,Nat.mul_assoc 7]
  rw [Nat.mul_assoc _ (x^32) (L^k)] at hrun
  change _ ≤ 1000*V*Z*u at hrun
  omega

end CellSparse

end BorderVNP
end Computability
end OAI
