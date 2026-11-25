import OAI.Hierarchy.DescentPackedResetImage
import OAI.Hierarchy.DescentResetPaletteCode

namespace OAI
/-! # Reset private-tree records store short multiplicities and share the original grain width -/
namespace Hierarchy.DescentPackedFallbackTree
open DescentPrivateTreeTemplate DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section

def fieldWidth (H n : ℕ) := H+2+Nat.log 2 (n+1)

def heapName (h : ℕ) (i : Site h) := DescentResetPaletteCode.heap i

theorem count_le {H n : ℕ} (p : Panel H n) (t : Template) : count p t≤n := by
  calc
    _ ≤ ∑_ : Fin n,1 := Finset.sum_le_sum (fun i _=>by split <;> omega)
    _ = n := by simp

theorem features_small {d H n : ℕ} (h : d≤H) (p : Panel H n) (s : ℕ) (j : Fin 5) :
    let t:=DescentPrivateTreeTemplate.lookup H d s (heapName d)
    ![t.active,t.source,t.target,count p t,t.active] j < 2^(fieldWidth H n) := by
  have a : n<2^(fieldWidth H n) := by
    have loose:=Nat.lt_pow_succ_log_self (by decide : 1<2) (n+1)
    exact (Nat.lt_succ_self n).trans (loose.trans_le (Nat.pow_le_pow_right (by decide) (by unfold fieldWidth;omega)))
  have names (x : Site d) : heapName d x<2^(fieldWidth H n) := by
    have hl:=x.1.isLt
    have bound:=(DescentResetPaletteCode.heap_bounds x).2
    have le := Nat.pow_le_pow_right (by decide : 0<2) (show x.1.val+1≤fieldWidth H n by unfold fieldWidth;omega)
    unfold heapName
    omega
  have one : 1<2^(fieldWidth H n) := Nat.one_lt_two_pow (by unfold fieldWidth;omega)
  generalize eqn : DescentPrivateTreeTemplate.lookup H d s (heapName d)=t
  have units:= (count_le p t).trans_lt a
  have ends : t.active<2^(fieldWidth H n) ∧ t.source<2^(fieldWidth H n) ∧ t.target<2^(fieldWidth H n) := by
    rw [←eqn]
    unfold DescentPrivateTreeTemplate.lookup
    cases (edgeAt d s) with
    | none=>simp
    | some e=>exact ⟨one,names _,names _⟩
  fin_cases j <;> simp [*,Matrix.cons_val_zero]

/-- The fourth short field is the number of active old bundles.  The physical
width at a live private edge is that number times the common reset unit. -/
theorem image_read {d H n : ℕ} (hd : d≤H) (p : Panel H n) (cap : ℕ) (s : Fin cap) (j : Fin 5) :
    let t:=DescentPrivateTreeTemplate.lookup H d s.val (heapName d)
    digit (fieldWidth H n) (finProdFinEquiv (s,j)).val
        (Image.columns H n (fieldWidth H n) 1 cap heapName (pack H d p)).val =
      ![t.active,t.source,t.target,count p t,t.active] j := by
  rw [Image.column_read H n (fieldWidth H n) 1 cap hd heapName p s j]
  simp only [one_mul]
  exact Fin.val_cast_of_lt (features_small hd p s.val j)

end
end Hierarchy.DescentPackedFallbackTree

end OAI
