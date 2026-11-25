import OAI.Computability.NearSquareRoot.InterchangeROMBankReindex
import OAI.Computability.NearSquareRoot.InterchangeROMBankCarve

/-! # Composing bounded bank transformations on actual tree buffers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip Space
open InterchangeROMBankCarve

def chainCoeff (t u B : ℕ) := (t+u+2)*(B+1)

theorem Run.join {c d : Cmd} {t s u k B : ℕ} {x y z : Tree}
    (h : Run c t s x y) (g : Run d u k y z) (hm : y.count ≤ B*amount x z) :
    Run (c.join d) (chainCoeff t u B) (chainCoeff s k B) x z := by
  let V := amount x z
  let N := (B+1)*V
  have vpos : 0 < V := by dsimp [V,amount]; omega
  have npos : 0 < N := Nat.mul_pos (Nat.succ_pos _) vpos
  have left : amount x y ≤ N := by
    change y.count ≤ B*V at hm
    dsimp only [N]; rw [Nat.add_mul,Nat.one_mul]; dsimp only [amount,V] at *; omega
  have right : amount y z ≤ N := by
    change y.count ≤ B*V at hm
    dsimp only [N]; rw [Nat.add_mul,Nat.one_mul]; dsimp only [amount,V] at *; omega
  have sum (a b : ℕ) : a*amount x y + b*amount y z + 2 ≤ chainCoeff a b B * V := by
    calc
      _ ≤ a*N + b*N + 2*N := Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left a left) (Nat.mul_le_mul_left b right)) (by omega)
      _ = _ := by dsimp only [N,chainCoeff]; ring
  intro env r base hr
  have cap := sum s k
  have first := (h env r base hr).mono le_rfl
    (show base+s*amount x y ≤ base+chainCoeff s k B*V by omega) le_rfl
  have last := (g env r base hr).mono le_rfl
    (show base+k*amount y z ≤ base+chainCoeff s k B*V by omega)
    (show k*amount y z ≤ chainCoeff s k B*V by omega)
  exact (first.join last (by omega)).mono (sum t u) le_rfl le_rfl

theorem stripe_counts_le {A : Type} (p : Series A) (v w : A → Tree) {m : ℕ} (hm : 0 < m)
    (hw : ∀ a, (v a).count ≤ m*(w a).count) : (stripe p v).count ≤ m*(stripe p w).count := by
  simp only [stripe_simple]
  induction p.explore with
  | nil => simp only [Task.forest_nil,Tree.count,Nat.mul_one]; omega
  | cons a l ih =>
    simp only [Task.forest_cons,Tree.count,Nat.mul_add,Nat.mul_one]
    have := hw a
    omega

theorem stripe_entry_le {A : Type} (p : Series A) (v : A → Tree) (a : A) :
    (v a).count ≤ (stripe p v).count := by
  rw [stripe_simple]
  exact LoomRegisters.count_le_forest v (p.complete a)

noncomputable def carveCoeff : ℕ := carve_bounded.choose
noncomputable def flattenCoeff : ℕ := flatten_bounded.choose

abbrev ruler {A D T : Type} (p : Series A) (d : Series D) (t : Series T) :=
  send (tally p.count,tally d.count,tally t.count)

abbrev flat {A D T : Type} (p : Series A) (d : Series D) (t : Series T) (v : (A×D)×T → Tree) :=
  stripe ((p.cart d).cart t) v

abbrev nested {A D T : Type} (p : Series A) (d : Series D) (t : Series T) (v : (A×D)×T → Tree) :=
  stripe p fun x => stripe d fun j => stripe t fun z => v ((x,j),z)

theorem carve_run {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hp : 0 < p.count) (hd : 0 < d.count) (ht : 0 < t.count) (v : (A×D)×T → Tree) :
    Run carveCommand carveCoeff carveCoeff ((ruler p d t).fork (flat p d t v)) (nested p d t v) := by
  intro env r base hr
  have c := carve_bounded.choose_spec p d t hp hd ht v env r base hr
  have pos := (nested p d t v).count_pos
  have h := Nat.mul_le_mul_left carveCoeff (show ((ruler p d t).fork (flat p d t v)).count+2 ≤
    amount ((ruler p d t).fork (flat p d t v)) (nested p d t v) by dsimp only [amount]; omega)
  exact c.mono h (Nat.add_le_add_left h _) h

theorem flatten_run {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hp : 0 < p.count) (hd : 0 < d.count) (ht : 0 < t.count) (v : (A×D)×T → Tree) :
    Run flattenCommand flattenCoeff flattenCoeff (nested p d t v) (flat p d t v) := by
  intro env r base hr
  have c := flatten_bounded.choose_spec p d t hp hd ht v env r base hr
  have pos := (flat p d t v).count_pos
  have h := Nat.mul_le_mul_left flattenCoeff (show (nested p d t v).count+2 ≤
    amount (nested p d t v) (flat p d t v) by dsimp only [amount]; omega)
  exact c.mono h (Nat.add_le_add_left h _) h

end InterchangeROMBank

end NearSquareRoot
end Computability
end OAI
