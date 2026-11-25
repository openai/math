import OAI.Computability.NearSquareRoot.InterchangeROMRepairPRDecode
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic

/-! # Primitive recursive block matrices for the ordinary leaves of the repair script -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.LocalTable

open Raw Matrix

def vcat (r : ℕ) (f g : Mat) : Mat := fun i j => if i < r then f i j else g (i-r) j
def hcat (c : ℕ) (f g : Mat) : Mat := fun i j => if j < c then f i j else g i (j-c)
def zeros : Mat := fun _ _ => 0

/-- Repeat an arbitrary rectangular ground matrix on the diagonal, once per label. -/
def perLabel (r c : ℕ) (f : Mat) : Mat := fun i j =>
  if i/r = j/c then f (i%r) (j%c) else 0

variable {P : Type*} [Primcodable P]

theorem pr_vcat {n : P → ℕ} {f g : P → Mat} (hn : Primrec n) (hf : EntryPR f) (hg : EntryPR g) :
    EntryPR fun x => vcat (n x) (f x) (g x) :=
  Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp .snd) (hn.comp .fst)) hf
    (hg.eval .fst (Primrec.nat_sub.comp (Primrec.fst.comp .snd) (hn.comp .fst)) (Primrec.snd.comp .snd))

theorem pr_hcat {n : P → ℕ} {f g : P → Mat} (hn : Primrec n) (hf : EntryPR f) (hg : EntryPR g) :
    EntryPR fun x => hcat (n x) (f x) (g x) :=
  Primrec.ite (Primrec.nat_lt.comp (Primrec.snd.comp .snd) (hn.comp .fst)) hf
    (hg.eval .fst (Primrec.fst.comp .snd) (Primrec.nat_sub.comp (Primrec.snd.comp .snd) (hn.comp .fst)))

theorem pr_perLabel {r c : P → ℕ} {f : P → Mat} (hr : Primrec r) (hc : Primrec c) (hf : EntryPR f) :
    EntryPR fun x => perLabel (r x) (c x) (f x) :=
  let i := Primrec.fst.comp (Primrec.snd (α := P) (β := ℕ × ℕ))
  let j := Primrec.snd.comp (Primrec.snd (α := P) (β := ℕ × ℕ))
  Primrec.ite (Primrec.eq.comp (Primrec.nat_div.comp i (hr.comp .fst)) (Primrec.nat_div.comp j (hc.comp .fst)))
    (hf.eval .fst (Primrec.nat_mod.comp i (hr.comp .fst)) (Primrec.nat_mod.comp j (hc.comp .fst))) (.const 0)

def cat {R : Type} {a b : ℕ} (x : Fin a → R) (y : Fin b → R) : Fin (a+b) → R := Fin.addCases x y

def flat {R : Type} {l n : ℕ} (x : Fin l → Fin n → R) (j : Fin (l*n)) : R :=
  x j.divNat j.modNat

private theorem flat_at {R : Type} {l n : ℕ} (x : Fin l → Fin n → R)
    (a : Fin l) (i : Fin n) : flat x (finProdFinEquiv (a,i)) = x a i := by
  change x ((finProdFinEquiv : Fin l × Fin n ≃ _).symm (finProdFinEquiv (a,i))).1
    (finProdFinEquiv.symm (finProdFinEquiv (a,i))).2 = _
  simp

def act {p : ℕ} (r c : ℕ) (f : Mat) (x : Fin c → ZMod (p+1)) := (interpret p r c f).mulVec x

theorem act_vcat {p a b c : ℕ} (f g : Mat) (x : Fin c → ZMod (p+1)) :
    act (a+b) c (vcat a f g) x = cat (act a c f x) (act b c g x) := by
  funext i
  refine Fin.addCases (fun u => ?_) (fun v => ?_) i
  · simp [act, vcat, cat, interpret, mulVec, dotProduct]
  · simp [act, vcat, cat, interpret, mulVec, dotProduct]

theorem act_hcat {p a b c : ℕ} (f g : Mat) (x : Fin a → ZMod (p+1)) (y : Fin b → ZMod (p+1)) :
    act c (a+b) (hcat a f g) (cat x y) = act c a f x + act c b g y := by
  funext i
  simp [act,hcat,cat,interpret,mulVec,dotProduct,Fin.sum_univ_add]

@[simp] theorem act_zero {p r c : ℕ} (x : Fin c → ZMod (p+1)) : act r c zeros x = 0 := by
  ext j; simp [act,interpret,zeros,mulVec,dotProduct]

@[simp] theorem act_ident {p n : ℕ} (x : Fin n → ZMod (p+1)) : act n n ident x = x := by simp [act]

@[simp] theorem act_add {p r c : ℕ} (f g : Mat) (x : Fin c → ZMod (p+1)) :
    act r c (add f g) x = act r c f x + act r c g x := by simp [act,add_mulVec]

@[simp] theorem act_neg {p r c : ℕ} (f : Mat) (x : Fin c → ZMod (p+1)) :
    act r c (neg p f) x = -act r c f x := by simp [act,Matrix.neg_mulVec]

@[simp] theorem act_scale {p r c : ℕ} (a : ℕ) (f : Mat) (x : Fin c → ZMod (p+1)) :
    act r c (scale a f) x = (a : ZMod (p+1)) • act r c f x := by simp [act,smul_mulVec]

theorem act_perLabel {p l r c : ℕ} (f : Mat) (x : Fin l → Fin c → ZMod (p+1)) :
    act (l*r) (l*c) (perLabel r c f) (flat x) = flat (fun a => act r c f (x a)) := by
  funext i
  obtain ⟨⟨a,b⟩,rfl⟩ := (finProdFinEquiv : Fin l × Fin r ≃ _).surjective i
  rw [flat_at]
  change (∑ j : Fin (l*c), (perLabel r c f (finProdFinEquiv (a,b)).val j.val : ZMod (p+1)) *
    flat x j) = _
  rw [← (finProdFinEquiv : Fin l × Fin c ≃ _).sum_comp]
  rw [Fintype.sum_prod_type]
  have ij {n : ℕ} (a : Fin l) (b : Fin n) :
      (finProdFinEquiv (a,b)).val / n = a.val ∧ (finProdFinEquiv (a,b)).val % n = b.val := by
    have he := (finProdFinEquiv : Fin l × Fin n ≃ _).symm_apply_apply (a,b)
    exact ⟨congrArg (fun z => z.1.val) he,congrArg (fun z => z.2.val) he⟩
  have div {n : ℕ} (a : Fin l) (b : Fin n) := (ij a b).1
  have rem {n : ℕ} (a : Fin l) (b : Fin n) := (ij a b).2
  simp only [perLabel,div,rem,flat_at,Fin.val_eq_val]
  rw [Finset.sum_eq_single a]
  · simp [act,interpret,mulVec,dotProduct]
  · intro z _ hz
    simp [Ne.symm hz]
  · simp

end InterchangeROMRepair.Physical.LocalTable

end NearSquareRoot
end Computability
end OAI
