import OAI.ThreeFlat.Routing.BitonicComparator
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Local site update in an addressed bitonic layer -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.StableCompactStep
open TableCompiler

abbrev Pin (u : ℕ) := Fin 2 ⊕ (Fin 3 × Fin u)

def pin {u : ℕ} (stride phase : Bool) (a b c : Fin u → Bool) : Pin u → Bool :=
  Sum.elim ![stride,phase] (fun p => ![a,b,c] p.1 p.2)

def selected {u : ℕ} (stride phase : Bool) (a b : Fin u → Bool) : Fin u → Bool :=
  (addressEquiv u).symm (if stride = phase then min ((addressEquiv u) a) ((addressEquiv u) b)
    else max ((addressEquiv u) a) ((addressEquiv u) b))

private abbrev Src (u : ℕ) := BitSource (u+u) (Fintype.card (Pin u))
private def ext {u : ℕ} (p : Pin u) : Src u := .pin (Fintype.equivFin _ p)
private def refs {u : ℕ} (a : Fin 3) (j : Fin u) : Src u := ext (.inr (a,j))
private def lo {u : ℕ} (j : Fin u) : Src u := .hidden (j.castAdd u)
private def hi {u : ℕ} (j : Fin u) : Src u := .hidden (Fin.natAdd u j)

private abbrev port (u : ℕ) : Option (Fin u) → ℕ
  | none => (u+u)+(u+u)
  | some _ => 5

private def check (v : Fin 5 → Bool) : Prop := v 4 = if v 0 = v 1 then v 2 else v 3

private def parts (K : Type*) [Zero K] [One K] (u : ℕ) : (g : Option (Fin u)) → BitNetwork K (port u g)
  | none => BitonicComparator.network K u
  | some _ => localTableNetwork (fun v => if check v then 1 else 0)

private def wire (u : ℕ) : (g : Option (Fin u)) → Fin (port u g) → Src u
  | none => Fin.append (Fin.append (refs 0) (refs 1)) (Fin.append lo hi)
  | some j => ![ext (.inl 0),ext (.inl 1),lo j,hi j, refs 2 j]

def network (K : Type*) [Zero K] [One K] (u : ℕ) : BitNetwork K (Fintype.card (Pin u)) :=
  BitNetwork.glue (parts K u) (wire u)

theorem network_cells (K : Type*) [Zero K] [One K] (u : ℕ) :
    (network K u).cells ≤ 4096*(u+1) := by
  have h := BitonicComparator.network_cells K u
  simp only [network,BitNetwork.glue_cells,Fintype.sum_option,parts,localTableNetwork_cells,port,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

theorem network_internal (K : Type*) [Zero K] [One K] (u : ℕ) :
    (network K u).internal ≤ 4096*(u+1) := by
  have h := BitonicComparator.network_internal K u
  simp only [network,BitNetwork.glue_internal,Fintype.sum_option,parts,localTableNetwork_internal,port,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

private def low {u : ℕ} (a b : Fin u → Bool) :=
  (addressEquiv u).symm (min ((addressEquiv u) a) ((addressEquiv u) b))

private def high {u : ℕ} (a b : Fin u → Bool) :=
  (addressEquiv u).symm (max ((addressEquiv u) a) ((addressEquiv u) b))

private def left {u : ℕ} (z : Fin (u+u) → Bool) (j : Fin u) := z (j.castAdd u)
private def right {u : ℕ} (z : Fin (u+u) → Bool) (j : Fin u) := z (Fin.natAdd u j)
private def bare {u : ℕ} (p : Pin u → Bool) := fun i => p ((Fintype.equivFin _).symm i)

private theorem read_cmp {u : ℕ} (s t : Bool) (a b c : Fin u → Bool) (z : Fin (u+u) → Bool) :
    (fun i => (wire u none i).read z (bare (pin s t a b c))) =
      Fin.append (Fin.append a b) (Fin.append (left z) (right z)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
    simp only [wire,Fin.append_left,Fin.append_right,refs,ext,lo,hi,left,right,BitSource.read,
      bare,Equiv.symm_apply_apply,pin,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]

private theorem read_check {u : ℕ} (s t : Bool) (a b c : Fin u → Bool) (z : Fin (u+u) → Bool) (j : Fin u) :
    check (fun i => (wire u (some j) i).read z (bare (pin s t a b c))) ↔
      c j = if s=t then left z j else right z j := by
  simp [check,wire,lo,hi,refs,ext,BitSource.read,bare,pin,left,right]

theorem network_eval {K : Type*} [CommSemiring K] {u : ℕ} (s t : Bool) (a b c : Fin u → Bool) :
    TypedWiring.value (network K u) (pin s t a b c) = if c = selected s t a b then 1 else 0 := by
  classical
  have cmp (z : Fin (u+u) → Bool) :
      (parts K u none).eval (fun i => (wire u none i).read z (bare (pin s t a b c))) =
        if left z = low a b ∧ right z = high a b then (1 : K) else 0 := by
    exact (congrArg (BitonicComparator.network K u).eval (read_cmp s t a b c z)).trans
      (BitonicComparator.network_eval u a b (left z) (right z))
  have row (z : Fin (u+u) → Bool) (j : Fin u) :
      (parts K u (some j)).eval (fun i => (wire u (some j) i).read z (bare (pin s t a b c))) =
        if c j = (if s=t then left z j else right z j) then (1 : K) else 0 := by
    exact (localTableNetwork_eval (fun v => if check v then (1 : K) else 0)
      (fun i => (wire u (some j) i).read z (bare (pin s t a b c)))).trans
      (ite_congr (propext (read_check s t a b c z j)) (fun _ => rfl) (fun _ => rfl))
  change (network K u).eval (bare (pin s t a b c)) = _
  rw [network,BitNetwork.glue_eval]
  simp only [Fintype.prod_option]
  let good := Fin.append (low a b) (high a b)
  rw [Finset.sum_eq_single_of_mem good (Finset.mem_univ _)]
  · have L : left good = low a b := by funext i; simp only [good,left,Fin.append_left]
    have R : right good = high a b := by funext i; simp only [good,right,Fin.append_right]
    rw [cmp good, ite_eq_left ⟨L,R⟩, one_mul]
    simp only [row, L, R, Fintype.prod_boole]
    apply ite_congr _ (fun _ => rfl) (fun _ => rfl)
    apply propext
    by_cases e : s=t <;> simp only [e,ite_true,ite_false,selected,low,high,funext_iff]
  · intro z _ hn
    have hf : ¬ (left z = low a b ∧ right z = high a b) := by
      rintro ⟨l,r⟩
      apply hn
      funext i
      exact Fin.addCases (fun j => (congrFun l j).trans (Fin.append_left _ _ _).symm)
        (fun j => (congrFun r j).trans (Fin.append_right _ _ _).symm) i
    rw [cmp z, ite_eq_right hf, zero_mul]

end ThreeFlat.Routing.StableCompactStep

end
end OAI
