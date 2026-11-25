import OAI.Computability.MultitapeWeakETH.TensorCoding

/-! # Finite restriction from repeated pinned outputs to independent equality wires -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor Finset
open scoped BigOperators Classical

/-- Coherent implementation of the chosen arrays. At each party a single
stream index selects a product of local maps. The same party then reads its
terminal columns, including multiple endpoints when they are colocated. -/
theorem coded_wire_restriction {K J R E A : Type} [Field K] [Fintype J] [Fintype R] [Fintype E]
    (T : Tensor K J) (root : J) (B Pin Stream : J → Type)
    [∀ j, Fintype (B j)] [∀ j, Fintype (Stream j)]
    (pin : ∀ j, A → Pin j) (maps : ∀ j, Pin j → B j → T.Basis j → K)
    (out : A → (j : J) → B j) (scalar : A → K) (nz : ∀ a, scalar a ≠ 0)
    (display : ∀ a, applyLocal (fun j => maps j (pin j a)) T.coeff =
      fun b => if b = out a then scalar a else 0)
    (u v : E → J) (Label : E → Type) [∀ e, Fintype (Label e)]
    (choose : ((e : E) → Label e) → R → A)
    (index : ∀ j, ((e : E) → Label e) → Stream j) (decode : ∀ j, Stream j → R → Pin j)
    (pins : ∀ j s r, decode j (index j s) r = pin j (choose s r))
    (read : ∀ j, (R → B j) → (wireNetwork (k := K) u v Label).Basis j)
    (correct : ∀ s j, read j (fun r => out (choose s r) j) = edgeAssignment u v s j) :
    Restricts (tensorProduct (tensorFamilyProduct (fun _ : R => T))
      (wireNetwork (fun _ : J => root) id Stream)) (wireNetwork u v Label) := by
  classical
  let copies := tensorFamilyProduct (fun _ : R => T)
  let D := wireNetwork (k := K) u v Label
  let parallel (j : J) (q : Stream j) (x : R → B j) (s : copies.Basis j) :=
    ∏ r, maps j (decode j q r) (x r) (s r)
  let reader (j : J) (b : D.Basis j) (x : R → B j) : K := if read j x = b then 1 else 0
  let joint (j : J) (q : Stream j) (b : D.Basis j) (s : copies.Basis j) :=
    ∑ x, reader j b x * parallel j q x s
  let outputs (q : (j : J) → Stream j) := applyLocal (fun j => joint j (q j)) copies.coeff
  let c (s : (e : E) → Label e) := ∏ r, scalar (choose s r)
  let chosen (s : (e : E) → Label e) := fun j => index j s
  have pinned (s : (e : E) → Label e) (b) :
      outputs (chosen s) b = if edgeAssignment u v s = b then c s else 0 := by
    let x (j : J) (r : R) := out (choose s r) j
    have before : applyLocal (fun j => parallel j (index j s)) copies.coeff =
        fun z => if z = x then c s else 0 := by
      funext z
      change applyLocal (fun j y a => ∏ r, maps j (decode j (index j s) r) (y r) (a r))
        copies.coeff z = _
      simp_rw [pins]
      erw [apply_copies T (fun r j => maps j (pin j (choose s r))) z]
      simp_rw [display]
      by_cases eq : z = x
      · subst z; simp [x,c]
      · have mismatch : ∃ r, (fun j => z j r) ≠ out (choose s r) := by
          by_contra! all
          exact eq (funext fun j => funext fun r => congrFun (all r) j)
        obtain ⟨r,ne⟩ := mismatch
        rw [ite_eq_right eq,prod_eq_zero (mem_univ r) (ite_eq_right ne)]
    change applyLocal (fun j b a => ∑ x, reader j b x * parallel j (index j s) x a) copies.coeff b = _
    rw [← applyLocal_comp,before]
    change applyLocal (fun j b x => if read j x = b then (1:K) else 0)
      (fun z => if z = x then c s else 0) b = _
    simp only [applyLocal,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true,Fintype.prod_boole,
      ← funext_iff,ite_mul,one_mul,zero_mul,show (fun j => read j (x j)) = edgeAssignment u v s from funext (correct s)]
    split <;> split <;> first | rfl | (rename_i h₁ h₂; exact False.elim (h₁ h₂)) | (rename_i h₁ h₂; exact False.elim (h₂ h₁))
  obtain ⟨weight,h⟩ := coherent_display (K := K) chosen (edgeAssignment u v)
    outputs c (fun s => prod_ne_zero_iff.mpr fun r _ => nz (choose s r)) (fun s b => by
      by_cases h : edgeAssignment u v s = b <;> simpa only [h,ite_true,ite_false] using pinned s b)
  have available := pin_star_restriction copies root Stream D.Basis weight joint
  obtain ⟨m,eq⟩ := available
  refine ⟨m,?_⟩
  funext b
  apply (congrFun eq b).trans ((h b).trans ?_)
  rw [← sum_wire_basis u v Label b]
  apply sum_congr rfl
  intro s _
  by_cases eq : edgeAssignment u v s = b <;> simp [eq]

end OAI.Computability.MultitapeWeakETH
