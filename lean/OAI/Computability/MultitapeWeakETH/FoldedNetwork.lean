import OAI.Computability.MultitapeWeakETH.Tables
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Common supply graph for the shifted four-column tables

The four original table factors at the same vertex are grouped at one site.
Their internal wires are independent. Each low-end block has a processor for
two subtractions. The borrow wire out of the last block returns to block zero
where its value is discarded and the input borrows are set to zero. This keeps a uniform pair of borrow ports even for a
one-block word. A folded edge carries two difference blocks to one terminal.
-/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open Finset
open scoped Classical
noncomputable section

variable {n b N : ℕ} (G : Network n b)

abbrev Site (N : ℕ) := Fin G.vertices ⊕ Fin (n ⌈/⌉ b) ⊕ Fin N
abbrev Wire := (Fin 4 × Fin G.edges) ⊕ (Fin 4 × Fin (n ⌈/⌉ b)) ⊕ Fin (n ⌈/⌉ b) ⊕ Fin (n ⌈/⌉ b)

def original (v : Fin G.vertices) : Site G N := Sum.inl v
def processor (i : Fin (n ⌈/⌉ b)) : Site G N := Sum.inr (Sum.inl i)
def terminal (i : Fin N) : Site G N := Sum.inr (Sum.inr i)

def src : Wire G → Site G N
  | .inl (_,e) => original G (G.src e)
  | .inr (.inl (_,j)) => original G (G.output j)
  | .inr (.inr (.inl j)) | .inr (.inr (.inr j)) => processor G j

def dst [NeZero N] : Wire G → Site G N
  | .inl (_,e) => original G (G.dst e)
  | .inr (.inl (_,j)) => processor G j
  | .inr (.inr (.inl j)) => processor G (finRotate _ j)
  | .inr (.inr (.inr j)) => terminal G (Fin.ofNat N j.val)

def width : Wire G → ℕ
  | .inl (_,e) => G.width e
  | .inr (.inl _) => b
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 2*b

theorem width_le (hb : 0 < b) {D : ℕ} (bound : G.Bounded D) (w : Wire G) :
    width G w ≤ (D+2)*b := by
  rcases w with ⟨_,e⟩ | ⟨_,j⟩ | j | j <;> simp only [width,add_mul]
  · exact (bound.2 e).trans (Nat.le_add_right ..)
  all_goals omega

theorem site_count (hN : N ≤ n ⌈/⌉ b) : Fintype.card (Site G N) ≤ 3*G.vertices := by
  have hm := Fintype.card_le_of_embedding G.input
  simp only [Fintype.card_fin] at hm
  simp only [Site,Fintype.card_sum,Fintype.card_fin]
  omega

private theorem fiber_one {A B : Type} [Fintype A] (f : A ↪ B) (v : B) :
    (univ.filter fun i => f i = v).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  exact f.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)

private theorem folded_fiber [NeZero N] {m C : ℕ} (hm : m ≤ C*N) (v : Fin N) :
    (univ.filter fun j : Fin m => Fin.ofNat N j.val = v).card ≤ C := by
  let pool := univ.filter fun j : Fin m => Fin.ofNat N j.val = v
  let quotient (j : ↥pool) : Fin C := ⟨j.val.val/N,
    (Nat.div_lt_iff_lt_mul (NeZero.pos _)).mpr (j.val.isLt.trans_le hm)⟩
  have inj : Function.Injective quotient := by
    intro a b eq
    have div : a.val.val/N = b.val.val/N := congrArg Fin.val eq
    have rem : a.val.val%N = b.val.val%N :=
      congrArg Fin.val ((mem_filter.mp a.property).2.trans (mem_filter.mp b.property).2.symm)
    have left := Nat.mod_add_div a.val.val N
    rw [div,rem,Nat.mod_add_div] at left
    exact Subtype.ext (Fin.ext left.symm)
  simpa only [pool,Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective _ inj

/-- The degree estimate is independent of the shift, the number of bits in
a block and all table entries. The fold ratio C bounds the terminal fan-in. -/
theorem degree_le [NeZero N] {C D : ℕ} (hC : n ⌈/⌉ b ≤ C*N) (bound : G.Bounded D) (v : Site G N) :
    (univ.filter fun w => src G w = v).card + (univ.filter fun w => dst G w = v).card ≤ 4*D+7+C := by
  have count (f : Wire G → Site G N) :
      (univ.filter fun w => f w = v).card = ∑ w, if f w = v then 1 else 0 := by simp
  rw [count (src G),count (dst G)]
  simp only [Wire,Fintype.sum_sum_type,Fintype.sum_prod_type]
  rcases v with v | j | t
  · simp [src,dst,original,terminal,processor,
      sum_boole]
    have hv := bound.1 v
    unfold Network.degree at hv
    by_cases occupied : ∃ j, G.output j = v
    · obtain ⟨j,rfl⟩ := occupied
      have singleton [DecidablePred (fun x => x = j)] :
          (univ.filter (fun x => x = j)).card = 1 := by
        have eq : univ.filter (fun x => x = j) = {j} := by ext; simp
        rw [eq,card_singleton]
      simp only [G.output.injective.eq_iff,singleton]
      omega
    · have absent i : G.output i ≠ v := fun h => occupied ⟨i,h⟩
      simp [absent]
      omega
  · have ht := fiber_one (finRotate (n ⌈/⌉ b)).toEmbedding j
    simp [src,dst,original,terminal,processor,
      sum_boole] at *
    omega
  · simpa [src,dst,original,terminal,processor,
      sum_boole] using (folded_fiber hC t).trans (show C ≤ 4*D+7+C by omega)

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
