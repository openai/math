import OAI.Computability.BorderVNP.PackedBankPadding
import OAI.Computability.BorderVNP.PackedPoolCircuit

/-! # Boolean public fields for the origin and terminal sparse records

The public branch supplies the number of matched blocks and one count per fixed
term. Each row's base, its padding offset, and its padding length are computed
by a fixed straight-line expression in those words. The private verifier reads
the resulting rectangles by copy and lane indices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCircuit

open ParseBatchSort VPVNP.VerifierNetwork Crossing.Profile.Cell Word
open scoped Classical

/-- A selector spoke at the origin, or a selector, original, or feeder at a terminal. -/
abbrev Slice (D A : ℕ) := (Fin D × Bool) ⊕ (Unit ⊕ Unit ⊕ Fin A)

/-- Mutable address columns of a row of the fixed-stride local assignment bank. -/
inductive SliceColumn where | base | padBase | padWidth
  deriving DecidableEq

instance : Fintype SliceColumn :=
  ⟨{.base,.padBase,.padWidth},by intro c; cases c <;> simp⟩

/-- Pass-through count words, followed by the computed addresses of all sparse rows. -/
abbrev Header (D A : ℕ) := Option (Fin A) ⊕ (Slice D A × SliceColumn)

variable {D A : ℕ} (b : ℕ)

private noncomputable def rank : Slice D A → ℕ
  | .inl u => (Fintype.equivFin (Fin D × Bool) u).val
  | .inr u => (Fintype.equivFin (Unit ⊕ Unit ⊕ Fin A) u).val

/-- The fixed number of lanes per copy in this physical slice. -/
def lanes : Slice D A → ℕ
  | .inl _ | .inr (.inl _) => Nat.clog 2 A
  | .inr (.inr _) => b

private def countField : Slice D A → Option (Fin A)
  | .inr (.inr (.inr a)) => some a
  | _ => none

private def strideScale : Slice D A → ℕ
  | .inl _ => Fintype.card (Fin D × Bool) * Nat.clog 2 A
  | .inr _ => Nat.clog 2 A + 2*b

private noncomputable def code (r : Slice D A) (c : SliceColumn) : WidthExpr (Option (Fin A)) :=
  let base := PoolCircuit.scaleExpr none (rank r * strideScale b r)
  let stride := PoolCircuit.scaleExpr none (strideScale b r)
  let used := PoolCircuit.scaleExpr (countField r) (lanes b r)
  match c with
  | .base => base
  | .padBase => .binary .add base used
  | .padWidth => .binary .sub stride used

/-- Each accepted header has exactly these linear arithmetic field values. -/
noncomputable def headerWord (x : Option (Fin A) → ℕ) : Header D A → ℕ
  | .inl i => x i
  | .inr (r,c) =>
    let stride := strideScale b r * x none
    let start := rank r * stride
    let used := lanes b r * x (countField r)
    match c with
    | .base => start
    | .padBase => start + used
    | .padWidth => stride - used

private noncomputable def expression : Header D A → WidthExpr (Option (Fin A))
  | .inl i => .field i
  | .inr (r,c) => code b r c

private theorem expr_value (x : Option (Fin A) → ℕ) (i : Header D A) :
    (expression b i).eval x = headerWord b x i := by
  rcases i with _ | ⟨r,c⟩
  · rfl
  · cases c <;> simp only [expression,code,headerWord,WidthExpr.eval,PoolCircuit.scale_eval,Op.apply,Nat.mul_assoc]

/-- A bound on the end of every reserved row and its occupied prefix. -/
def HeaderFits (w : ℕ) (x : Option (Fin A) → ℕ) : Prop :=
  ∀ r : Slice D A, (rank r + 1) * (strideScale b r * x none) < 2^w ∧
    lanes b r * x (countField r) ≤ strideScale b r * x none

private theorem expr_fits {w : ℕ} (x : Option (Fin A) → ℕ) (h : ∀ i, x i < 2^w)
    (hf : HeaderFits (D := D) b w x) (i : Header D A) : (expression b i).Fits w x := by
  rcases i with i | ⟨r,c⟩
  · exact h i
  · obtain ⟨hroom,hused⟩ := hf r
    rw [Nat.add_mul,Nat.one_mul] at hroom
    have hstart : rank r * strideScale b r * x none < 2^w := by rw [Nat.mul_assoc]; omega
    have hs := PoolCircuit.scale_fits w x none _ (h none) hstart
    have ht := PoolCircuit.scale_fits w x none (strideScale b r) (h none) (by omega)
    have hu := PoolCircuit.scale_fits w x (countField r) (lanes b r) (h _) (by omega)
    cases c with
    | base => exact hs
    | padBase =>
      refine ⟨hs,hu,?_⟩
      simp only [Op.apply,PoolCircuit.scale_eval,Nat.mul_assoc]
      omega
    | padWidth =>
      refine ⟨ht,hu,?_⟩
      simp only [Op.apply,PoolCircuit.scale_eval]
      omega

/-- Static size coefficient of the public word compiler for one seed. -/
noncomputable def headerNodes (D A b : ℕ) : ℕ :=
  ∑ i : Header D A, (expression b i).nodes

/-- All origin and terminal record operands are emitted by one shared gate list. -/
theorem exists_headerFrame {S σ : Type*} [Fintype S] [Fintype σ] (D A b w : ℕ)
    (source : Frame σ (S × Option (Fin A) × Fin w)) :
    ∃ f : Frame σ (S × Header D A × Fin w),
      f.size ≤ source.size + 1 + Fintype.card S * (headerNodes D A b * (100*(w+1)^2)) ∧
      ∀ x s, let counts := fun i => value (fun j => source.eval x (s,i,j))
        HeaderFits (D := D) b w counts →
          ∀ i, value (fun j => f.eval x (s,i,j)) = headerWord b counts i := by
  classical
  let leaf (p : S × Header D A) := ((expression b p.2).frame w).subst
    (Frame.initial (fun i : Option (Fin A) × Fin w => (p.1,i)))
  obtain ⟨joint,hs,he⟩ := Crossing.exists_parallelFrames leaf
  let pins (i : S × Header D A × Fin w) : Σ _ : S × Header D A, Fin w := ⟨(i.1,i.2.1),i.2.2⟩
  refine ⟨(joint.select pins).subst source, ?_, ?_⟩
  · have hl (p : S × Header D A) : (leaf p).size ≤ (expression b p.2).nodes * (100*(w+1)^2) := by
      simp only [leaf,Frame.subst_size,Frame.initial_size,zero_add]
      exact (expression b p.2).frame_size w
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hl t)
    have htotal : (∑ p : S × Header D A, (expression b p.2).nodes * (100*(w+1)^2)) =
        Fintype.card S * (headerNodes D A b * (100*(w+1)^2)) := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        Nat.cast_id,headerNodes,← Finset.sum_mul,Nat.mul_assoc]
    rw [htotal] at hsum
    simp only [Frame.subst_size,Frame.select_size]
    exact (Nat.add_le_add_left (hs.trans (Nat.add_le_add_left hsum 1)) _).trans_eq (by omega)
  · intro x s counts hfit i
    let z := fun p : Option (Fin A) × Fin w => source.eval x (s,p)
    have hv : (fun j => ((joint.select pins).subst source).eval x (s,i,j)) = ((expression b i).frame w).eval z := by
      funext j
      simp [Frame.subst_eval,pins,he,leaf,z]
      congr 1
      funext k
      simp
    rw [hv]
    exact ((expression b i).frame_value w z (expr_fits b counts (fun _ => value_lt _) hfit i)).trans
      (expr_value b counts i)

/-- Numerical values of the three columns of a physical assignment-bank slice. -/
noncomputable def sliceRead {R : Type*} [Fintype R] (L : BankLayout R) (r : R) : SliceColumn → ℕ
  | .base => address L r 0
  | .padBase => address L r (active L r)
  | .padWidth => L.stride - active L r

/-- At the origin the computed columns use exactly the shared selector-bank stride. -/
theorem origin_word (j : ℕ) (p : Fin A → ℕ) (r : Fin D × Bool) (c : SliceColumn) :
    headerWord b (fun i => i.elim j p) (.inr (.inl r,c)) =
      sliceRead (originLayout (Fin D × Bool) j A) r c := by
  cases c <;> simp only [headerWord,rank,strideScale,lanes,countField,Option.elim,sliceRead,
    address,active,originStride,add_zero] <;> (try simp only [originLayout]) <;> ac_rfl

/-- For an attained histogram the terminal uses the selector and the two copies of the
matched lanes (one gathered and one distributed over the feeders). -/
theorem terminal_word (j : ℕ) (p : Fin A → ℕ) (hp : ∑ a, p a = j)
    (r : Unit ⊕ Unit ⊕ Fin A) (c : SliceColumn) :
    headerWord (D := D) b (fun i => i.elim j p) (.inr (.inr r,c)) =
      sliceRead (terminalLayout j b p) r c := by
  rcases r with _ | _ | _ <;> cases c <;>
    simp only [headerWord,rank,strideScale,lanes,countField,Option.elim,sliceRead,address,
      active,terminalStride j b p hp,add_zero] <;> (try simp only [terminalLayout,Sum.elim_inl,Sum.elim_inr]) <;> ac_rfl

/-- The arithmetic fit conditions follow from the sizes of the two allocated physical
banks and attainability of the count vector. -/
theorem headerFits_of_capacity (w j : ℕ) (p : Fin A → ℕ) (hp : ∑ a, p a = j)
    (ho : Fintype.card (Fin D × Bool) * (originLayout (Fin D × Bool) j A).stride < 2^w)
    (ht : Fintype.card (Unit ⊕ Unit ⊕ Fin A) * (terminalLayout j b p).stride < 2^w) :
    HeaderFits (D := D) b w (fun i => i.elim j p) := by
  intro r
  rcases r with u | v
  · let L := originLayout (Fin D × Bool) j A
    have hstride : strideScale b (.inl u : Slice D A) * j = L.stride := by
      rw [show L.stride = _ from originStride (P := Fin D × Bool) j A]
      dsimp [strideScale]
      ac_rfl
    change (rank (.inl u : Slice D A) + 1) * (strideScale b (.inl u : Slice D A) * j) < 2^w ∧
      Nat.clog 2 A * j ≤ strideScale b (.inl u : Slice D A) * j
    rw [hstride]
    refine ⟨(Nat.mul_le_mul_right _ (Fintype.equivFin (Fin D × Bool) u).isLt).trans_lt ho, ?_⟩
    rw [Nat.mul_comm]
    exact Finset.single_le_sum (f := fun r => L.copies r * L.lanes r) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
  · let L := terminalLayout j b p
    have hstride : strideScale b (.inr v : Slice D A) * j = L.stride := by
      rw [show L.stride = _ from terminalStride j b p hp]
      exact Nat.mul_comm _ _
    change (rank (.inr v : Slice D A) + 1) * (strideScale b (.inr v : Slice D A) * j) < 2^w ∧
      lanes b (.inr v : Slice D A) * (countField (.inr v : Slice D A)).elim j p ≤ strideScale b (.inr v : Slice D A) * j
    rw [hstride]
    refine ⟨(Nat.mul_le_mul_right _ (Fintype.equivFin (Unit ⊕ Unit ⊕ Fin A) v).isLt).trans_lt ht, ?_⟩
    have h := Finset.single_le_sum (f := fun r => L.copies r * L.lanes r)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    rcases v with _ | _ | _ <;> rw [Nat.mul_comm] <;> exact h

end Packing.BankCircuit

end BorderVNP
end Computability
end OAI
