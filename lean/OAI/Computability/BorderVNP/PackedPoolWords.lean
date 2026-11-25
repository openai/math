import OAI.Computability.BorderVNP.PackedPoolCircuit

/-! # The public bin directory for one simultaneous replacement

The prior scan supplies one binary population at every bin. Permuted counts are shared
between the computations of all direction pools, and each seed's block number and width
are retained once. Reading the width of the inverse seed permutation gives the prefix to
take at the corresponding direction of an old bin.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PoolCircuit

open VPVNP.VerifierNetwork ParseBatchSort Shortening.SeedIntervals
open scoped Classical

/-- Repeat a single Boolean fragment at a fixed array of input wire maps, sharing all
earlier gates and retaining each row of outputs. -/
theorem copies {I O σ A : Type*} [Fintype I] [Fintype O] [Fintype σ] [Fintype A]
    (f : Frame I O) (pins : A → I → σ) :
    ∃ joint : Frame σ (A × O), joint.size ≤ 1 + Fintype.card A * f.size ∧
      ∀ x a j, joint.eval x (a,j) = f.eval (x ∘ pins a) j := by
  let row (a : A) := f.subst (Frame.initial (pins a))
  obtain ⟨g,hg,he⟩ := Crossing.exists_parallelFrames row
  refine ⟨g.select (fun p => ⟨p.1,p.2⟩),?_,?_⟩
  · simpa [row] using hg
  · intro x a j
    rw [Frame.select_eval,he,Frame.subst_eval]
    congr 1
    funext i
    simp [Function.comp_apply]

/-- Count, direction-pool width, number of blocks, common seed width, and the selected
prefix for each direction in an old bin. -/
abbrev LocalWord (D : ℕ) := Fin 4 ⊕ Fin D

/-- Numerical values of the public words of the actual geometric allocator. -/
noncomputable def localWord {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ}
    (N : Crossing.Network D P bits) {A : Type} (bin : N.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (m : ℕ) (a : A) : LocalWord D → ℕ :=
  Sum.elim ![count N bin a, count N bin a / D, blocks N bin perm m a, common N bin perm m a]
    (take N bin perm m a)

/-- All bin records are computed by one DAG of linear size in the number of bins and
polynomial size in the binary word width. Every output denotes the actual geometric quantity. -/
theorem directory_frames (D m : ℕ) [NeZero D] (hm : 0 < m) :
    ∃ C e : ℕ, ∀ w {A : Type} [Fintype A] (perm : Fin D → Equiv.Perm A),
      ∃ f : Frame (A × Fin w) (A × LocalWord D × Fin w),
        f.size ≤ 2 + Fintype.card A * (C*(w+1)^e) ∧
        ∀ {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits)
          (bin : N.Edge → Option A) (x : A × Fin w → Bool),
          (∀ a, value (fun j => x (a,j)) = count N bin a) →
          ∀ a f', value (fun j => f.eval x (a,f',j)) = localWord N bin perm m a f' := by
  obtain ⟨C,e, hs⟩ := seed_frames D m hm
  obtain ⟨C',e', hq⟩ := fixed_division_frames D (NeZero.pos _)
  refine ⟨C'+C,max e e',fun w A _ perm => ?_⟩
  obtain ⟨s,sc,se⟩ := hs w
  obtain ⟨d,dc,de⟩ := hq w
  obtain ⟨seeds,hsize,hseed⟩ := copies s (fun (a : A) (i : Fin D × Fin w) => (perm i.1 a,i.2))
  obtain ⟨pools,psize,hpool⟩ := copies d (fun (a : A) (j : Fin w) => (a,j))
  let raw := Crossing.parallelFrame (Frame.initial (id : A × Fin w → _))
    (Crossing.parallelFrame pools seeds)
  let pins : A × LocalWord D × Fin w → (A × Fin w) ⊕ ((A × Fin w) ⊕ (A × (Fin w ⊕ Fin w))) :=
    fun ⟨a,word,j⟩ => word.elim
      (fun k => ![Sum.inl (a,j), Sum.inr (.inl (a,j)),
        Sum.inr (.inr (a,.inl j)), Sum.inr (.inr (a,.inr j))] k)
      (fun i => Sum.inr (.inr ((perm i).symm a,.inr j)))
  refine ⟨raw.select pins,?_,?_⟩
  · have p : (w+1)^e ≤ (w+1)^(max e e') := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
    have p' : (w+1)^e' ≤ (w+1)^(max e e') := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
    have h1 := sc.trans (Nat.mul_le_mul_left C p)
    have h2 := dc.trans (Nat.mul_le_mul_left C' p')
    simp only [Frame.select_size,raw,Crossing.parallelFrame_size,Frame.initial_size,zero_add]
    calc
      _ ≤ (1 + Fintype.card A * (C' * (w+1)^(max e e'))) +
        (1 + Fintype.card A * (C * (w+1)^(max e e'))) :=
        Nat.add_le_add (psize.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _))
          (hsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h1) _))
      _ = _ := by ring
  · intro P bits N bin x hx a k
    have hbs (a : A) :
        value (fun j => seeds.eval x (a,.inl j)) = blocks N bin perm m a ∧
        value (fun j => seeds.eval x (a,.inr j)) = common N bin perm m a := by
      simp only [hseed, Function.comp_def]
      simpa only [Function.comp_def,hx,blocks,common] using
        se (fun p => x (perm p.1 a,p.2))
    have hp (a : A) : value (fun j => pools.eval x (a,j)) = count N bin a / D := by
      simp only [hpool, Function.comp_def]
      simpa only [Function.comp_apply, hx] using de (fun j => x (a,j))
    cases k with
    | inr i =>
      simpa [pins,raw,localWord,take] using (hbs ((perm i).symm a)).2
    | inl i =>
      fin_cases i
      · simpa [pins,raw,localWord] using hx a
      · simpa [pins,raw,localWord] using hp a
      · simpa [pins,raw,localWord] using (hbs a).1
      · simpa [pins,raw,localWord] using (hbs a).2

end Packing.PoolCircuit

end BorderVNP
end Computability
end OAI
