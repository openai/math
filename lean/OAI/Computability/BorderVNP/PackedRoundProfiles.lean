import OAI.Computability.BorderVNP.PackedOldDirectory
import OAI.Computability.BorderVNP.PackedBankPhysical

/-! # Matched-size and guessed-histogram words for a physical combining round

The same population used to cut the cables supplies the block number for every seed.
All other words come from the fixed guessed bits. The Boolean count checks and the tensor
summands therefore use exactly the same profile, including at seeds with zero blocks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DirectoryCircuit

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open VPVNP.VerifierNetwork ParseBatchSort BankCircuit
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- All input words of the paid-bank computation, evaluated on the real profile bits. -/
theorem histogram_frames (hm : 0 < m) :
    ∃ C E : ℕ, ∀ (M k w : ℕ) {A : Type} {σ : Type*} [Fintype A] [Fintype σ]
      (p : PublicPopulation.Pins (Fin M) σ k w) (code : A ↪ Fin (2^k)) (perm : Fin D → Equiv.Perm A)
      (guess : A → Fin e.count → Fin w → σ),
      ∃ f : Frame σ (A × Option (Fin e.count) × Fin w),
        f.size ≤ (PublicPopulation.frame p code).size + 2 + Fintype.card A * (C*(w+1)^E) ∧
        ∀ {P : Type*} {bits : P → ℕ} (N : Network D P bits) (bin : N.Edge → Option A)
          (slot : N.Edge ↪ Fin M) (x : σ → Bool),
          PublicPopulation.Represents p N bin slot code x → (∀ a, count N bin a < 2^w) →
          let j := blocks (Names.denseLayout N slot) (CutCircuit.denseBin N slot bin) perm m
          (∀ a, value (fun i => f.eval x (a,none,i)) = j a) ∧
          (∀ a t i, f.eval x (a,some t,i) = x (guess a t i)) := by
  obtain ⟨C,E,hdir⟩ := PoolCircuit.directory_frames D m hm
  refine ⟨C,E,fun M k w A σ _ _ p code perm guess => ?_⟩
  obtain ⟨dir,hs,he⟩ := hdir w perm
  let pop := PublicPopulation.frame p code
  let result := parallelFrame (Frame.initial (id : σ → σ)) (dir.subst pop)
  let read (z : A × Option (Fin e.count) × Fin w) : σ ⊕ (A × PoolCircuit.LocalWord D × Fin w) :=
    z.2.1.elim (.inr (z.1,.inl 2,z.2.2)) (fun t => .inl (guess z.1 t z.2.2))
  refine ⟨result.select read,?_,?_⟩
  · simp only [Frame.select_size,result,parallelFrame_size,Frame.initial_size,zero_add,Frame.subst_size]
    exact (Nat.add_le_add_left hs _).trans_eq (by dsimp [pop]; omega)
  · intro P bits N bin slot x hx fit j
    let L := Names.denseLayout N slot
    let labels := CutCircuit.denseBin N slot bin
    have hp := PublicPopulation.frame_count p L labels (CutCircuit.denseRows N slot) code x
      (CutCircuit.dense_represents N slot bin p code x hx)
      (fun a => (CutCircuit.dense_count N slot bin a).trans_lt (fit a))
    constructor
    · intro a
      simpa [read,result,Frame.subst_eval,PoolCircuit.localWord,j,L,labels] using
        he L labels (pop.eval x) hp a (.inl 2)
    · intro a t i
      simp [read,result]

/-- A fixed multiplier bounds the word widths of every seed-bank cable at an accepted profile. -/
noncomputable def widthMultiplier : ℕ := 1 + ∑ u : TemplateEdge e, (BankCircuit.operand e u).2

/-- Every seed profile has at most as many blocks as the total incoming width of one of its bins. -/
theorem blocks_le_count {P : Type*} {bits : P → ℕ} (N : Network D P bits) {A : Type}
    (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (a : A) :
    blocks N bin perm m a ≤ count N bin (perm 0 a) := by
  let f := fun i : Fin D => count N bin (perm i a) / D
  have hmin : Epoch.leastCount f ≤ f 0 := Finset.min'_le _ _ (Finset.mem_image_of_mem f (Finset.mem_univ 0))
  exact (Nat.div_le_self _ _).trans (hmin.trans (Nat.div_le_self _ _))

/-- The physical cable widths of the successor fit a word if the fixed bank multiplier times
each input population fits. This bound is independent of the history's actual histogram. -/
theorem physical_width_fits {P : Type*} {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool)
    (first : Fin D × Bool) (q : Counts e p bin perm) {nSites nEdges nSeeds w : ℕ}
    (oldSite : p.layout.Site ↪ Fin nSites) (old : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)
    (room : ∀ a, widthMultiplier e * count p.layout bin a < 2^w) (a : A) (u : TemplateEdge e) :
    BankCircuit.physical e p bin perm positive first q oldSite old seed a u .width < 2^w := by
  let j := blocks p.layout bin perm m a
  have hterm (t : Fin e.count) : (q a).val t ≤ j :=
    (Finset.single_le_sum (f := (q a).val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)).trans_eq
      (profileCounts_total e _ q a)
  let mul := (BankCircuit.operand e u).2
  have hm : mul ≤ widthMultiplier e :=
    (Finset.single_le_sum (f := fun z => (BankCircuit.operand e z).2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ u)).trans (Nat.le_add_left _ _)
  have hwidth : BankCircuit.physical e p bin perm positive first q oldSite old seed a u .width ≤ mul*j := by
    rw [← BankCircuit.read_physical e p bin perm positive first q oldSite old seed a u .width]
    rcases u with u | ⟨t,v⟩ | ⟨t,z⟩
    · exact (Nat.mul_comm _ _).le
    · exact (Nat.mul_le_mul_right _ (hterm t)).trans_eq (Nat.mul_comm _ _)
    · exact (Nat.mul_le_mul_right _ (hterm t)).trans_eq (Nat.mul_comm _ _)
  exact hwidth.trans_lt ((Nat.mul_le_mul hm (blocks_le_count p.layout bin perm a)).trans_lt (room _))

end Packing.DirectoryCircuit

end BorderVNP
end Computability
end OAI
