import OAI.Computability.BorderVNP.PackedBandCircuit
import OAI.Computability.BorderVNP.ShortenPublicPopulation

/-! # Computing and scattering the band boundaries to the live cables

Only one copy of the population and pool computations is run. A sorted batch of sparse
queries returns the cut positions from each live cable's own bin, even when the assignment
of cable rows to bins depends on all earlier public profiles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PoolCircuit

open VPVNP.VerifierNetwork ParseBatchSort Shortening Shortening.SeedIntervals
open scoped Classical

/-- Read every field of a sparse table at the dynamic address of each query. Independent
fields share all gates of the source, including the computation of addresses and payloads. -/
theorem table_reads {A U F σ : Type*} [Fintype A] [Fintype U] [Fintype F] [Fintype σ]
    (k w : ℕ) (code : A ↪ Fin (2^k)) (field : A → F → Fin w → σ) (addr : U → Fin k → σ) :
    let n := Fintype.card A + Fintype.card U
    ∃ f : Frame σ (U × F × Fin w),
      f.size ≤ 1 + Fintype.card F * (2*(n+1)*PublicPopulation.laneCost (Nat.clog 2 n) k w) ∧
      ∀ x u a, value (x ∘ addr u) = (code a).val →
        ∀ f' j, f.eval x (u,f',j) = x (field a f' j) := by
  intro n
  let row (v : F) := PackedLookup.lookup (PackedHistogram.layout A U) code
    (fun a j => .input (field a v j)) (fun u j => .input (addr u j))
  obtain ⟨joint,hj,he⟩ := Crossing.exists_parallelFrames row
  refine ⟨joint.select (fun z => ⟨z.2.1,(z.1,z.2.2)⟩),?_,?_⟩
  · have hpad : 2^(Nat.clog 2 n) ≤ 2*(n+1) := by
      by_cases hz : n = 0
      · simp [hz]
      · exact (PackedHistogram.layout_size A U (Nat.pos_of_ne_zero hz)).le.trans (by dsimp [n]; omega)
    have hr (v : F) : (row v).size ≤ 2*(n+1)*PublicPopulation.laneCost (Nat.clog 2 n) k w := by
      refine (PackedHistogram.queries_size _ _ _ _ 3 (by decide)
        (fun _ _ => by change 1 ≤ 3; decide)
        (fun _ _ => by change 1 ≤ 3; decide)
        (fun _ _ => by change 1 ≤ 3; decide)).trans ?_
      exact Nat.mul_le_mul_right _ hpad
    rw [Frame.select_size]
    apply hj.trans (Nat.add_le_add_left _ 1)
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun v _ => hr v)
  · intro x u a hu v j
    rw [Frame.select_eval,he]
    exact PackedLookup.lookup_bits (PackedHistogram.layout A U) code
      (fun a j => .input (field a v j)) (fun u j => .input (addr u j)) x u a hu j

/-- The combined gate count for compiling bin populations, their pool directories, all
band endpoints and one scatter of those endpoints back to every sparse old row. -/
def scatterCost (A U D C e k w : ℕ) : ℕ :=
  let n := A+U
  let sort := 2*(n+1)*PublicPopulation.laneCost (Nat.clog 2 n) k w
  sort + (2 + A*(C*(w+1)^e)) + 1 + A*(endpointNodes D*(100*(w+1)^2)) +
    (1 + Fintype.card (Band D × Bool) * sort)

/-- A single deterministic Boolean DAG returns the geometric allocator's cut endpoints
at the reserved slot of each charged cable. Both its bin and its pool widths are dynamic. -/
theorem scatter_frames (D m : ℕ) [NeZero D] (hm : 0 < m) :
    ∃ C e : ℕ, ∀ (k w : ℕ) {A : Type} {U σ : Type*} [Fintype A] [Fintype U] [Fintype σ]
      (p : PublicPopulation.Pins U σ k w) (code : A ↪ Fin (2^k)) (perm : Fin D → Equiv.Perm A),
      ∃ f : Frame σ (U × (Band D × Bool) × Fin w),
        f.size ≤ scatterCost (Fintype.card A) (Fintype.card U) D C e k w ∧
        ∀ {P : Type*} {bits : P → ℕ} (N : Crossing.Network D P bits) (bin : N.Edge → Option A)
          (slot : N.Edge ↪ U) (x : σ → Bool),
          PublicPopulation.Represents p N bin slot code x → (∀ a, count N bin a < 2^w) →
          ∀ c a, bin c = some a → ∀ b r, value (fun j => f.eval x (slot c,(b,r),j)) =
            bandEnd (count N bin a) (count N bin a / D) (take N bin perm m a) b r := by
  obtain ⟨C,e,ds⟩ := directory_frames D m hm
  refine ⟨C,e,fun k w A U σ _ _ _ p code perm => ?_⟩
  obtain ⟨dir,hd,ed⟩ := ds w perm
  let pop := PublicPopulation.frame p code
  let directory := dir.subst pop
  obtain ⟨ends,hs,es⟩ := endpoints_frame D w directory
  let retained := Crossing.parallelFrame (Frame.initial (id : σ → σ)) ends
  let pos := fun (a : A) (f : Band D × Bool) (j : Fin w) =>
    (Sum.inr (a,f.1,f.2,j) : σ ⊕ (A × Band D × Bool × Fin w))
  let addr := fun u j => (Sum.inl (p.key u j) : σ ⊕ (A × Band D × Bool × Fin w))
  obtain ⟨reads, hr, er⟩ := table_reads k w code pos addr
  refine ⟨reads.subst retained,?_,?_⟩
  · rw [Frame.subst_size]
    simp only [retained,Crossing.parallelFrame_size,Frame.initial_size,zero_add]
    have hp := PublicPopulation.frame_size p code
    simp only [directory,Frame.subst_size,pop] at hs
    dsimp only [scatterCost]
    dsimp only at hr hp
    rw [Nat.add_comm (Fintype.card U) (Fintype.card A)] at hp
    omega
  · intro P bits N bin slot x hx fit c a hc b r
    have ep := PublicPopulation.frame_count p N bin slot code x hx fit
    have hdir (a : A) (j : LocalWord D) :
        value (fun i => directory.eval x (a,j,i)) = localWord N bin perm m a j := by
      simp only [directory,Frame.subst_eval]
      exact ed N bin (pop.eval x) ep a j
    let fld := fun j : LocalWord D => value (fun i => directory.eval x (a,j,i))
    have hpool : D*fld (.inl 1) ≤ fld (.inl 0) := by
      simpa only [fld,hdir,localWord,Sum.elim_inl,Matrix.cons_val_zero,Matrix.cons_val_one,
        Nat.mul_comm D] using Nat.div_mul_le_self (count N bin a) D
    have htake : ∀ d : Fin D, fld (.inr d) ≤ fld (.inl 1) := by
      intro d
      simpa [fld,hdir,localWord] using take_le N bin perm m a d
    have haddr : value (retained.eval x ∘ addr (slot c)) = (code a).val := by
      have heq : retained.eval x ∘ addr (slot c) = x ∘ p.key (slot c) := by
        funext j
        simp [retained,addr,Function.comp_apply]
      rw [heq]
      exact hx.address c a hc
    have hre : (fun j => (reads.subst retained).eval x (slot c,(b,r),j)) =
        fun j => ends.eval x (a,b,r,j) := by
      funext j
      rw [Frame.subst_eval, er _ _ _ haddr]
      simp [retained,pos]
    rw [hre]
    simpa [hdir,localWord] using es x a hpool htake b r

end Packing.PoolCircuit

end BorderVNP
end Computability
end OAI
