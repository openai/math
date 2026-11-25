import OAI.Computability.BorderVNP.PackedInheritedWorkWords
import OAI.Computability.BorderVNP.PackedHistoryNamedReceipt

/-! # Work operands from the actual named histogram guess

The total count used by the origin and terminal programs is the sum of the
selected histogram. The individual paid counts are already wires of the
branch encoder. No new matched-count advice is required.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing ParseBatchSort VPVNP.VerifierNetwork Word Shortening Epoch Cover
open PackedHistoryCircuit.Normalized
open private totalExpr total_fits total_value total_nodes from OAI.Computability.BorderVNP.PackedProfileCounts
open private zero zero_size from OAI.Computability.BorderVNP.PackedBankInstall
open scoped Classical

variable {S σ : Type*} [Fintype S] [Fintype σ] {count w : ℕ} (hist : Frame σ (S × Fin count × Fin w))

private noncomputable def optional (z : S × Option (Fin count) × Fin w) : (S × Fin count × Fin w) ⊕ Unit :=
  match z.2.1 with
  | none => .inr ()
  | some i => .inl (z.1,i,z.2.2)

/-- Recover the matched total and every paid multiplicity from the shared
physical guess columns. The total needs only the width of the accepted word. -/
theorem exists_counts :
    ∃ f : Frame σ (S × Option (Fin count) × Fin w), f.size ≤ hist.size + 2 +
      Fintype.card S*(2*count+1)*(100*(w+1)^2) ∧
      ∀ x a, let h := fun i => value (fun j => hist.eval x (a,i,j))
        (∑ i, h i) < 2^w → ∀ i : Option (Fin count),
          value (fun j => f.eval x (a,i,j)) = i.elim (∑ t, h t) h := by
  let src := (parallelFrame hist zero).select optional
  let expr := totalExpr (List.finRange count)
  obtain ⟨sum,hs,hf⟩ := exists_words (Frame.initial (id : S × Option (Fin count) × Fin w → _)) id (fun _ => expr)
  let pick (z : S × Option (Fin count) × Fin w) : (S × Option (Fin count) × Fin w) ⊕ (S × Fin w) :=
    z.2.1.elim (.inr (z.1,z.2.2)) (fun _ => .inl z)
  let f := (sum.withInput.select pick).subst src
  have hsrc : src.size ≤ hist.size+1 := by
    simpa only [src,Frame.select_size,parallelFrame_size] using Nat.add_le_add_left (zero_size (σ := σ)) hist.size
  have cost : sum.size ≤ 1 + Fintype.card S*(2*count+1)*(100*(w+1)^2) := by simpa [expr,total_nodes] using hs
  refine ⟨f,?_,?_⟩
  · simp only [f,Frame.subst_size,Frame.select_size,Frame.withInput_size]
    omega
  · intro x a h fit i
    cases i with
    | some i => simp [f,pick,src,optional,h]
    | none =>
      let env := fun i => value (fun j => src.eval x (a,i,j))
      have he (i : Fin count) : env (some i) = h i := by simp [env,h,src,optional]
      have hsum : ((List.finRange count).map (env ∘ some)).sum = ∑ t,h t := by
        rw [← List.ofFn_id,List.map_ofFn,List.sum_ofFn]
        exact Finset.sum_congr rfl fun i _ => he i
      have hg := hf (src.eval x) a
      simp only [Frame.initial_eval,id_eq] at hg
      have hh := hg (total_fits env _ (hsum.trans_lt fit))
      simpa only [f,pick,Frame.subst_eval,Frame.select_eval,Option.elim_none,Frame.withInput_eval_inr]
        using hh.trans ((total_value env _).trans hsum)

variable {D m k lev old : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {I B P : Type} [Fintype I] [Fintype B] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I old}
variable (s : Stage m B lev child) (room : ∀ a, s.matched a < 2^w) (q : s.Index e)

/-- On the selected real histogram, the sum gate reads the matched count and
each paid template reads its own multiplicity. -/
theorem named_counts {src : Frame σ (((I → Deck (lev+1)) × B) × Fin e.count × Fin w)} {x : σ → Bool}
    (read : src.eval x = NamedReceipt.word s room q)
    (f : Frame σ (((I → Deck (lev+1)) × B) × Option (Fin e.count) × Fin w))
    (hf : ∀ a, let h := fun i => value (fun j => src.eval x (a,i,j))
      (∑ i, h i) < 2^w → ∀ t : Option (Fin e.count), value (fun j => f.eval x (a,t,j)) = t.elim (∑ i, h i) h) :
    ∀ a (t : Option (Fin e.count)), value (fun j => f.eval x (a,t,j)) = t.elim (s.matched a) (q a).val := by
  intro a t
  have h (i : Fin e.count) : value (fun j => src.eval x (a,i,j)) = (q a).val i := by
    rw [read]
    exact (NamedReceipt.word_value s room q a i).symm
  have ht : ∑ i, (q a).val i = s.matched a := (profile_iff_total (q a).val).mp (q a).property
  have hh := hf a
  dsimp only at hh
  simp only [h,ht] at hh
  exact hh (room a) t

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
