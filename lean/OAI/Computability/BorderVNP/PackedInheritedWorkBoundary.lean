import OAI.Computability.BorderVNP.PackedInheritedWorkRouting
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms
import OAI.Computability.BorderVNP.ShortenPublicSubdivisionRows

/-! # Work words at the subdivision and parallel boundaries

Subdivision retains the whole previous extent at an original site and needs
zero work at each inserted relay. Parallelization concatenates the child
rectangles by their permanent product numbering without adding arithmetic.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.PublicCapacity Shortening.PublicParallel ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private zero zero_size false_word from OAI.Computability.BorderVNP.PackedBankInstall
open scoped Classical

variable {σ : Type*} [Fintype σ] {s : Shape} {w : ℕ}

/-- Reuse the old width rectangle and route one shared zero to every reserved
intermediate site. Unused old rows retain their previous zero words. -/
noncomputable def subdivision (extra : ℕ) (prev : Frame σ (Fin s.sites × Fin w)) :
    Frame σ (Fin (s.subdivide extra).sites × Fin w) :=
  (parallelFrame prev zero).select fun z =>
    match finSumFinEquiv.symm z.1 with
    | .inl i => .inl (i,z.2)
    | .inr _ => .inr ()

theorem subdivision_size (extra : ℕ) (prev : Frame σ (Fin s.sites × Fin w)) :
    (subdivision extra prev).size ≤ prev.size+1 := by
  simpa [subdivision] using Nat.add_le_add_left (zero_size (σ := σ)) prev.size

/-- Both old and inserted physical programs have exactly the work in this
public table, including subdivisions with inactive or zero-width cables. -/
theorem subdivision_covers {D np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (r : N.WireRoutes) (rows : Rows s N) (extra : ℕ)
    (fits : ∀ e, r.interior e ≤ extra) (ports : P ↪ Fin np) (prior : Site.Programs N)
    (prev : Frame σ (Fin s.sites × Fin w)) (x : σ → Bool)
    (hw : Covers rows.site (fun v => (prior v).program.size) prev x) :
    let next := rows.subdivide r extra fits
    let program := Subdivision.subdividePrivatePrograms N r rows.edge next.edge ports prior
    Covers next.site (fun v => (program v).program.work) (subdivision extra prev) x := by
  intro next program
  have old (i : Fin s.sites) (j : Fin w) :
      (subdivision extra prev).eval x (finSumFinEquiv (.inl i),j) = prev.eval x (i,j) := by
    simp only [subdivision,Frame.select_eval,Equiv.symm_apply_apply,parallelFrame_eval_inl]
  have fresh (i : Fin (extra*s.edges)) (j : Fin w) :
      (subdivision extra prev).eval x (finSumFinEquiv (.inr i),j) = false := by
    simp only [subdivision,Frame.select_eval,Equiv.symm_apply_apply,parallelFrame_eval_inr,zero,
      Frame.step_eval,StatementCircuit.Expr.eval]
  constructor
  · rintro (v | j)
    · change value (fun j => (subdivision extra prev).eval x (finSumFinEquiv (.inl (rows.site v)),j)) =
        (prior v).program.size
      simpa only [old] using hw.live v
    · let i : Fin (extra*s.edges) := Fin.cast (Nat.mul_comm _ _) (flat (rows.edge j.1) (Fin.castLE (fits j.1) j.2))
      change value (fun k => (subdivision extra prev).eval x (finSumFinEquiv (.inr i),k)) = 0
      simpa only [fresh] using false_word (w := w)
  · intro i hi
    obtain ⟨z,rfl⟩ := finSumFinEquiv.surjective i
    cases z with
    | inl j =>
      have hj : j ∉ Set.range rows.site := by rintro ⟨v,rfl⟩; exact hi ⟨.inl v,rfl⟩
      simpa only [old] using hw.hole j hj
    | inr j => simpa only [fresh] using false_word (w := w)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
