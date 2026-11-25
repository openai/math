import OAI.Computability.BorderVNP.PackedBankCircuit
import OAI.Computability.BorderVNP.PackedBankProfiles

/-! # Physical correctness of the compiled seed bank

The public output words of the bank compiler are the names, endpoints and
widths of the actual cables entering the next combining step. Their address
bounds come directly from the rectangular capacities.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCircuit

open ParseBatchSort VPVNP.VerifierNetwork Shortening StaticRows CombiningStep SeedIntervals

variable {D m : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} {K : Type*} [Field K]
variable (e : Crossing.PaidIdentity K D m) (p : Pack D P bits K)
variable {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable {nSites nEdges nSeeds : ℕ} (oldSite : p.layout.Site ↪ Fin nSites)
variable (oldEdge : p.layout.Edge ↪ Fin nEdges) (seed : A ↪ Fin nSeeds)

/-- Look up the column of a bank cable in the actual sewn network. -/
noncomputable def physical (a : A) (u : TemplateEdge e) : Column → ℕ :=
  let L := (output e p bin perm positive first q).layout
  let edge : L.Edge := .inr (.inr ⟨a,u⟩)
  let sites := siteRows e p oldSite seed
  fun c => match c with
    | .row => (outputRows e p bin perm positive first q oldEdge seed edge).val
    | .source => (sites (L.src edge)).val
    | .destination => (sites (L.dst edge)).val
    | .width => L.width edge

/-- The arithmetic formulas agree with the fields of the actual branch for every cable. -/
theorem read_physical (a : A) (u : TemplateEdge e) (c : Column) :
    read e (fun s => (seed s).val) nSites nEdges a u
      (fun f => f.elim (blocks p.layout bin perm m a) (q a).val) c =
    physical e p bin perm positive first q oldSite oldEdge seed a u c := by
  have hf := bank_fields e p bin perm positive first q a u
  cases c with
  | row => exact (bankRow e p bin perm oldEdge seed a u).symm
  | source =>
    change _ = (siteRows e p oldSite seed _).val
    rw [hf.1]
    exact (siteRow_seed e p oldSite seed a _).symm
  | destination =>
    change _ = (siteRows e p oldSite seed _).val
    rw [hf.2.1]
    exact (siteRow_seed e p oldSite seed a _).symm
  | width => exact hf.2.2.symm

/-- A single Boolean frame implements all the physical bank cable rows on every
accepted histogram branch. Word fit is expressed in terms of the physical capacities
and the actual branch cable widths. -/
theorem exists_physicalFrame {σ : Type*} [Fintype σ] (w : ℕ)
    (source : Frame σ (A × Option (Fin e.count) × Fin w))
    (siteFits : siteCapacity e nSites nSeeds ≤ 2^w)
    (edgeFits : edgeCapacity e nEdges nSeeds ≤ 2^w) :
    ∃ f : Frame σ (A × TemplateEdge e × Column × Fin w),
      f.size ≤ source.size + 1 + Fintype.card A *
        (4 * (∑ u : TemplateEdge e, nodeBudget e u) * (100*(w+1)^2)) ∧
      ∀ (x : σ → Bool) (q : Counts e p bin perm),
        (∀ a i, value (fun j => source.eval x (a,i,j)) = i.elim (blocks p.layout bin perm m a) (q a).val) →
        (∀ a u, physical e p bin perm positive first q oldSite oldEdge seed a u .width < 2^w) →
        ∀ a u c, value (fun j => f.eval x (a,u,c,j)) =
          physical e p bin perm positive first q oldSite oldEdge seed a u c := by
  obtain ⟨f,hs,hf⟩ := exists_bankFrame e (fun s => (seed s).val) nSites nEdges w source
  refine ⟨f,hs,fun x q hx hwidth a u c => ?_⟩
  have hcolumns : read e (fun s => (seed s).val) nSites nEdges a u
        (fun i => value (fun j => source.eval x (a,i,j))) c =
      physical e p bin perm positive first q oldSite oldEdge seed a u c := by
    rw [funext (hx a)]
    exact read_physical e p bin perm positive first q oldSite oldEdge seed a u c
  have hfit : physical e p bin perm positive first q oldSite oldEdge seed a u c < 2^w := by
    cases c with
    | row => exact (outputRows e p bin perm positive first q oldEdge seed _).isLt.trans_le edgeFits
    | source | destination => exact (siteRows e p oldSite seed _).isLt.trans_le siteFits
    | width => exact hwidth a u
  exact (hf x a u c (hcolumns.trans_lt hfit)).trans hcolumns

end Packing.BankCircuit

end BorderVNP
end Computability
end OAI
