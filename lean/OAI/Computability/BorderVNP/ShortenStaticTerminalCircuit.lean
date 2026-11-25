import OAI.Computability.BorderVNP.PackedPoolCircuit
import OAI.Computability.BorderVNP.ShortenStaticRowsAccess

/-!
# Writing terminal-site names from the inverse seed permutation

For each candidate hook the axis is known from the static layout. A shared
Boolean circuit supplies the seed number. Two fixed-scale additions compute
the positive and negative terminal rows; the orientation selector can choose
either one without duplicating the circuit producing the seed numbers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.StaticTerminalCircuit

open Packing Packing.Word ParseBatchSort VPVNP.VerifierNetwork StaticRows
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : Crossing.PaidIdentity K D m)

/-- The physical template row of one of the two signed terminals on the given axis. -/
noncomputable def terminalCode (d : Fin D) (side : Bool) : Fin (Fintype.card (TemplateSite e)) :=
  Fintype.equivFin (TemplateSite e) (.inr (.inl (d,side)))

/-- The reserved rectangle's address at a dynamic seed number. -/
noncomputable def address (oldSites : ℕ) (d : Fin D) (side : Bool) (seed : ℕ) : ℕ :=
  oldSites + ((terminalCode e d side).val + Fintype.card (TemplateSite e) * seed)

/-- This arithmetic address is the actual terminal site in the sewn network's
static row embedding. -/
theorem address_eq_siteRow {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} {oldSites seeds : ℕ} (old : p.layout.Site ↪ Fin oldSites)
    (seed : A ↪ Fin seeds) (a : A) (d : Fin D) (side : Bool) :
    address e oldSites d side (seed a).val =
      (siteRows e p old seed (.inr ⟨a,.inr (.inl (d,side))⟩)).val := rfl

/-- All addresses fit a single word whenever the static site rectangle fits. -/
theorem address_fits (oldSites seeds w : ℕ) (d : Fin D) (side : Bool) {seed : ℕ}
    (hs : seed < seeds) (hcapacity : siteCapacity e oldSites seeds ≤ 2^w) :
    address e oldSites d side seed < 2^w := by
  apply lt_of_lt_of_le _ hcapacity
  unfold address siteCapacity
  apply Nat.add_lt_add_left
  calc
    (terminalCode e d side).val + Fintype.card (TemplateSite e) * seed
        < Fintype.card (TemplateSite e) + Fintype.card (TemplateSite e) * seed :=
      Nat.add_lt_add_right (terminalCode e d side).isLt _
    _ = Fintype.card (TemplateSite e) * (seed+1) := by ring
    _ ≤ seeds * Fintype.card (TemplateSite e) := by
      rw [Nat.mul_comm seeds]
      exact Nat.mul_le_mul_left _ hs

private noncomputable def expression (oldSites : ℕ) (d : Fin D) (side : Bool) : WidthExpr Unit :=
  .binary .add (.const (oldSites + (terminalCode e d side).val))
    (PoolCircuit.scaleExpr () (Fintype.card (TemplateSite e)))

/-- Number of word-expression nodes per signed terminal; it depends only on the fixed template. -/
def nodeBudget : ℕ := (PoolCircuit.scaleExpr () (Fintype.card (TemplateSite e))).nodes + 2

private theorem expression_value (oldSites : ℕ) (d : Fin D) (side : Bool) (x : Unit → ℕ) :
    (expression e oldSites d side).eval x = address e oldSites d side (x ()) := by
  simp only [expression, WidthExpr.eval, Op.apply, PoolCircuit.scale_eval, address, Nat.add_assoc]

private theorem expression_fits (oldSites w : ℕ) (d : Fin D) (side : Bool) (x : Unit → ℕ)
    (hx : x () < 2^w) (haddr : address e oldSites d side (x ()) < 2^w) :
    (expression e oldSites d side).Fits w x := by
  unfold address at haddr
  refine ⟨by change oldSites + _ < _; omega, PoolCircuit.scale_fits _ _ _ _ hx (by omega), ?_⟩
  simpa only [Op.apply, WidthExpr.eval, PoolCircuit.scale_eval, Nat.add_assoc] using haddr

private theorem expression_nodes (oldSites : ℕ) (d : Fin D) (side : Bool) :
    (expression e oldSites d side).nodes = nodeBudget e := by
  change 1 + (PoolCircuit.scaleExpr () (Fintype.card (TemplateSite e))).nodes + 1 =
    (PoolCircuit.scaleExpr () (Fintype.card (TemplateSite e))).nodes + 2
  omega

/-- Compute both signed endpoint addresses for every candidate in parallel.
All candidates share the source frame, so its gates are charged once. -/
theorem exists_terminalFrame {U σ : Type*} [Fintype U] [Fintype σ] (oldSites : ℕ)
    (axis : U → Fin D) (w : ℕ) (source : Frame σ (U × Fin w)) :
    ∃ f : Frame σ (U × Bool × Fin w),
      f.size ≤ source.size + 1 + Fintype.card U * (2 * nodeBudget e * (100*(w+1)^2)) ∧
      ∀ (x : σ → Bool) (u : U) (side : Bool),
        let seed := value (fun j => source.eval x (u,j))
        address e oldSites (axis u) side seed < 2^w →
        value (fun j => f.eval x (u,side,j)) = address e oldSites (axis u) side seed := by
  let single (v : U × Bool) :=
    ((expression e oldSites (axis v.1) v.2).frame w).subst
      (Frame.initial (fun z : Unit × Fin w => (v.1,z.2)))
  obtain ⟨joint,hsize,heval⟩ := Crossing.exists_parallelFrames single
  let out (z : U × Bool × Fin w) : Σ _ : U × Bool, Fin w := ⟨(z.1,z.2.1),z.2.2⟩
  refine ⟨(joint.select out).subst source, ?_, ?_⟩
  · have hs (v : U × Bool) : (single v).size ≤ nodeBudget e * (100*(w+1)^2) := by
      simp only [single, Frame.subst_size, Frame.initial_size, zero_add]
      simpa only [expression_nodes] using (expression e oldSites (axis v.1) v.2).frame_size w
    have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hs v)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
      nsmul_eq_mul] at h
    change (∑ v : U × Bool, (single v).size) ≤ (Fintype.card U * 2) *
      (nodeBudget e * (100*(w+1)^2)) at h
    have hsum : joint.size ≤ 1 + Fintype.card U * (2 * nodeBudget e * (100*(w+1)^2)) := by
      apply hsize.trans
      exact Nat.add_le_add_left (by simpa only [Nat.mul_assoc] using h) 1
    simp only [Frame.subst_size, Frame.select_size]
    omega
  · intro x u side seed h
    let z (i : Unit × Fin w) := source.eval x (u,i.2)
    let fields (i : Unit) := value (fun j => z (i,j))
    have hv : (fun j => ((joint.select out).subst source).eval x (u,side,j)) =
        ((expression e oldSites (axis u) side).frame w).eval z := by
      funext j
      simp [Frame.subst_eval, out, heval, single, z]
      congr 1
      funext i
      simp
    rw [hv]
    exact ((expression e oldSites (axis u) side).frame_value w z
      (expression_fits e oldSites w (axis u) side fields (value_lt _) h)).trans
      (expression_value e oldSites (axis u) side fields)

end Shortening.StaticTerminalCircuit

end BorderVNP
end Computability
end OAI
