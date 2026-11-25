import OAI.Computability.BorderVNP.ShortenPublicSegmentFrame
import OAI.Computability.BorderVNP.ShortenPreparedLabels

/-!
# Jointly realized geometric labels for the public segment reader

The labels used by the fitted-pack and mean-coverage proofs can be chosen
to agree with the Boolean row circuit simultaneously on all active edges.
The enabled bit is computed from the original charge bit and the presence of
a segment tag, which removes coincident and unused cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Epoch Catalog Crossing PreparedBins PackMotions
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open scoped Classical

variable {D d : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
variable {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
variable (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
variable (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+1))
variable (catalogued : ∀ i v, relative d (sites i v) ∈ S)

/-- The two canonically encoded site payloads of an actual edge in one of the packs. -/
noncomputable def cableBits (i : Fin copies) (e : (input i).layout.Edge) :=
  endpointBits (sites i ((input i).layout.src e)) (sites i ((input i).layout.dst e))
    (catalogued i _) (catalogued i _)

/-- Fitted placement may use the exact type chosen by the circuit on every cable
of every pack. The two endpoints have a common integral lift with unchanged length. -/
theorem labels_of_typeRow {f : Frame (Bool × FieldBit (↥S) (Cube D) (d+1)) B.types}
    (row : TypeRow B d f)
    (positive : ∀ w : Active input active, sites w.1 ((input w.1).layout.src w.2.val) ≠
      sites w.1 ((input w.1).layout.dst w.2.val))
    (short : ∀ w : Active input active, dist (sites w.1 ((input w.1).layout.src w.2.val))
      (sites w.1 ((input w.1).layout.dst w.2.val)) ≤ 2*h) :
    ∃ L : Labels B input active sites, ∀ w : Active input active,
      f.eval (cableBits input sites catalogued w.1 w.2.val) = fun u => decide (u=L.kind w) := by
  have edge (w : Active input active) := row.2 _ _ (catalogued w.1 _) (catalogued w.1 _) (positive w) (short w)
  choose kind represented read using edge
  choose lift src dst len using represented
  exact ⟨⟨kind,lift,src,dst,fun w => (len w).symm.trans (kind w).val.dist_ends⟩,read⟩

/-- The enabled wire tests the original charge and the existence of a type bit.
The circuit shares its type outputs with the following motion table. -/
private noncomputable def enabledExpr {T : Type*} [Fintype T] {X : Type*} :
    Expr ((Unit ⊕ X) ⊕ T) :=
  .and (.input (.inl (.inl ()))) (Expr.disjoin (Finset.univ.toList.map fun t : T => .input (.inr t)))

private theorem enabledExpr_size {T X : Type*} [Fintype T] :
    (enabledExpr (T := T) (X := X)).size ≤ 2*Fintype.card T+3 := by
  let xs := Finset.univ.toList.map fun t : T => (Expr.input (.inr t) : Expr ((Unit ⊕ X) ⊕ T))
  have h := Expr.size_disjoin_le xs 1 fun z hz => by
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    rfl
  change 1+(Expr.disjoin xs).size+1 ≤ _
  dsimp [xs]
  simp [xs] at h
  omega

/-- Forward the type mask and compute one public activity bit from its presence. -/
noncomputable def markRow {T X : Type*} [Fintype T] [Fintype X] (f : Frame X T) :
    Frame (Unit ⊕ X) (Unit ⊕ T) :=
  let typed := (f.subst (Frame.initial Sum.inr)).withInput
  let mark := (Frame.initial id).step fun _ : Unit => enabledExpr (T := T) (X := X)
  (parallelFrame mark (Frame.initial Sum.inr)).subst typed

/-- Gate cost of the charge-and-presence computation. -/
theorem markRow_size {T X : Type*} [Fintype T] [Fintype X] (f : Frame X T) :
    (markRow f).size ≤ f.size + 2*Fintype.card T+3 := by
  have h := Frame.step_size_le (Frame.initial id) (fun _ : Unit => enabledExpr (T := T) (X := X))
    _ (fun _ => enabledExpr_size)
  simpa [markRow, Nat.add_assoc] using Nat.add_le_add_left h f.size

/-- The forwarded type bits are exactly the outputs of the geometric reader. -/
theorem markRow_tag {T X : Type*} [Fintype T] [Fintype X] (f : Frame X T)
    (b : Bool) (x : X → Bool) (t : T) :
    (markRow f).eval (Sum.elim (fun _ => b) x) (.inr t) = f.eval x t := by
  have get : (Frame.initial (Sum.inr : X → Unit ⊕ X)).eval (Sum.elim (fun _ => b) x) = x :=
    funext fun _ => by simp
  simp [markRow,Frame.subst_eval,get,Frame.withInput_eval_inr]

/-- The presence bit ignores zero-length or uncharged wires and accepts every
charged wire carrying a catalog tag. -/
theorem markRow_enabled {T X : Type*} [Fintype T] [Fintype X] (f : Frame X T)
    (b : Bool) (x : X → Bool) :
    (markRow f).eval (Sum.elim (fun _ => b) x) (.inl ()) = true ↔ b = true ∧ ∃ t, f.eval x t = true := by
  have get : (Frame.initial (Sum.inr : X → Unit ⊕ X)).eval (Sum.elim (fun _ => b) x) = x :=
    funext fun _ => by simp
  simp [markRow,Frame.subst_eval,get,Frame.step_eval,enabledExpr,Expr.eval,
    Expr.eval_disjoin_true,Frame.withInput_eval_inl,Frame.withInput_eval_inr]

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
