import OAI.Computability.BorderVNP.PackedInheritedWorkInstalled

/-! # Transporting the computed widths with a densely saved named state -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Epoch Cover PackedHistoryCircuit.Normalized VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {V w : ℕ} {σ : Type*} [Fintype σ] {N : Type*}

/-- A second circuit reads the same named word when each corresponding bit
agrees on the actual assignment. Both live and unused row facts transfer. -/
theorem Covers.of_bits {τ : Type*} [Fintype τ] {name : N ↪ Fin V} {width : N → ℕ}
    {f : Frame σ (Fin V × Fin w)} {g : Frame τ (Fin V × Fin w)} {x : σ → Bool} {y : τ → Bool}
    (hf : Covers name width f x) (hg : ∀ i j, g.eval y (i,j) = f.eval x (i,j)) : Covers name width g y := by
  constructor
  · intro v; simpa only [hg] using hf.live v
  · intro i hi; simpa only [hg] using hf.hole i hi

/-- Equality of numerical widths survives a change of names between equal
site capacities. The returned field uses the actual integer row. -/
theorem Covers.resize {U : ℕ} (eq : U=V) (id : N ↪ Fin U) {amt : N → ℕ}
    {f : Frame σ (Fin V × Fin w)} {x : σ → Bool} (hf : Covers (id.trans (finCongr eq).toEmbedding) amt f x) :
    Covers id amt (f.select fun z => (Fin.cast eq z.1,z.2)) x := by
  subst V
  exact hf.of_bits (fun _ _ => by simp only [Frame.select_eval,Fin.cast_refl,id_eq])

variable {D lev E : ℕ} {K P : Type} {bits : P → ℕ} {p saved : PlacedPack D P bits K (Cube D) lev}
variable {fin fin' : Fintype P} (dir : Directory p V E) (names : Directory saved V E)
variable (eq : saved = p.dense dir.cables) (named : HEq names dir.dense)
variable (installed : @Site.Programs D P fin bits p.pack.layout) (f : Frame σ (Fin V × Fin w)) (x : σ → Bool)

include named in
/-- Keep the complete numerical width word, including zero holes, while
transporting the installed program through the actual second dense save. -/
theorem Covers.stored (measure : Site → ℕ)
    (h : Covers dir.sites (fun v => measure (installed v).program) f x) :
    Covers names.sites (fun v => measure ((carryPrivatePrograms p saved dir.cables eq (fin' := fin') installed v).program))
      f x := by
  subst saved
  cases eq_of_heq named
  exact h

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
