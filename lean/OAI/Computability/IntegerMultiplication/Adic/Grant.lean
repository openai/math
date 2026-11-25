import OAI.Computability.IntegerMultiplication.Adic.Grow
import OAI.Computability.IntegerMultiplication.Strip.Across

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open Strip Strip.Dims Code Code.Task
variable {I : Type} {p : ℕ} {n l : I→ℕ} {r : Regime I}
theorem grant (hp : 2 ≤ p) (j : I→ℕ) (h : Regime.Has r (tally ∘ j))
    -- n covers shape
    (e : ∀ i,p^j i ≤ n i) :
    Rip r n l r.header (stackRun (fun i => layout (field p (j i))) fun _ x => send (least x)) := by
  have nP i : 1 ≤ n i := le_trans (Nat.one_le_pow _ _ (by omega)) (e i)
  have hj : Dom r.scale j :=
    (Regime.Small.extent (k := send ∘ tally ∘ j) h).mono (fun i => by
      change _ ≤ size (tally _)
      rw [size_tally,tally_length]; omega)
  -- process stream in two stages: shoots ثم reverse; budget cost proportional via tally_bound
  have t := (Adic.generate p hp).on (fun i : I => tally (j i))
  obtain ⟨k,hK,u⟩ := hj.add (Dom.const r.scale 1)
  let ui := Rip.relay (l:=l) nP (tally ∘ j) (Rip.header nP h) t
    (show ∃ k D : ℕ, ∀ i:I, (((tally (j i)).length+1)*p^(tally (j i)).length:ℕ)+ (1:ℝ) ≤ (D:ℝ)*mass _ _ _ k i from
      ⟨k,hK+1, fun i => by
        rw [tally_length]
        have hu : (j i+1:ℝ)≤hK*(r.scale i+1:ℝ)^k := by exact_mod_cast u i
        have he : ((p^j i:ℕ):ℝ) ≤ n i := by exact_mod_cast e i
        have hx : (j i+1:ℝ)*(p^j i:ℕ)≤ (hK:ℝ)*mass r n l k i := by
          calc
           _ ≤ ((hK:ℝ)*(r.scale i+1:ℝ)^k)*n i := by gcongr
           _ ≤ _ := by
            unfold mass
            have : 0≤(hK:ℝ)*((n i:ℝ)*(l i:ℝ)) := by positivity
            linarith
        have hh := unit_mass (l:=l) (r:=r) nP k i
        push_cast at hx ⊢
        linarith⟩)
  obtain ⟨f,c⟩ := ui
  have g := c.chain (Carries.func c.budget c.out (List.map List.reverse) Easy.reverse.mapping)
  refine ⟨f,?_⟩
  unfold stackRun
  simp_rw [stripe_eq']
  let target (q:ℕ) := (layout (field p q)).tab least
  have eq (q:ℕ) : List.map List.reverse (shoots p (tally q)) = target q := by
    rw [shoots, Series.map_tab]
    change target (tally q).length = target q
    rw [tally_length]
  simpa only [eq] using g

end Adic

end IntegerMultiplication
end Computability
end OAI
