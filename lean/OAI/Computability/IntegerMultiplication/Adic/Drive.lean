import OAI.Computability.IntegerMultiplication.Strip.Aero
import OAI.Computability.IntegerMultiplication.Adic.Grant

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Adic
open IntegerMultiplication.Code Strip Strip.Dims IntegerMultiplication.Port
variable {p : ℕ} [NeZero p] (hp : 2 ≤ p)
variable {I : Type} {r : Regime I} (j : I→ℕ)
variable (h : Regime.Has r (tally ∘ j))
abbrev line (p j : ℕ) := layout (field p j)

include hp h in
omit [NeZero p] in
theorem terminal : Station r (fun i => line p (j i)) := by
  have eq (i : ℕ) : field p i = List.replicate i p := by
    induction i <;> simp_all [field,List.replicate_succ]
  apply Station.tape
  · intro i n hn
    rw [eq] at hn
    have : n=p := (List.eq_of_mem_replicate hn)
    exact this ▸ hp
  have hv : (shape ∘ fun (i:I) => field p (j i)) =
      fun i => (tally (j i)).map (fun _ => tally p) := by
    funext i
    simp [shape,eq,tally]
  rw [hv]
  exact h.ez (show Easy (fun (k:Tally) => k.map fun _ => tally p) from by fun_prop)

theorem lineSize (p j) : (line p j).count=p^j := by rw [Strip.Series.total]; exact count

variable {n l : I→ℕ}
noncomputable section

include hp h in
omit [NeZero p] in
theorem marked (g : ∀ i,p^j i ≤ n i) :
    Rip r n l r.header (stackRun (fun i => line p (j i)) (fun _ x => send (least x))) :=
  grant hp j h g

-- positive transform with arbitrary readable offset and arbitrary outer volume n>=size=line length.
include hp h in
theorem motion (g : ∀ i,p^j i ≤ n i) (a b : Nug p) (o : I→Raw p) (t : (i:I)→Tower p (j i))
    (grantO : r.Has o) (pack : ∀ i,Holds (j i) (o i) (t i))
    (v : (i:I)→Block p (j i)→Tree)
    (e : Alive r n l (stackRun (fun i => line p (j i)) v)) :
    Drive r n l (stackRun (fun i => line p (j i)) v)
      (stackRun (fun i => line p (j i)) fun i x => v i ((swift a b (t i)).symm x)) := by
  have pn (i) := ((Nat.one_le_pow (j i) p (by omega)).trans (g i))
  have q := Drive.fetch pn e
  have k := q.chain (marked hp j h g)
  have m := q.chain (clones (terminal hp j h) (by simpa only [lineSize] using g)
    (fun i => send (o i)) grantO)
  obtain ⟨K,f⟩ := Rip.coalesce _ _ m k
  obtain ⟨d,e⟩ := Drive.self pn e
  exact ⟨K+d,keyed j t (fun i _ => o i) (fun i _ => pack i) v a b (e.larger (mass_le (by omega : d≤K+d)))
    (f.larger (mass_le (by omega : K≤K+d)))⟩

include hp h in
theorem dilation (g : ∀ i,p^j i ≤ n i) (a : Span p)
    (v : (i:I)→Block p (j i)→Tree)
    (e : Alive r n l (stackRun (fun i => line p (j i)) v)) :
    Drive r n l (stackRun (fun i => line p (j i)) v)
      (stackRun (fun i => line p (j i)) fun i x => v i ((sweep a (j i)).symm x)) := by
  have pn (i) := ((Nat.one_le_pow (j i) p (by omega)).trans (g i))
  have k := (Drive.fetch pn e).chain (marked hp j h g)
  obtain ⟨d,e⟩ := Drive.self pn e
  obtain ⟨K,f⟩ := k
  exact ⟨K+d,signs j _ _ (e.larger (mass_le (by omega : d≤K+d)))
    (f.larger (mass_le (by omega : K≤K+d)))⟩

end
end Adic

end IntegerMultiplication
end Computability
end OAI
