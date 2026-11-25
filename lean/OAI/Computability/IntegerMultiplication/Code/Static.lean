import OAI.Computability.IntegerMultiplication.Code.List
import OAI.Computability.IntegerMultiplication.Code.Finite

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code.Task
variable {X Y U : Type*}

/-- Finite interpolation allowed where both query and reply have bounded size.
Only applies on the promised ghost domain. `he` states that the answer is determined
by the actual input. All constants/tables are independent of U data. -/
theorem restricted (t : U → ℕ) (q w : U → Tree) (k m : ℕ)
    (h : ∀ i, (q i).count ≤ k) (g : ∀ i, (w i).count ≤ m)
    (he : ∀ i j, q i=q j → w i=w j) : Task t q w := by
  classical
  let c (v : Tree) := if hl : ∃ i, q i=v then Task.prepare 0 (w hl.choose) else Prog.pass
  have hm (i : U) : c (q i)=Task.prepare 0 (w i) := by
    unfold c
    split
    · next e => exact congrArg _ (he _ i e.choose_spec)
    · next e => simp_all
  exact ⟨parse k 0 c,5*m+4*k,fun i env r =>
    (fits_parse _ _ _ _ _ _ _ _ (by rw [hm]; exact fits_prepare 0 (w i) _ _) (h i)).mono (by
      have e₁ := h i
      have e₂ := g i
      rw [Nat.mul_add,Nat.mul_one]
      omega)⟩

/-- Query (forest l, p), branch on whether l is empty using constant overhead. -/
theorem byForest (f : X → Tree) {l : U → List X} {p v : U → Tree} {t : U → ℕ}
    (a : Task (fun i : {i // l i=[]} => t i.val) (fun i => p i.val) (fun i => v i.val))
    (b : Task (fun i : {i // l i≠[]} => t i.val)
      (fun i => .fork (forest f (l i.val)) (p i.val)) (fun i => v i.val)) :
    Task t (fun i => .fork (forest f (l i)) (p i)) v := by
  obtain ⟨c,C,hc⟩ := a
  obtain ⟨d,D,hd⟩ := b
  refine ⟨splitRoot 0 (fun _ => .pass)
    (splitRoot 0 (fun _ => c) (.join (pack 0) (.join (pack 0) d))),
    C+D+20, fun i env r => ?_⟩
  cases e : l i with
  | nil =>
    have h := hc ⟨i,e⟩ env r
    beta_reduce
    rw [e]
    refine (fits_pair (fits_bit (c := fun _ => c) (b:=false) h)).mono ?_
    simp only [Nat.add_mul]
    omega
  | cons x y =>
    have h := hd ⟨i,by simp [e]⟩ env r
    simp only [e] at *
    refine (fits_pair (fits_pair ((fits_pack (f x) (forest f y) (pile 0 (p i) r) _ _).join ((fits_pack _ _ _ _ _).join h)))).mono ?_
    simp only [Nat.add_mul]
    omega
end Code.Task

end IntegerMultiplication
end Computability
end OAI
