import OAI.Computability.NearSquareRoot.InterchangeBQuestLocal
import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.IntegerMultiplication.Loom.Fare

/-!
# Resource-bounded oracle bodies for the recursive interchange

One fixed stack command runs against an arbitrary recursive implementation.
The local time allowance is added to the *sum* of child times. The parked
data and continuation depth are added to a *maximum* child allowance,
independently of the number of children.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom NearSquareRoot.Space

variable {I Y : Type} {job : Job Y} {w d : I → ℕ} {uses more : I → List Y}
    {p q v : I → Tree}

/-- A bounded oracle call certificate, uniform over the recursive command,
its external stack environment, and the amounts of child time and space.
The parked caller deck is tracked explicitly at every recursive depth. -/
structure Body (job : Job Y) (w : I → ℕ) (uses : I → List Y) (input output : I → Tree) : Prop where
  build : ∃ (cmd : Cmd) (K : ℕ), ∀ (i : I) (parent : Cmd) (env : Env) (price : Y → ℕ)
    (childSpace childDepth : ℕ),
    (∀ y ∈ uses i, ∀ d base, DeckCap base d →
      BoundedFits (parent::env) parent (pile 0 (job.issue y) d) (pile 0 (job.reply y) d)
        (price y) (base+childSpace) childDepth) →
    ∀ d base, DeckCap base d →
      BoundedFits (parent::env) cmd (pile 0 (input i) d) (pile 0 (output i) d)
        (K*(w i+1)+((uses i).map price).sum)
        (base+K*(w i+1)+childSpace) (K*(w i+1)+childDepth)

namespace Body

theorem mono (h : Body job w uses p q) (hwd : ∀ i, w i ≤ d i) : Body job d uses p q := by
  obtain ⟨c,K,f⟩ := h.build
  refine ⟨c,K,fun i parent env price S D ih stack base hs => ?_⟩
  have hh := Nat.mul_le_mul_left K (Nat.add_le_add_right (hwd i) 1)
  exact (f i parent env price S D ih stack base hs).mono (by omega) (by omega) (by omega)

theorem walkway (h : BoundedTask w w p q) : Body job w (fun _ => []) p q := by
  obtain ⟨c,K,f⟩ := h
  refine ⟨c,K,fun i parent env price S D _ stack base hs => ?_⟩
  exact (f i (parent::env) stack base hs).mono (by simp) (by omega) (by omega)

theorem summon (child : I → Y) : Body job w (fun i => [child i]) (job.issue ∘ child) (job.reply ∘ child) := by
  refine ⟨.again 0,1,fun i _ _ _ _ _ ih stack base hs => ?_⟩
  exact (ih (child i) (List.mem_singleton_self _) stack base hs).again0.mono
    (by simp) (by omega) (by omega)

theorem seam (h : Body job w uses p q) (g : Body job w more q v) :
    Body job w (fun i => uses i ++ more i) p v := by
  obtain ⟨c,K,f⟩ := h.build
  obtain ⟨e,L,t⟩ := g.build
  refine ⟨c.join e,K+L+2,?_⟩
  intro i parent env price S D ih stack base hs
  have hl := f i parent env price S D (fun y hy => ih y (List.mem_append_left _ hy)) stack base hs
  have hr := t i parent env price S D (fun y hy => ih y (List.mem_append_right _ hy)) stack base hs
  let cap := base+(K+L+2)*(w i+1)+S
  let depth := (K+L+2)*(w i+1)+D
  have hl' := hl.mono le_rfl (show _ ≤ cap by dsimp [cap]; rw [Nat.add_mul,Nat.add_mul]; omega) le_rfl
  have hr' := hr.mono le_rfl (show _ ≤ cap by dsimp [cap]; rw [Nat.add_mul,Nat.add_mul]; omega)
    (show _ ≤ depth by dsimp [depth]; rw [Nat.add_mul,Nat.add_mul]; omega)
  have joined := hl'.join hr' (by dsimp [depth]; rw [Nat.add_mul,Nat.add_mul]; omega)
  refine joined.mono ?_ le_rfl le_rfl
  simp only [List.map_append, List.sum_append, Nat.add_mul]
  omega

end Body

/-- A bounded command whose local polynomial header exponent is independent
of child commands and all child resource allocations. -/
structure BQuest (job : Job Y) (r : Regime I) (n l : I → ℕ) (uses : I → List Y)
    (input output : I → Tree) : Prop where
  eligible : ∃ k, Body job (massNat r n l k) uses input output

variable {r : Regime I} {n l : I → ℕ} {zone : I → Y → Prop} {a b : ℤ}

namespace BQuest

theorem entry (h : Rip r n l p q) : BQuest job r n l (fun _ => []) p q := by
  obtain ⟨k,e⟩ := rip_bounded h
  exact ⟨k,Body.walkway e⟩

theorem board (child : I → Y) :
    BQuest job r n l (fun i => [child i]) (job.issue ∘ child) (job.reply ∘ child) :=
  ⟨0,Body.summon _⟩

theorem seam (h : BQuest job r n l uses p q) (g : BQuest job r n l more q v) :
    BQuest job r n l (fun i => uses i ++ more i) p v := by
  obtain ⟨k,f⟩ := h.eligible
  obtain ⟨k',g⟩ := g.eligible
  exact ⟨max k k', (f.mono (massNat_mono r n l (le_max_left ..))).seam
    (g.mono (massNat_mono r n l (le_max_right ..)))⟩

end BQuest

/-- Counted, well-typed oracle requests carrying a bounded fixed command. -/
structure BHop (job : Job Y) (r : Regime I) (n l : I → ℕ) (zone : I → Y → Prop)
    (limit : ℤ) (input output : I → Tree) : Prop where
  safe : ∃ uses : I → List Y, (∀ i y, y ∈ uses i → zone i y) ∧
    (∀ i, (uses i).length ≤ limit) ∧ BQuest job r n l uses input output

namespace BHop

theorem tarry (h : Rip r n l p q) : BHop job r n l zone 0 p q :=
  ⟨fun _ => [], by simp, by simp,BQuest.entry h⟩

theorem summon (child : I → Y) (valid : ∀ i, zone i (child i)) :
    BHop job r n l zone 1 (job.issue ∘ child) (job.reply ∘ child) :=
  ⟨fun i => [child i], fun i y hy => (List.mem_singleton.mp hy) ▸ valid i, by simp, BQuest.board _⟩

theorem seam (h : BHop job r n l zone a p q) (g : BHop job r n l zone b q v) :
    BHop job r n l zone (a+b) p v := by
  obtain ⟨c,hc,cc,fc⟩ := h.safe
  obtain ⟨d,hd,cd,fd⟩ := g.safe
  refine ⟨fun i => c i ++ d i, fun i y hy => (List.mem_append.mp hy).elim (hc i y) (hd i y), ?_, fc.seam fd⟩
  intro i
  simpa only [List.length_append, Nat.cast_add] using add_le_add (cc i) (cd i)

theorem monotone (h : BHop job r n l zone a p q) (hab : a ≤ b) : BHop job r n l zone b p q := by
  obtain ⟨c,hc,cc,fc⟩ := h.safe
  exact ⟨c,hc,fun i => (cc i).trans hab,fc⟩

theorem preceded (h : BHop job r n l zone a q v) (g : Rip r n l p q) :
    BHop job r n l zone a p v := by simpa only [Int.zero_add] using (tarry g).seam h

theorem afterTask (h : BHop job r n l zone a p q) (g : Rip r n l q v) :
    BHop job r n l zone a p v := by simpa only [Int.add_zero] using h.seam (tarry g)

end BHop

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
