import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI
/-! # Monochromatic chains from large-set sampler mixing -/

namespace Hierarchy.AdaptiveProbe
open Finset
noncomputable section

variable {V : Type*} [Fintype V]

def SamplerMixes (edge : V → V → Prop) (a : ℕ) : Prop :=
  ∀ A B : Finset V, a≤A.card → a≤B.card → ∃ x ∈ A, ∃ y ∈ B, edge x y

omit [Fintype V] in
/-- Distinct input and output positions suffice for the actual partial tile matching. -/
theorem SamplerMixes.on_tiles {T : Type*} [Fintype T] {edge : V → V → Prop} {a : ℕ}
    (mix : SamplerMixes edge a) (output input : T ↪ V) :
    SamplerMixes (fun i j => edge (output i) (input j)) a := by
  intro A B largeA largeB
  obtain ⟨x,hx,y,hy,adj⟩ := mix (A.map output) (B.map input) (by simpa using largeA)
    (by simpa using largeB)
  obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hy
  exact ⟨u,hu,v,hv,adj⟩

private def Ends (edge : V → V → Prop) (layer : ℕ → Finset V) (n : ℕ) (v : V) :=
  ∃ f : ℕ → V, f n=v ∧ (∀ j, j≤n → f j ∈ layer j) ∧ (∀ j, j<n → edge (f j) (f (j+1)))

omit [Fintype V] in
private theorem extend {edge : V → V → Prop} {layer : ℕ → Finset V} {n : ℕ} {v w : V}
    (prev : Ends edge layer n v) (inside : w ∈ layer (n+1)) (adj : edge v w) :
    Ends edge layer (n+1) w := by
  obtain ⟨f,hf,hs,he⟩ := prev
  refine ⟨fun j => if j=n+1 then w else f j,by simp,?_,?_⟩
  · intro j hj
    dsimp only
    split
    · rename_i e; simpa only [e] using inside
    · exact hs j (by omega)
  · intro j hj
    dsimp only
    rw [ite_eq_right (by omega : j ≠ n+1)]
    split
    · rename_i e
      have jn : j=n := by omega
      simpa only [jn,hf] using adj
    · simpa using he j (by omega)

omit [Fintype V] in
/-- Each stage of a reachable path has at least a positions as soon as the layer contains
2a tiles and the previous stage contains a reachable outputs. -/
private theorem reachable (edge : V → V → Prop) (layer : ℕ → Finset V) (a : ℕ)
    (mix : SamplerMixes edge a) (n : ℕ) (large : ∀ j, j≤n → 2*a≤(layer j).card) :
    ∃ A : Finset V, a≤A.card ∧ ∀ v ∈ A, Ends edge layer n v := by
  classical
  induction n with
  | zero =>
    refine ⟨layer 0,by have := large 0 le_rfl; omega,fun v hv => ?_⟩
    exact ⟨fun _ => v,rfl,fun j hj => by simpa only [Nat.le_zero.mp hj] using hv,
      fun j hj => by omega⟩
  | succ n ih =>
    obtain ⟨A,ha,ends⟩ := ih (fun j hj => large j (by omega))
    let B := layer (n+1)
    let next := B.filter fun y => ∃ x ∈ A, edge x y
    have bad : (B\next).card<a := by
      by_contra! h
      obtain ⟨x,hx,y,hy,e⟩ := mix A _ ha h
      obtain ⟨hyB,hno⟩ := Finset.mem_sdiff.mp hy
      exact hno (Finset.mem_filter.mpr ⟨hyB,x,hx,e⟩)
    have count := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ B : next ⊆ B)
    change (B\next).card+next.card=B.card at count
    refine ⟨next,by have := large (n+1) le_rfl; change 2*a≤B.card at this; omega,?_⟩
    intro y hy
    obtain ⟨hyB,x,hx,e⟩ := Finset.mem_filter.mp hy
    exact extend (ends x hx) hyB e

omit [Fintype V] in
/-- The sampler connects H distinct tiles of one mark whenever at least 2Ha remain.
Ports may use an arbitrary matching from tile inputs to tile outputs. -/
theorem exists_sampler_chain {edge : V → V → Prop} (a H : ℕ) (ha : 0<a) (hH : 0<H)
    (mix : SamplerMixes edge a) (left : Finset V) (many : H*(2*a)≤left.card) :
    ∃ walk : Fin H ↪ V, (∀ j, walk j ∈ left) ∧
      ∀ j : ℕ, ∀ hj : j+1<H, edge (walk ⟨j,by omega⟩) (walk ⟨j+1,hj⟩) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin H × Fin (2*a)) ≤ Fintype.card left by simpa using many)
  let block (j : Fin H) : Fin (2*a) ↪ V :=
    ⟨fun t => (e (j,t)).val,fun x y eq => congrArg Prod.snd (e.injective (Subtype.ext eq))⟩
  let layer (j : ℕ) := if h : j<H then Finset.univ.map (block ⟨j,h⟩) else ∅
  have mem {j : ℕ} (h : j<H) {v} (hv : v ∈ layer j) : ∃ t : Fin (2*a), (e (⟨j,h⟩,t)).val=v := by
    rw [show layer j = Finset.univ.map (block ⟨j,h⟩) from dite_eq_left h] at hv
    obtain ⟨t,_,val⟩ := Finset.mem_map.mp hv
    exact ⟨t,val⟩
  have large (j : ℕ) (hj : j≤H-1) : 2*a≤(layer j).card := by
    have lt : j<H := by omega
    simp [layer,lt]
  obtain ⟨A,hc,ends⟩ := reachable edge layer a mix (H-1) large
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (ha.trans_le hc)
  obtain ⟨f,_,loc,adj⟩ := ends v hv
  have witness (j : Fin H) := mem j.isLt (loc j (by omega))
  refine ⟨⟨fun j => f j,?_⟩,?_,?_⟩
  · intro i j eq
    obtain ⟨s,hs⟩ := witness i
    obtain ⟨t,ht⟩ := witness j
    exact congrArg Prod.fst (e.injective (Subtype.ext (hs.trans (eq.trans ht.symm))))
  · intro j
    obtain ⟨s,hs⟩ := witness j
    change f j ∈ left
    rw [←hs]
    exact (e (j,s)).property
  · intro j hj
    exact adj j (by omega)

omit [Fintype V] in
/-- Maximality bounds the unused tiles of each fixed mark within each group. -/
theorem remaining_tiles_lt {edge : V → V → Prop} (a H : ℕ) (ha : 0<a) (hH : 0<H)
    (mix : SamplerMixes edge a) (left : Finset V)
    (maximal : ∀ walk : Fin H ↪ V, (∀ j, walk j ∈ left) →
      ¬ ∀ j : ℕ, ∀ hj : j+1<H, edge (walk ⟨j,by omega⟩) (walk ⟨j+1,hj⟩)) :
    left.card < H*(2*a) := by
  by_contra! many
  obtain ⟨walk,inside,path⟩ := exists_sampler_chain a H ha hH mix left many
  exact maximal walk inside path

end
end Hierarchy.AdaptiveProbe

end OAI
