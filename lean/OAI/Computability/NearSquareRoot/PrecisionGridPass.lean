import OAI.Computability.NearSquareRoot.PrecisionCartesian
import OAI.Computability.NearSquareRoot.PrecisionBoundedMap
import OAI.Computability.NearSquareRoot.BoundedProgramForget
import OAI.Computability.NearSquareRoot.PrecisionGridTask
import OAI.Computability.NearSquareRoot.PrecisionGridStream

/-! # Framed execution of a prefix-table pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Code

/-- Physical word streams read by the table-expansion program. The local
coefficient records include the shift ruler needed by the product. -/
def tableWords {w : ℕ} (f : ℕ) (t : List (Dusk.Grain w)) : List Grid.Orb :=
  t.map fun y => (tally f, Dusk.mark y)

def prefixWords {w : ℕ} (s : List (Dusk.Grain w)) : List Dusk.Pair := s.map Dusk.mark

def extendTable {w : ℕ} (f : ℕ) (s t : List (Dusk.Grain w)) : List (Dusk.Grain w) :=
  PhaseStream.extend (fun x y => Grid.launch (x, tally f, Dusk.mark y)) s t

@[simp] theorem extendTable_length {w : ℕ} (f : ℕ) (s t : List (Dusk.Grain w)) :
    (extendTable f s t).length = s.length * t.length := PhaseStream.length_extend ..

private theorem map_size_le {α β : Type*} [Codec β] (g : α → β) (s : List α) (b : ℕ)
    (hg : ∀ x ∈ s, size (g x) + 1 ≤ b) : size (s.map g) ≤ s.length * b + 1 := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, size_cons, List.length_cons, Nat.succ_mul]
    have h₁ := hg x (by simp)
    have h₂ := ih (fun q hq => hg q (by simp [hq]))
    omega

theorem tableWords_size {w f : ℕ} (t : List (Dusk.Grain w)) (hf : f ≤ w+1) :
    size (tableWords f t) ≤ t.length * (12*(w+1))+1 := by
  apply map_size_le
  intro x _
  rw [size_prod, size_tally, tally_length, Dusk.volume]
  omega

theorem prefixWords_size {w : ℕ} (s : List (Dusk.Grain w)) :
    size (prefixWords s) ≤ s.length * (12*(w+1))+1 := by
  apply map_size_le
  intro x _
  rw [Dusk.volume]
  omega

private theorem pass_cost {a b sa sb w c : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : w+1 ≤ c) (hsa : sa ≤ a*(12*(w+1))+1) (hsb : sb ≤ b*(12*(w+1))+1) :
    sb + sa + (sa*b+sb*a) + a*b*c + 1 ≤ 54*(a*b*c + 1) := by
  have bound (u s : ℕ) (hu : 0 < u) (hs : s ≤ u * (12*(w+1))+1) : s ≤ 13 * (u*c) := by
    have h₁ : u*(12*(w+1)) ≤ u*(12*c) := by gcongr
    have h₂ : 0 < u*c := Nat.mul_pos hu (by omega)
    nlinarith
  have h₁ : sa*b ≤ 13*(a*b*c) :=
    (Nat.mul_le_mul_right b (bound a sa ha hsa)).trans_eq (by ring)
  have h₂ : sb*a ≤ 13*(a*b*c) :=
    (Nat.mul_le_mul_right a (bound b sb hb hsb)).trans_eq (by ring)
  have h₃ := Nat.le_mul_of_pos_right sa hb
  have h₄ := Nat.le_mul_of_pos_right sb ha
  omega

/-- For every nonempty pair of a prefix stream and a local table, a single
fixed program builds their Cartesian product and applies the signed
fixed-point multiplier. The time includes exchanging the two source streams
and copying the table for every prefix. -/
theorem extendTable_bounded {I : Type} (w f : I → ℕ) (s t : (i : I) → List (Dusk.Grain (w i)))
    (hf : ∀ i, f i ≤ w i + 1) (hs : ∀ i, (s i) ≠ []) (ht : ∀ i, (t i) ≠ []) :
    Space.BoundedTask (fun i => (s i).length * (t i).length * GridTask.recordCost (w i))
      (fun i => (s i).length * (t i).length * (w i+1) + GridTask.recordCost (w i))
      (fun i => .fork (send (tableWords (f i) (t i))) (send (prefixWords (s i))))
      (fun i => send (prefixWords (extendTable (f i) (s i) (t i)))) := by
  let l i := prefixWords (s i)
  let r i := tableWords (f i) (t i)
  let xy i := (l i).flatMap fun x => (r i).map fun y => (x,y)
  have A := Task.exchange (fun i => send (r i)) (fun i => send (l i))
  have B := Cartesian.cartesian l r (fun i => by simpa [l, prefixWords] using hs i)
    (fun i => by simpa [r, tableWords] using ht i)
  have hlen : ∀ i, (xy i).length = (s i).length * (t i).length := by
    intro i
    simp [xy, List.length_flatMap, List.map_map, Function.comp_def, l, r, prefixWords, tableWords]
  have widths (i : I) (z) (hz : z ∈ xy i) : size z ≤ 20*(w i+1) := by
      rcases List.mem_flatMap.mp hz with ⟨x,hx,hrow⟩
      obtain ⟨y,hyi,rfl⟩ := List.mem_map.mp hrow
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨v,_,hv⟩ := List.mem_map.mp hyi
      subst y
      change size (Dusk.mark u) + (size (tally (f i)) + size (Dusk.mark v) + 1) + 1 ≤ _
      rw [Dusk.volume, Dusk.volume, size_tally, tally_length]
      have h := hf i
      omega
  have out (i : I) : (xy i).map Grid.adjust = prefixWords (extendTable (f i) (s i) (t i)) := by
    simp [xy,l,r,prefixWords,tableWords,extendTable,PhaseStream.extend,List.map_flatMap,
      List.flatMap_map, List.map_map,Function.comp_def,Grid.inject]
  let N i := (s i).length * (t i).length
  let volume i := N i * (w i+1)
  let c i := GridTask.recordCost (w i)
  have prep := Space.BoundedTask.of_time (A.compose B)
  have pcost (i : I) :
      size (r i) + size (l i) + (size (l i)*(r i).length + size (r i)*(l i).length) +
        1 ≤ 54 * (volume i + 1) := by
    have h := pass_cost (List.length_pos_iff.mpr (hs i)) (List.length_pos_iff.mpr (ht i))
      (le_rfl (a := w i+1)) (prefixWords_size _) (tableWords_size _ (hf i))
    simp only [r,l,prefixWords,tableWords,List.length_map]
    exact (by dsimp only [volume,N]; dsimp only [prefixWords,tableWords] at h; omega)
  have P := prep.bound (time' := volume) (space' := volume) 54 108
    pcost (fun i => by
      have h := pcost i
      change (size (r i) + size (l i) + 1) +
        (size (r i) + size (l i) + (size (l i) * (r i).length + size (r i) * (l i).length)) + 1 ≤ _
      omega)
  let V i : ℕ := N i * (21 * (w i+1)) + 1
  have wc (i : I) : w i+1 ≤ c i := GridTask.width_le_recordCost _
  have leR (i : I) (z) (hz : z ∈ xy i) : size z ≤ 20*c i :=
    (widths i z hz).trans (Nat.mul_le_mul_left 20 (wc i))
  obtain ⟨D,hD⟩ := GridTask.recordCost_scale 20
  have call : Task (fun v : (i : I) × Fin (xy i).length => 20*c v.1)
      (fun v => send ((xy v.1)[v.2.val])) (fun v => send (Grid.adjust ((xy v.1)[v.2.val]))) := by
    apply (GridTask.adjustTask.on (fun v : (i : I) × Fin (xy i).length => (xy v.1)[v.2.val])).bound (D+1)
    intro v
    have h := hD (w v.1) _ (widths v.1 _ (List.getElem_mem v.2.isLt))
    change GridTask.recordCost _ ≤ D * c v.1 at h
    change GridTask.recordCost _ + 1 ≤ (D+1) * (20*c v.1 + 1)
    nlinarith only [h, Nat.zero_le (D*c v.1), Nat.zero_le (c v.1), Nat.zero_le D]
  have batch := Space.BoundedTask.mapping xy Grid.adjust V (fun i => 20*c i) call
    (fun i => by
      have h := map_size_le id (xy i) (21*(w i+1)) (fun z hz => by have := widths i z hz; change size z + 1 ≤ 21 * (w i + 1); omega)
      simpa [V,N,hlen] using h)
    (fun i => by
      rw [out]
      have h := prefixWords_size (extendTable (f i) (s i) (t i))
      rw [extendTable_length] at h
      exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) 1))
    leR
  have run := (P.compose batch).conform (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun i => congrArg send (out i))
  apply run.bound 46 24
  · intro i
    change volume i + (V i + (xy i).length * (20*c i+1)) + 1 ≤ 46*(N i*c i+1)
    have h₁ : volume i ≤ N i*c i := Nat.mul_le_mul_left _ (wc i)
    have h₂ : N i ≤ N i*c i := Nat.le_mul_of_pos_right _ (by have := wc i; omega)
    have h₃ : (xy i).length = N i := hlen i
    rw [h₃]
    dsimp only [V,volume] at *
    nlinarith only [h₁,h₂,Nat.zero_le (N i*c i)]
  · intro i
    change max (volume i) (V i + 20*c i) + 1 ≤ 24*(volume i + c i + 1)
    have hv : V i = 21*volume i+1 := by dsimp only [V,volume]; ring
    rw [hv]
    omega

/-- Per-pass time as an ordinary framed P192 task. -/
theorem extendTable_task {I : Type} (w f : I → ℕ) (s t : (i : I) → List (Dusk.Grain (w i)))
    (hf : ∀ i, f i ≤ w i + 1) (hs : ∀ i, (s i) ≠ []) (ht : ∀ i, (t i) ≠ []) :
    Task (fun i => (s i).length * (t i).length * GridTask.recordCost (w i))
      (fun i => .fork (send (tableWords (f i) (t i))) (send (prefixWords (s i))))
      (fun i => send (prefixWords (extendTable (f i) (s i) (t i)))) :=
  (extendTable_bounded w f s t hf hs ht).forget

end FixedPoint

end NearSquareRoot
end Computability
end OAI
