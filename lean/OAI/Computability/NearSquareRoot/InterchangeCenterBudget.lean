import OAI.Computability.NearSquareRoot.InterchangeOuterReserves
import OAI.Computability.NearSquareRoot.InterchangeBQuestBank

/-! # Local costs at the boundary between the two families of children -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.InterchangeBatch

/-- The headed smaller-row program passes its descriptor to the reserve
phase. Any transient duplication takes place in the local work. -/
theorem BHop.keep_header {I Y : Type} {r : Regime I} {job : Job Y}
    {n l : I → ℕ} {zone : I → Y → Prop} {limit : ℤ} {input output : I → Tree}
    (h : BHop job r n l zone limit (together r.header input) output)
    (positive : ∀ i, 1 ≤ n i) (src : Alive r n l input) (dst : Alive r n l output) :
    BHop job r n l zone limit (together r.header input) (together r.header output) := by
  have hh := Drive.started (l:=l) (r:=r) positive
  have fetch : BHop job r n l zone 0 (together r.header input) r.header :=
    .tarry (Drive.fetch positive src)
  simpa only [zero_add] using fetch.doubleg h (Rip.alivePair hh src) hh dst

/-- A bounded-size record array has a volume allowance at degree zero. -/
theorem record_capacity {I : Type} (r : Regime I) (n l : I → ℕ) (C : ℕ) (i : I) :
    n i*(C*(l i+1)+1)+1 ≤ (C+2)*(massNat r n l 0 i+1) := by
  simp only [massNat, pow_zero]
  nlinarith

private theorem length_le_count {X : Type*} (tag : X → Tree) (xs : List X) :
    xs.length ≤ (headers tag xs).count := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [headers,Task.forest_cons,List.length_cons,Tree.count] at *; omega

/-- All local terms needed by the reserve header compiler fit one parent
degree. The serialized remaining header forest still has its own allowance
when a full-volume child is live. -/
theorem center_local_cost {I X : Type} {r : Regime I} {n l : I → ℕ}
    (tag : X → Tree) (uses : I → List X) (source : I → Tree) (V : I → ℕ)
    (positive : ∀ i, 1 ≤ n i) (small : r.Small (fun i => headers tag (uses i)))
    (Vpos : ∀ i, (source i).count ≤ V i) (A : ℕ)
    (volume : ∀ i, V i ≤ A*(massNat r n l 0 i + 1)) (u : I → ℕ) (hu : Dom r.scale u) :
    ∃ k C : ℕ, ∀ i, (r.header i).count + (source i).count + V i + u i +
      (headers tag (uses i)).count + (uses i).length + 1 ≤ C*(massNat r n l k i+1) := by
  let H i := (headers tag (uses i)).count
  have size : Dom r.scale H := small.extent
  have count : Dom r.scale (fun i => (uses i).length) := size.mono (fun i => length_le_count tag _)
  obtain ⟨k,C,h⟩ := ((((r.gauge.add hu).add size).add count).add (Dom.const r.scale 1))
  refine ⟨k,C+2*A,fun i => ?_⟩
  have p := positive i
  have pk : (r.scale i + 1)^k ≤ massNat r n l k i := by
    unfold massNat
    exact (Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_left _ p)
  have tagBound := (h i).trans (Nat.mul_le_mul_left C (pk.trans (Nat.le_succ _)))
  change (r.header i).count + u i + H i + (uses i).length + 1 ≤ C*(massNat r n l k i + 1) at tagBound
  have vol := (volume i).trans (Nat.mul_le_mul_left A
    (Nat.add_le_add_right (massNat_mono r n l (Nat.zero_le k) i) 1))
  change (r.header i).count + (source i).count + V i + u i + H i + (uses i).length + 1 ≤ _
  rw [Nat.add_mul, Nat.mul_assoc 2]
  have := Vpos i
  omega

end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
