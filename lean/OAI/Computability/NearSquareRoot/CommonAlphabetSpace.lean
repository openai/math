import OAI.Computability.NearSquareRoot.ShortWordSpace

/-! # Visited cells of a fixed-width tape serialization

A code of width `w` represents logical address `p` at physical address
`p * w` on the same tape. The simulator may leave this block during a
microprogram. We cover every visited logical cell by one physical interval
large enough for a complete microprogram, independently of the total number
of simulated steps.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication

variable {A B Q R I : Type}
  {m : TM.Rule A Q I} {machine : TM.Rule B R I}
  {x : TM.Config A Q I} {start : TM.Config B R I} {n steps cells : ℕ}

/-- Expand the finite set of visited logical cells by a fixed physical
radius. Different logical cells' intervals may overlap. -/
theorem visitsAtMost_of_scaled_neighborhoods (width radius : ℕ)
    (space : VisitsAtMost m x n cells)
    (locality : ∀ t ≤ steps, ∀ y, Trace (TM.advance machine) start t y → ∀ i : I,
      ∃ p : ℤ, (i,p) ∈ visitedCells m x n ∧
        p * width - radius ≤ (y.tape i).pos ∧ (y.tape i).pos ≤ p * width + radius) :
    VisitsAtMost machine start steps ((2 * radius + 1) * cells) := by
  classical
  obtain ⟨cover,hcard,hcover⟩ := space
  let neighborhood (p : I × ℤ) : Finset (I × ℤ) :=
    (Finset.Icc (p.2 * width - radius) (p.2 * width + radius)).map (Function.Embedding.sectR p.1 ℤ)
  have count (p : I × ℤ) : (neighborhood p).card = 2 * radius + 1 := by
    simp only [neighborhood, Finset.card_map, Int.card_Icc]
    omega
  refine ⟨cover.biUnion neighborhood, ?_, ?_⟩
  · calc
      _ ≤ ∑ p ∈ cover, (neighborhood p).card := Finset.card_biUnion_le
      _ = (2*radius+1) * cover.card := by simp [count, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ hcard
  · intro t ht y hy i
    obtain ⟨p,hp,lo,hi⟩ := locality t ht y hy i
    obtain ⟨k,hk,z,hz,hpos⟩ := hp
    have hc := hcover k hk z hz i
    change (z.tape i).pos = p at hpos
    rw [hpos] at hc
    exact Finset.mem_biUnion.mpr ⟨(i,p), hc, Finset.mem_map.mpr
      ⟨(y.tape i).pos, Finset.mem_Icc.mpr ⟨lo,hi⟩, rfl⟩⟩

private theorem checkpoint_before (clock : ℕ → ℕ) (radius n t : ℕ)
    (hg : ∀ k < n, clock (k+1) ≤ clock k + radius)
    (h0 : clock 0 ≤ t) (hstop : t ≤ clock n) :
    ∃ k ≤ n, clock k ≤ t ∧ t - clock k ≤ radius := by
  induction n with
  | zero => exact ⟨0, le_rfl, h0, by omega⟩
  | succ n ih =>
    by_cases ht : t ≤ clock n
    · obtain ⟨k,hk,hle,hbound⟩ := ih (fun j hj => hg j (Nat.lt_succ_of_lt hj)) ht
      exact ⟨k, Nat.le_succ_of_le hk, hle, hbound⟩
    · have := hg n (Nat.lt_succ_self _)
      exact ⟨n, Nat.le_succ _, by omega, by omega⟩

/-- At each checkpoint the physical and logical head positions agree after
scaling by `width`. This includes a potentially nonempty initialization
phase preceding checkpoint zero. All of its visited cells are charged. -/
theorem visitsAtMost_of_clocked_simulation (width radius : ℕ) (clock : ℕ → ℕ)
    (space : VisitsAtMost m x n cells)
    (initial : clock 0 ≤ radius)
    (between : ∀ k < n, clock (k+1) ≤ clock k + radius)
    (aligned : ∀ k ≤ n, ∃ old current,
      Trace (TM.advance m) x k old ∧ Trace (TM.advance machine) start (clock k) current ∧
      ∀ i : I, (current.tape i).pos = (old.tape i).pos * width) :
    VisitsAtMost machine start (clock n) ((2 * radius + 1) * cells) := by
  apply visitsAtMost_of_scaled_neighborhoods width radius space
  intro t ht y hy i
  by_cases h : clock 0 ≤ t
  · obtain ⟨k,hk,hle,hnear⟩ := checkpoint_before clock radius n t between h ht
    obtain ⟨old,current,ho,hc,hs⟩ := aligned k hk
    obtain ⟨mid,hm,tail⟩ := trace_split hy hle
    have he := trace_endpoint_unique hm hc
    subst mid
    obtain ⟨lo,hi⟩ := head_excursion tail i
    rw [hs i] at lo hi
    exact ⟨(old.tape i).pos, ⟨k,hk,old,ho,rfl⟩, by omega, by omega⟩
  · obtain ⟨old,current,ho,hc,hs⟩ := aligned 0 (Nat.zero_le _)
    obtain ⟨mid,hm,tail⟩ := trace_split hc (by omega : t ≤ clock 0)
    have he := trace_endpoint_unique hm hy
    subst mid
    obtain ⟨lo,hi⟩ := head_excursion tail i
    rw [hs i] at lo hi
    exact ⟨(old.tape i).pos, ⟨0,Nat.zero_le _,old,ho,rfl⟩, by omega, by omega⟩

/-- Distinct visited cells for the block serializer whose initial scan takes
at most `2 * width` transitions and whose microprogram takes at most
`1 + 5 * width` transitions per source step. -/
theorem visitsAtMost_of_checkpoints (width : ℕ) (clock : ℕ → ℕ)
    (space : VisitsAtMost m x n cells)
    (initial : clock 0 ≤ 2 * width)
    (between : ∀ k < n, clock (k+1) ≤ clock k + (1 + 5 * width))
    (aligned : ∀ k ≤ n, ∃ old current,
      Trace (TM.advance m) x k old ∧ Trace (TM.advance machine) start (clock k) current ∧
      ∀ i : I, (current.tape i).pos = (old.tape i).pos * width) :
    VisitsAtMost machine start (clock n) ((2 * (1 + 5 * width) + 1) * cells) :=
  visitsAtMost_of_clocked_simulation width (1 + 5 * width) clock space (by omega) between aligned

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
