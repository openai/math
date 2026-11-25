import OAI.Computability.NearSquareRoot.ScheduleInterpreterSpace

/-! # Visited space of a folded follower and a return to the origin

Mapping every address on the designated tape to its absolute value covers the
follower head. A rewind that moves the two heads toward zero remains in these
same sets of addresses. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Align
open IntegerMultiplication TM

variable {A B Q R I : Type}

/-- The lifted control can leave the other heads parked while the designated
head and its folded copy travel back toward zero. -/
structure Tracks (out : I) (v : Config A Q I) (z : Config B R (Option I)) : Prop where
  parked : ∀ i, i ≠ out → (z.tape (some i)).pos = (v.tape i).pos
  output_lo : min 0 (v.tape out).pos ≤ (z.tape (some out)).pos
  output_hi : (z.tape (some out)).pos ≤ max 0 (v.tape out).pos
  follower_lo : 0 ≤ (z.tape none).pos
  follower_hi : (z.tape none).pos ≤ ((v.tape out).pos.natAbs : ℤ)

/-- During an emulated transition all original head positions are preserved and
the follower head is exactly the distance of the designated head from zero. -/
theorem tracks_exact (out : I) (v : Config A Q I) (z : Config B R (Option I))
    (heads : ∀ i, (z.tape (some i)).pos = (v.tape i).pos)
    (follower : (z.tape none).pos = ((v.tape out).pos.natAbs : ℤ)) : Tracks out v z := by
  refine ⟨fun i _ => heads i, ?_, ?_, ?_, ?_⟩
  · rw [heads]; exact min_le_right _ _
  · rw [heads]; exact le_max_right _ _
  · rw [follower]; exact_mod_cast Nat.zero_le _
  · exact follower.le

/-- Original projected cells and absolute addresses of original cells cover
the alignment wrapper, including setup and all motion during the rewind. -/
theorem visits_of_prefixes {m : Rule A Q I} {machine : Rule B R (Option I)}
    {x : Config A Q I} {start : Config B R (Option I)} {n t cells : ℕ}
    (out : I) (origin : (x.tape out).pos = 0) (space : VisitsAtMost m x n cells)
    (prefixes : ∀ j ≤ t, ∀ z, Trace (advance machine) start j z →
      ∃ k ≤ n, ∃ v, Trace (advance m) x k v ∧ Tracks out v z) :
    VisitsAtMost machine start t (2*cells) := by
  classical
  obtain ⟨old,limit,cover⟩ := space
  let data : I × ℤ → Option I × ℤ := fun p => (some p.1,p.2)
  let folded : I × ℤ → Option I × ℤ := fun p => (none,p.2.natAbs)
  refine ⟨old.image data ∪ old.image folded, ?_, ?_⟩
  · have h₁ := Finset.card_union_le (old.image data) (old.image folded)
    have h₂ := Finset.card_image_le (s := old) (f := data)
    have h₃ := Finset.card_image_le (s := old) (f := folded)
    omega
  · intro j hj z run i
    obtain ⟨k,hk,v,sub,h⟩ := prefixes j hj z run
    have inside (p : ℤ) (h₁ : min 0 (v.tape out).pos ≤ p) (h₂ : p ≤ max 0 (v.tape out).pos) :
        (out,p) ∈ old := by
      obtain ⟨a,ha,w,run',hw⟩ := Uniform.crosses sub out p (origin ▸ h₁) (origin ▸ h₂)
      rw [← hw]
      exact cover a (ha.trans hk) w run' out
    cases i with
    | some i =>
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      by_cases hi : i = out
      · subst i
        exact ⟨_,inside _ h.output_lo h.output_hi,rfl⟩
      · exact ⟨_,cover k hk v sub i,by simp [data,h.parked i hi]⟩
    | none =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      let p := (z.tape none).pos
      have h₁ : 0 ≤ p := h.follower_lo
      have h₂ : p ≤ |(v.tape out).pos| := by simpa only [Int.natCast_natAbs] using h.follower_hi
      by_cases side : 0 ≤ (v.tape out).pos
      · rw [abs_of_nonneg side] at h₂
        exact ⟨_,inside p (by omega) (by omega),by simp [folded,abs_of_nonneg h₁,p]⟩
      · rw [abs_of_neg (by omega)] at h₂
        exact ⟨_,inside (-p) (by omega) (by omega),by simp [folded,abs_of_nonneg h₁,p]⟩

/-- To cover an exact simulation, it suffices to supply its checkpoints and
verify the rewind relative to its final running state. Time one is the first
logical checkpoint, after a stationary setup transition. -/
theorem visits_of_segments {m : Rule A Q I} {machine : Rule B R (Option I)}
    {x y : Config A Q I} {start last : Config B R (Option I)} {n back cells : ℕ}
    (out : I) (origin : (x.tape out).pos = 0) (space : VisitsAtMost m x n cells)
    (run : Trace (advance m) x n y) (setup : Tracks out x start)
    (logical : ∀ k ≤ n, ∃ v z, Trace (advance m) x k v ∧
      Trace (advance machine) start (k+1) z ∧ Tracks out v z)
    (finalCheckpoint : Trace (advance machine) start (n+1) last)
    (unwind : ∀ k ≤ back, ∀ z, Trace (advance machine) last k z → Tracks out y z) :
    VisitsAtMost machine start (n+1+back) (2*cells) := by
  apply visits_of_prefixes out origin space
  intro j hj z physical
  cases j with
  | zero =>
    have he := trace_endpoint_unique physical (.nil start)
    exact ⟨0,Nat.zero_le _,x,.nil _,he ▸ setup⟩
  | succ k =>
    by_cases h : k ≤ n
    · obtain ⟨v,expected,hr,hs,ht⟩ := logical k h
      exact ⟨k,h,v,hr,trace_endpoint_unique physical hs ▸ ht⟩
    · obtain ⟨mid,first,tail⟩ := trace_split physical (k := n+1) (by omega)
      obtain rfl := trace_endpoint_unique first finalCheckpoint
      exact ⟨n,le_rfl,y,run,unwind _ (by omega) _ tail⟩

end CommonAlphabet.Align

end NearSquareRoot
end Computability
end OAI
