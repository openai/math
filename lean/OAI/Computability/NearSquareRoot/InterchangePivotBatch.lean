import OAI.Computability.NearSquareRoot.InterchangeTailBatch
import OAI.Computability.NearSquareRoot.InterchangeRequestHeader

/-! # Preparing a full-volume pivot schedule

The schedule stored beside the one live stream consists only of child headers.
The same stream is the child's physical input before a pivot and is already in
the required enclosing order on return.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic
  IntegerMultiplication.Loom NearSquareRoot.InterchangeBatch

namespace Request

abbrev payload {b : ℕ} (a : Request b) := stripe a.rows a.contents

/-- Physical size of a list of header trees, including its list constructors. -/
theorem headers_count_bound {b : ℕ} (qs : List (Request b)) (N : ℕ)
    (bound : ∀ a ∈ qs, a.header.count ≤ N) :
    (headers header qs).count ≤ qs.length * (N+1) + 1 := by
  induction qs with
  | nil => simp [headers, Tree.count]
  | cons q qs ih =>
    have h := bound q List.mem_cons_self
    have ht := ih (fun a ha => bound a (List.mem_cons_of_mem _ ha))
    simp only [headers, Task.forest_cons, Tree.count, List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

theorem headers_count_log {b : ℕ} (qs : List (Request b)) (n : ℕ)
    (hb : 2 ≤ b) (valid : ∀ x ∈ qs, Admissible x ∧ x.rows.count = n) :
    (headers header qs).count ≤ qs.length * ((2*b+8)*(Nat.log 2 n + 1)+1) + 1 := by
  refine headers_count_bound qs _ fun a ha => ?_
  obtain ⟨ok,eq⟩ := valid a ha
  simpa only [eq] using a.header_count_log hb ok

end Request

abbrev pivotOps {J : Type} (b : ℕ) (pairs : List (J × J)) : List (Lag J b) :=
  pairs.map fun ⟨x,y⟩ => Lag.pivot x y

theorem pivotOps_legal {J : Type} {n : ℕ} (ord : J ≃ Fin n) (b : ℕ) (pairs : List (J × J)) :
    ∀ a ∈ pivotOps b pairs, a.legal (ranking ord) := by
  intro a ha
  obtain ⟨⟨x,y⟩,_,rfl⟩ := List.mem_map.mp ha
  trivial

variable {I J : Type} [DecidableEq J] {b n : ℕ} [NeZero b]
  {r : Regime I} (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ)

/-- For a fixed finite pivot program, the actual header generator, the exact
list of calls, and the stream equalities used by the physical batch command.
Each record in every call is one of the original records. -/
theorem pivot_schedule (good : I → Tree → Prop) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (pairs : List (J × J))
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree)
    (hgood : ∀ i k, good i (v i k)) :
    ∃ uses : I → List (Request b),
      (∀ i, (uses i).length = pairs.length) ∧
      (∀ i a, a ∈ uses i → (allowed f (countRows (b:=b) ord P G B f) l i a ∧
        ∀ k, good i (a.contents k)) ∧ inherited b (P i) (G i) (B i) a) ∧
      r.Small (fun i => headers Request.header (uses i)) ∧
      ∀ i, Chain Request.payload (Request.job b).reply (stripe (layoutRows ord P G B f i) (v i))
        (uses i) (stripe (layoutRows ord P G B f i) (v i ∘
          (recreation ord (P i) (G i) (B i) (f i) (pivotOps b pairs)
            (pivotOps_legal ord b pairs)).symm)) := by
  induction pairs generalizing v with
  | nil =>
    refine ⟨fun _ => [], fun _ => rfl, by simp, ?_, fun i => .nil _⟩
    exact Regime.fixed (r:=r) false
  | cons pair pairs ih =>
    obtain ⟨x,y⟩ := pair
    let D i := field b (f i)
    let L i := preamble ord (P i) (G i) (D i) (false,x)
    let M i := silence ord (G i) (D i) (false,x) (true,y)
    let S i := appendix ord (G i) (B i) (D i) (true,y)
    let ax (i : I) := twoStops ord (false,x) (true,y) (Or.inl ⟨rfl,rfl⟩)
      (p:=b) (j:=f i) (P:=P i) (G:=G i) (B:=B i)
    let child (i : I) : Request b := ⟨L i, M i, S i, f i, l i, v i ∘ (ax i).view.cast.symm⟩
    let after (i : I) := v i ∘ (reflect ord (.pivot x y) trivial (P i) (G i) (B i) (f i)).symm
    obtain ⟨rest,card,valid,tags,linked⟩ := ih after (fun i _ => hgood i _)
    have childTag : r.Small (fun i => (child i).header) := by
      let digit := Told.carrier hb f hf
      exact hf.pair ((digit.stair ord hp hg (false,x)).shape.pair
        ((digit.corridor ord hg (false,x) (true,y)).shape.pair
          (digit.lounge ord hg hs (true,y)).shape))
    refine ⟨fun i => child i :: rest i, fun i => congrArg Nat.succ (card i), ?_,
      childTag.pair tags, ?_⟩
    · intro i a ha
      rcases List.mem_cons.mp ha with rfl | later
      · refine ⟨⟨⟨rfl, (ax i).view.cost.symm, rfl⟩, fun k => hgood i _⟩, ?_⟩
        intro k hk
        change k ∈ (L i ++ M i) ++ S i at hk
        simp only [L,M,S,preamble_false,silence_false_true,appendix_true,List.mem_append] at hk
        simp only [List.mem_append]
        rcases hk with (((hp | h₁) | h₂ | hg | h₃) | h₄ | hs)
        · exact .inr (.inl (.inl hp))
        · exact .inl (source_radix k _ b _ h₁)
        · exact .inl (source_radix k _ b _ h₂)
        · exact .inr (.inl (.inr hg))
        · exact .inl (source_radix k _ b _ h₃)
        · exact .inl (source_radix k _ b _ h₄)
        · exact .inr (.inr hs)
      · exact valid i a later
    · intro i
      have pre : Request.payload (child i) = stripe (layoutRows ord P G B f i) (v i) := by
        unfold Request.payload
        rw [(ax i).view.packet]
        exact congrArg (stripe _) (funext fun k => congrArg (v i) ((ax i).view.cast.symm_apply_apply k))
      have post : (Request.job b).reply (child i) = stripe (layoutRows ord P G B f i) (after i) := by
        unfold Request.job
        dsimp only
        rw [(ax i).view.packet]
        rfl
      rw [← pre]
      apply Chain.cons
      rw [post]
      exact linked i

/-- The schedule is generated on the left of the original stream. The
P192 program for generating it has the same running time on this packet as
on the parent header alone. -/
theorem prepare_pivot_headers {I : Type} {r : Regime I} {H : I → Tree} (h : r.Small H)
    (payload : I → Tree) :
    ∃ u : I → ℕ, Dom r.scale u ∧ Code.Task u (together r.header payload) (together H payload) := by
  obtain ⟨u, cost,run⟩ := h
  exact ⟨u,cost,run.left payload⟩

end InterchangeAddress

end NearSquareRoot
end Computability
end OAI
