import OAI.Computability.NearSquareRoot.InterchangePivotBatch
import OAI.Computability.NearSquareRoot.InterchangeBQuestBank

/-!
# Bounded execution of an address program

A physical pivot sends the header and payload of exactly one recursive
request. The payload on return already has the required parent layout.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeBatch

variable {I J : Type} [DecidableEq J] {b n : ℕ} [NeZero b]
    {r : Regime I} {l : I → ℕ} (ord : J ≃ Fin n)
    (P G B : I → Dims.Tape) (f : I → ℕ)

private theorem empty_chain {Y : Type} {payload reply : Y → Tree} {p q : Tree}
    (step : Chain payload reply p [] q) : p = q := by cases step; rfl

private theorem singleton_chain {Y : Type} {payload reply : Y → Tree} {p q : Tree} {u : Y}
    (step : Chain payload reply p [u] q) : payload u = p ∧ reply u = q := by
  cases step with
  | cons _ done => exact ⟨rfl,empty_chain done⟩

/-- Expose a singleton schedule as a local preparation followed by a call.
This gives a space-bounded caller the exact request family and its physical
reply, independently of the chosen oracle implementation. -/
theorem prepare_single_pivot (good : I → Tree → Prop)
    (hb : 2 ≤ b) (hf : r.Has (tally ∘ f)) (hp : Told r P) (hg : Told r G) (hs : Told r B)
    (x y : J) (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree)
    (hv : Manifest _ l v) (hgood : ∀ i k, good i (v i k)) :
    let data := stackRun (layoutRows (b:=b) ord P G B f)
    let perm i := reflect ord (.pivot x y) trivial (P i) (G i) (B i) (f i)
    ∃ child : I → Request b,
      (∀ i, (allowed f (countRows (b:=b) ord P G B f) l i (child i) ∧
          ∀ k, good i ((child i).contents k)) ∧ inherited b (P i) (G i) (B i) (child i)) ∧
      Drive r (countRows (b:=b) ord P G B f) l (data v) ((Request.job b).issue ∘ child) ∧
      (Request.job b).reply ∘ child = data (fun i => v i ∘ (perm i).symm) := by
  obtain ⟨uses, hlen, valid, tags, linked⟩ :=
    pivot_schedule ord P G B f l good hb hf hp hg hs [(x,y)] v hgood
  have one i : ∃ u, uses i = [u] := List.length_eq_one_iff.mp (hlen i)
  choose child child_eq using one
  have edges i := singleton_chain (child_eq i ▸ linked i)
  have st := layoutRows_station ord P G B f hb hf hp hg hs
  have hv0 := hv.lives st
  refine ⟨child, fun i => valid i (child i) (by simp [child_eq]), ?_, ?_⟩
  · have hh : Drive r (countRows (b:=b) ord P G B f) l (stackRun (layoutRows ord P G B f) v)
        (together (Request.header ∘ child) (fun _ => Tree.atom false)) := by
      simpa only [child_eq, headers, Task.forest_cons, Task.forest_nil, Function.comp_def, together] using
        (Drive.small st.1 hv0 tags)
    have prep := (Rip.split hh).1.twice (Drive.self st.1 hv0)
    have eq : (Request.job b).issue ∘ child = together (Request.header ∘ child)
        (stackRun (layoutRows ord P G B f) v) := funext fun i => congrArg _ (edges i).1
    rwa [eq]
  · funext i
    simpa [pivotOps, recreation, stackRun] using (edges i).2

open NearSquareRoot.InterchangeSpace

/-- Typed pivot requests and a bounded relative program with their price cap. -/
abbrev BChargedTyped (good : I → Tree → Prop) (budget : ℕ) (input output : I → Tree) :=
  BHop (Request.job b) r (countRows (b:=b) ord P G B f) l
    (fun i q => (allowed f (countRows (b:=b) ord P G B f) l i q ∧ ∀ k, good i (q.contents k)) ∧
      inherited b (P i) (G i) (B i) q) budget (together r.header input) output

private theorem bounded_pivot (good : I → Tree → Prop) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (x y : J)
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v)
    (hgood : ∀ i k, good i (v i k)) :
    BChargedTyped (r:=r) (l:=l) ord P G B f (b:=b) good 1 (stackRun (layoutRows ord P G B f) v)
      (stackRun (layoutRows ord P G B f)
        (fun i => v i ∘ (reflect ord (.pivot x y) trivial (P i) (G i) (B i) (f i)).symm)) := by
  obtain ⟨child, valid, prep, post⟩ := prepare_single_pivot ord P G B f good hb hf hp hg hs x y v hv hgood
  unfold BChargedTyped
  rw [← post]
  exact (BHop.summon child (zone := fun i q => (allowed f (countRows (b:=b) ord P G B f) l i q ∧
    ∀ k, good i (q.contents k)) ∧ inherited b (P i) (G i) (B i) q) valid).preceded prep

/-- Execute every legal finite address program on the bounded oracle
command. Only pivots invoke a child. Every child preserves the encoded
payload, record count, field width and spectator-dimension constraints. -/
theorem execute_bounded_typed (good : I → Tree → Prop) (hb : 2 ≤ b) (hf : r.Has (tally ∘ f))
    (hp : Told r P) (hg : Told r G) (hs : Told r B) (ops : List (Lag J b))
    (legal : ∀ a ∈ ops, a.legal (ranking ord))
    (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (hv : Manifest _ l v)
    (hgood : ∀ i k, good i (v i k)) :
    BChargedTyped (r:=r) (l:=l) ord P G B f (b:=b) good (ops.map Lag.prices).sum
      (stackRun (layoutRows ord P G B f) v)
      (stackRun (layoutRows ord P G B f) (fun i => v i ∘
        (recreation ord (P i) (G i) (B i) (f i) ops legal).symm)) := by
  have st := layoutRows_station ord P G B f hb hf hp hg hs
  induction ops generalizing v with
  | nil => exact BHop.tarry (Fleet.keep hv st)
  | cons op ops ih =>
    let ha := legal op List.mem_cons_self
    let e i := reflect ord op ha (P i) (G i) (B i) (f i)
    let after i := v i ∘ (e i).symm
    let stream := stackRun (layoutRows (b:=b) ord P G B f)
    have hafter : Manifest _ l after := hv.shift (fun i => (e i).symm)
    have head : BChargedTyped (r:=r) (l:=l) ord P G B f (b:=b) good op.prices
        (stream v) (stream after) := by
      by_cases h : op.prices = 0
      · rw [h]
        exact BHop.tarry (instruction ord P G B f hb hf hp hg hs op ha h v hv)
      · cases op with
        | width => contradiction
        | gather => contradiction
        | pivot x y => exact bounded_pivot ord P G B f good hb hf hp hg hs x y v hv hgood
    have tail := ih (fun op h => legal op (List.mem_cons_of_mem _ h)) after hafter (fun i _ => hgood i _)
    have all := BHop.sequence st.1 (hv.lives st) (hafter.lives st) head tail
    simpa only [BChargedTyped, List.map_cons, List.sum_cons, Nat.cast_add, stream, after, e,
      recreation, Function.comp_def, Equiv.symm_trans_apply] using all

end InterchangeAddress

end NearSquareRoot
end Computability
end OAI
