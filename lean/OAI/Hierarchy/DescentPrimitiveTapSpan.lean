import OAI.Hierarchy.DescentMetadataInputCore
import OAI.Hierarchy.DescentBundleLanes
import OAI.Hierarchy.DescentLaneGates

namespace OAI
/-! # Recognizing a second batched tap input from its physical flattened span fields -/
namespace Hierarchy.DescentResetMetadataInputs
open DescentBundleHistory DescentKernelHistory DescentLaneGates DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {U A : Type} {p : ℕ} {w : A→ℕ} {rec : BitRecipe U A w}
variable (sh : Shape p rec) (u : rec.Node)
local notation "S" => Slice p (BlockRef p w⊕BlockRef p rec.hiddenWidth)

def another (field : ℕ→ℕ) := 0<field (field 0)

theorem first_replicated {n : ℕ} (h : 0<n) (rest : List ℕ) :
    ((List.replicate n n++rest)[0]?).getD 0=n :=by
  cases n with
  | zero=>omega
  | succ n=>simp [List.replicate_succ]

theorem one_span (a : S) (active : 0<a.count) (row : sh.rows u=[[a]]) :
    ¬another (argumentSpan sh u):=by
  have es : argumentSpans sh u=List.replicate a.count a.count:=by simp [argumentSpans,row]
  have first : argumentSpan sh u 0=a.count:=by
    simpa only [argumentSpan,es,List.append_nil] using first_replicated active []
  unfold another
  rw [first]
  simp [argumentSpan,es]

theorem two_spans (a b : S) (left : 0<a.count) (right : 0<b.count) (row : sh.rows u=[[a],[b]]) :
    another (argumentSpan sh u):=by
  have es : argumentSpans sh u=List.replicate a.count a.count++List.replicate b.count b.count:=by simp [argumentSpans,row]
  have first : argumentSpan sh u 0=a.count:=by
    simpa only [argumentSpan,es] using first_replicated left (List.replicate b.count b.count)
  have rest : ((List.replicate b.count b.count)[0]?).getD 0=b.count:=by
    simpa only [List.append_nil] using first_replicated right []
  unfold another
  rw [first,argumentSpan,es,List.getElem?_append_right (by simp)]
  simpa only [List.length_replicate,Nat.sub_self,rest] using right

theorem lane_count_positive (l : Lane p w) (units : A→ℕ) (multiple : ∀a,w a=units a*p) (hp : 0<p) :
    0<l.count units:=Nat.zero_lt_of_lt (l.index_lt units multiple hp ⟨0,hp⟩)

private theorem one_row {β : Type} {k : ℕ} (f : Fin k→β) (hk:k=1) :
    ∃i : Fin k,List.ofFn (fun j=>[f j])=[[f i]]:=by
  subst k
  exact ⟨0,by simp [List.ofFn_succ]⟩

private theorem two_rows {β : Type} {k : ℕ} (f : Fin k→β) (hk:k=2) :
    ∃i j : Fin k,List.ofFn (fun y=>[f y])=[[f i],[f j]]:=by
  subst k
  exact ⟨0,1,by simp [List.ofFn_succ]⟩

theorem ofProgram_two {Y : ℕ} (units : A→ℕ) (multiple : ∀a,w a=units a*p)
    (hp : 0<p) (q : Program Y p w) (n : q.Node)
    (arity : (q.op n).arity=1 ∨ (q.op n).arity=2) :
    another (argumentSpan (ofProgram units multiple hp q) n) ↔ (q.op n).arity=2:=by
  let form:=ofProgram units multiple hp q
  let lane:Fin (q.op n).arity→Slice p (BlockRef p w⊕BlockRef p q.recipe.hiddenWidth):=
    fun i=>laneSlice units multiple hp ((q.op n).arg i)
  have rows : form.rows n=List.ofFn (fun i=>[lane i]):=by
    change List.ofFn (fun i=>List.ofFn (fun _ : Fin 1=>lane i))=_
    simp [List.ofFn_succ]
  have pos (i) : 0<(lane i).count:=lane_count_positive _ units multiple hp
  rcases arity with h|h
  · obtain ⟨i,hi⟩:=one_row lane h
    have zero:=one_span form n (lane i) (pos i) (rows.trans hi)
    exact ⟨fun h₁=>(zero h₁).elim,fun h₂=>by omega⟩
  · obtain ⟨i,j,hij⟩:=two_rows lane h
    exact ⟨fun _=>h,fun _=>two_spans form n (lane i) (lane j) (pos i) (pos j) (rows.trans hij)⟩

/-- Read the same two physical digits through a finite padded aperture. -/
def measured {a K : ℕ} (xs : Fin K→Cell a) (i : ℕ) := if h:i<K then (xs ⟨i,h⟩).val else 0
theorem captured {a K : ℕ} (xs : Fin K→Cell a) (hp : 0<p) (fits : (sh.recipe hp).arity u≤K)
    (read : ∀j,(xs j).val=argumentSpan sh u j.val) : measured xs=argumentSpan sh u :=by
  funext i
  by_cases h:i<K
  · simpa [measured,h] using read ⟨i,h⟩
  · have absent : ¬0<argumentSpan sh u i:=fun pos=>h ((span_occupied hp sh u i).mp pos|>.trans_le fits)
    simp [measured,h,Nat.eq_zero_of_not_pos absent]

end
end Hierarchy.DescentResetMetadataInputs

end OAI
