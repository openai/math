import OAI.Computability.NearSquareRoot.CRTPositionProgramStream
import OAI.Computability.NearSquareRoot.CRTPositionProgramPassAction

/-! # Execution and preparation cost of the emitted position-permutation stream -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code PositionPreparation Reflections
set_option synthInstance.maxSize 5000

/-- Forward action of one serialized physical descriptor on a binary array address. -/
def act {k : ℕ} (g : ℕ) (w : Fin k → Bool) : Op → Fin k → Bool
  | .inl q => swapWord q w
  | .inr (.inr (.inr q)) => swapPair q w
  | q => passAction g w q

/-- Every emitted elementary address movement is its own inverse, including
the safe interpretation of malformed unary indices. -/
theorem act_twice {k : ℕ} (G : ℕ) (op : Op) (w : Fin k → Bool) :
    act G (act G w op) op = w := by
  rcases op with q | (⟨r,t⟩ | (⟨s,d⟩ | q))
  · exact swapWord_twice q w
  · exact gathered_twice _ w
  · exact gathered_twice _ w
  · funext x
    by_cases h : q.1.length < k ∧ q.2.length < k <;> simp [act,swapPair,h]

private theorem foldl_agree {A B : Type*} {f e : A → B → A} (l : List B) (w : A)
    (h : ∀ a ∈ l, ∀ v, f v a = e v a) : l.foldl f w = l.foldl e w := by
  induction l generalizing w with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons,h a List.mem_cons_self]
    exact ih _ (fun j hj => h j (List.mem_cons_of_mem a hj))

private theorem passes_act {k : ℕ} (g : ℕ) (hg : 0 < g) (t : ReadTable) (w : Fin k → Bool) :
    (passes (tally (k/3),tally g,normalize (tally (k/3),t))).foldl (act g) w = directed (2,1,t) w := by
  refine (foldl_agree _ _ ?_).trans (passes_action g hg t w)
  intro a ha v
  rw [passes_range] at ha
  obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp ha
  rw [pass_value] at hr
  split at hr
  · obtain rfl := List.mem_singleton.mp hr
    rfl
  · dsimp only at hr
    split at hr
    · obtain rfl := List.mem_singleton.mp hr
      rfl
    · contradiction

theorem expand_action {k : ℕ} (g : ℕ) (hg : 0 < g) (a : Gate) (h : a.1 ≠ a.2.1)
    (w : Fin k → Bool) :
    (expand ((tally (k/3),tally g),a)).foldl (act g) w = directed a w := by
  obtain ⟨s,d,t⟩ := a
  simp only [expand,List.foldl_append,List.foldl_map]
  rw [passes_act g hg]
  exact gather_correct s d h t w

theorem roundStream_action {k : ℕ} (g : ℕ) (hg : 0 < g) (c : RoundCode) (w : Fin k → Bool) :
    (roundStream ((tally (k/3),tally g),c)).foldl (act g) w = executeRound @runTables c w := by
  rw [← nativeRound_eq_executeRound]
  simp only [roundStream,List.foldl_append,List.foldl_flatten,polyPush,List.foldl_map,run]
  apply foldl_agree
  exact fun a ha v => expand_action g hg a (gates_distinct _ a ha) v

theorem assemble_action {k G : ℕ} (hG : 0 < G) (p : Equiv.Perm (Fin k)) (w : Fin k → Bool) :
    (assemble (tally G,table p)).foldl (act G) w = w ∘ p := by
  have h : ruler (table p) = tally k := by rw [← recover_tally (ruler (table p)),ruler_length,table,List.length_ofFn]
  simp only [assemble,h,third_tally,List.foldl_append,roundStream_action G hG]
  exact execute_compilePositions p w

theorem rows_forward {k : ℕ} {B : Type*} (G : ℕ) (l : List Op) (f : (Fin k → Bool) → B)
    (w : Fin k → Bool) :
    (l.foldl (fun b op => b ∘ fun v => act G v op) f) (l.foldl (act G) w) = f w := by
  induction l generalizing f w with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons,ih,Function.comp_apply,act_twice]

/-- Reindexing the payload at each address step carries a row at the old
address to the new address, giving the inverse pullback on the complete array. -/
theorem assemble_rows {k G : ℕ} {B : Type*} (hG : 0 < G) (p : Equiv.Perm (Fin k)) (f : (Fin k → Bool) → B) :
    (assemble (tally G,table p)).foldl (fun b op => b ∘ fun v => act G v op) f = fun w => f (w ∘ p.symm) := by
  funext w
  have h := rows_forward G (assemble (tally G,table p)) f (w ∘ p.symm)
  rw [assemble_action hG p] at h
  simpa [Function.comp_def] using h

private theorem input_size {X : Type*} (k G : X → ℕ) (hG : Dom k G)
    (p : (x : X) → Equiv.Perm (Fin (k x))) : Dom k (fun x => size (tally (G x),table (p x))) := by
  have b : Dom k (fun x => size (table (p x))) := ⟨2,2,fun x => table_size (p x)⟩
  simpa only [size_prod,size_tally,tally_length] using
    ((((Dom.const k 2).mul hG).add (Dom.const k 1)).add b).add (Dom.const k 1)

/-- One fixed P192 program prepares the descriptor forest from the guard and
image table, with polynomial setup time in the number of address positions. -/
theorem assemble_setup {X : Type*} (k G : X → ℕ) (hG : Dom k G)
    (p : (x : X) → Equiv.Perm (Fin (k x))) :
    Task.BT k (fun x => send (tally (G x),table (p x)))
      (fun x => Task.forest send (assemble (tally (G x),table (p x)))) := by
  simp only [Task.forest_send]
  exact assemble_poly.on (input_size k G hG p)

/-- The actual serialized header consumes polynomially many tape cells in the
address width. This includes every repeated packed read table. -/
theorem assemble_forestCap {X : Type*} (k G : X → ℕ) (hG : Dom k G)
    (p : (x : X) → Equiv.Perm (Fin (k x))) :
    Dom k (fun x => (Task.forest send (assemble (tally (G x),table (p x)))).count) := by
  simp only [Task.forest_send]
  exact (assemble_poly.length.map (fun x => (tally (G x),table (p x)))).sub (input_size k G hG p)

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
