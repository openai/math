import OAI.Computability.NearSquareRoot.FixedLayerEffectiveDispatch

/-! # Truthful width-only physical budgets for the same file on all candidate tuples -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveBoundedTask
open IntegerMultiplication Code Space CommonRegisters GeneratorSyntax

private def smallTrees : ℕ → Finset Tree
  | 0 => ∅
  | n+1 => {.atom false,.atom true} ∪
      ((smallTrees n).product (smallTrees n)).image (fun p => .fork p.1 p.2)

private theorem in_smallTrees (n : ℕ) (t : Tree) (small : t.count ≤ n) : t ∈ smallTrees n := by
  induction n generalizing t with
  | zero => have := t.count_pos; omega
  | succ n ih =>
    cases t with
    | atom b => cases b <;> simp [smallTrees]
    | fork a b =>
      change a.count+b.count+1 ≤ n+1 at small
      have ha := a.count_pos
      have hb := b.count_pos
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(a,b),Finset.mem_product.mpr ⟨ih a (by omega),ih b (by omega)⟩,rfl⟩)

/-- Finite encoded inputs and outputs suffice even when the index carries
unbounded data invisible to the command. Its correctness already applies to every
environment and every register suffix. -/
private theorem width_time {I : Type} (cmd : Cmd) (width : I → ℕ) (u v : I → Tree)
    (inCap outCap : ℕ → ℕ) (hin : ∀ j, (u j).count ≤ inCap (width j))
    (hout : ∀ j, (v j).count ≤ outCap (width j))
    (raw : ∀ i, ∃ t, ∀ env r, Fits env cmd (pile 0 (u i) r) (pile 0 (v i) r) t) :
    ∃ T : ℕ → ℕ, ∀ i env r, Fits env cmd (pile 0 (u i) r) (pile 0 (v i) r) (T (width i)) := by
  classical
  let present (n : ℕ) (a : Tree × Tree) := ∃ i, width i = n ∧ u i = a.1 ∧ v i = a.2
  let price (n : ℕ) (a : Tree × Tree) :=
    if h : present n a then (raw h.choose).choose else 0
  let pairs n := (smallTrees (inCap n)).product (smallTrees (outCap n))
  refine ⟨fun n => (pairs n).sup (price n),fun i env r => ?_⟩
  let a := (u i,v i)
  have presentHere : present (width i) a := ⟨i,rfl,rfl,rfl⟩
  have hit : a ∈ pairs (width i) := Finset.mem_product.mpr
    ⟨in_smallTrees _ _ (hin i),in_smallTrees _ _ (hout i)⟩
  have one := (raw presentHere.choose).choose_spec env r
  have upper := Finset.le_sup (f := price (width i)) hit
  have bound := one.mono (show _ ≤ (pairs (width i)).sup (price (width i)) by
    simpa only [price,dite_eq_left presentHere] using upper)
  exact (congrArg₂ (fun x y => Fits env cmd (pile 0 x r) (pile 0 y r)
    ((pairs (width i)).sup (price (width i)))) presentHere.choose_spec.2.1 presentHere.choose_spec.2.2).mp bound

/-- The generated file runs for every tuple. Above the good tuple's cutoff it
receives its separately proved fast bounds. Elsewhere an upper bound on the
literal running time and stack growth exists at every width. This case split
is used only to measure the already specified command. -/
theorem total_width_budgets {P : Type} [Primcodable P] {I : P → Type} (good : P → Prop)
    (cut : P → ℕ) (n : ∀ p, I p → ℕ) (u v : ∀ p, I p → Tree)
    (inCap outCap target : P → ℕ → ℕ)
    (hin : ∀ p i, (u p i).count ≤ inCap p (n p i)) (hout : ∀ p i, (v p i).count ≤ outCap p (n p i))
    (cmd : P → Cmd) (R : ℕ) (gen : Effective ltr cmd) (hR : 0 < R) (within : ∀ p, Within R (cmd p))
    (raw : ∀ p i, ∃ t, ∀ env r, Fits env (cmd p) (pile 0 (u p i) r) (pile 0 (v p i) r) t)
    (fast : ∀ p, good p → Runs (cmd p)
      (fun i : {i : I p // cut p ≤ n p i} => target p (n p i.val)) (fun i => n p i.val)
      (fun i => u p i.val) (fun i => v p i.val)) :
    ∃ arena clock : P → ℕ → ℕ,
      Family (fun p i => clock p (n p i)) (fun p i => arena p (n p i)) u v ∧
      (∀ p w, w ≤ arena p w ∧ arena p w ≤ clock p w) ∧
      ∀ p, good p → ∀ w ≥ cut p, arena p w = w ∧ clock p w = max w (target p w) := by
  classical
  choose T hr using fun p => width_time (cmd p) (n p) (u p) (v p) (inCap p) (outCap p)
    (hin p) (hout p) (raw p)
  let wide p w := w+inCap p w+T p w
  let arena p w := if good p ∧ cut p ≤ w then w else wide p w
  let clock p w := if good p ∧ cut p ≤ w then max w (target p w) else wide p w
  have slow (p : P) (i : I p) (env : Env) (r : Deck) (base : ℕ)
      (bound : ∀ a, (letters r a).length ≤ base) :
      BoundedFits env (cmd p) (pile 0 (u p i) r) (pile 0 (v p i) r) (wide p (n p i))
        (base+wide p (n p i)) (wide p (n p i)) := by
    apply BoundedFits.of_fits (hr p i env r) (cap := base+wide p (n p i)) (depth := wide p (n p i)) _ _ |>.mono
    · dsimp [wide]; omega
    · exact le_rfl
    · exact le_rfl
    · intro a
      by_cases eq : a=0
      · subst a; rw [letters_here,List.length_append,Tree.spell_length]
        have := hin p i
        have := bound 0
        dsimp [wide]; omega
      · rw [pile_far _ _ (Ne.symm eq)]
        have := bound a
        dsimp [wide]; omega
    · dsimp [wide]; omega
  refine ⟨arena,clock,⟨cmd,R,gen,hR,fun p => ⟨within p,?_⟩⟩,fun p w => ?_,fun p hg w hw => ?_⟩
  · by_cases hg : good p
    · obtain ⟨C,run⟩ := fast p hg
      refine ⟨C+1,fun i env r base bound => ?_⟩
      by_cases hw : cut p ≤ n p i
      · simp only [clock,arena,ite_eq_left (And.intro hg hw)]
        apply (run ⟨i,hw⟩ env r base bound).mono
        · exact Nat.mul_le_mul (Nat.le_succ C) (Nat.succ_le_succ (le_max_right ..))
        · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ C)) _
        · exact Nat.mul_le_mul_right _ (Nat.le_succ C)
      · simp only [clock,arena,hw,and_false,ite_false]
        apply (slow p i env r base bound).mono <;> simp [Nat.succ_mul] <;> omega
    · refine ⟨1,fun i env r base bound => ?_⟩
      simp only [clock,arena,hg,false_and,ite_false,one_mul]
      apply (slow p i env r base bound).mono <;> omega
  · dsimp [arena,clock,wide]
    split_ifs <;> exact ⟨by omega,by omega⟩
  · simp only [arena,clock,ite_eq_left (And.intro hg hw),and_self]

end EffectiveBoundedTask

namespace FixedLayer
open IntegerMultiplication Code FixedCandidate FixedPoint SynchronizedLayers CommonRegisters GeneratorSyntax EffectiveBoundedTask
open private inputSize from OAI.Computability.NearSquareRoot.FixedLayerDispatch

/-- Literal row-command linkage, applicable to any of the three row types.
The ordinary correctness proof supplies arbitrary-width execution on every tuple;
the fast-run proof applies to the very same command. -/
theorem effectiveKindAt_of_total {P : Type} [Primcodable P] {I : P → Type}
    (n : ∀ p, I p → ℕ) (hv : ∀ p i, Directory (n p i)) (dir : ∀ p, I p → Bool)
    (hd : ∀ p i, 4 ≤ (box (n p i)).length) (hn : ∀ p i, 2 ≤ n p i)
    (kind : Kind) (good : P → Prop) (cut : P → ℕ) (target : P → ℕ → ℕ)
    (cmd : P → Cmd) (R : ℕ) (gen : Effective ltr cmd) (hR : 0 < R) (within : ∀ p, Within R (cmd p))
    (y : ∀ p (e : {e : RowInput (n p) (hv p) (dir p) // HasKind (n p) (hv p) (dir p) kind e}),
      Array (n p e.val.instanceIndex))
    (correct : ∀ p e, rowError (n p) (hv p) (dir p) (hd p) e.val (y p e))
    (raw : ∀ p e, ∃ t, ∀ env r, Fits env (cmd p)
      (pile 0 (send (encodedInput (n p) (hv p) (dir p) e.val)) r) (pile 0 (framed (y p e)) r) t)
    (fast : ∀ p, good p → Runs (cmd p)
      (fun e : {e : {e : RowInput (n p) (hv p) (dir p) // HasKind (n p) (hv p) (dir p) kind e} //
        cut p ≤ n p e.val.instanceIndex} => target p (n p e.val.val.instanceIndex))
      (fun e => n p e.val.val.instanceIndex)
      (fun e => send (encodedInput (n p) (hv p) (dir p) e.val.val)) (fun e => framed (y p e.val))) :
    ∃ arena clock : P → ℕ → ℕ,
      EffectiveImplementsAt n hv dir hd arena clock kind ∧
      (∀ p w, w ≤ arena p w ∧ arena p w ≤ clock p w) ∧
      ∀ p, good p → ∀ w ≥ cut p, arena p w = w ∧ clock p w = max w (target p w) := by
  let E p := {e : RowInput (n p) (hv p) (dir p) // HasKind (n p) (hv p) (dir p) kind e}
  obtain ⟨arena,clock,run,bounds,sharp⟩ := total_width_budgets good cut
    (fun p (e : E p) => n p e.val.instanceIndex)
    (fun p e => send (encodedInput (n p) (hv p) (dir p) e.val)) (fun p e => framed (y p e))
    (fun _ w => 1920000100000*(w+1)) (fun _ w => 75000*(w+1)) target
    (fun p e => inputSize (n p) (hv p) (dir p) (hn p) e.val)
    (fun p e => framed_size (hn p _) (y p e)) cmd R gen hR within raw fast
  exact ⟨arena,clock,⟨y,run,correct⟩,bounds,sharp⟩

end FixedLayer

end NearSquareRoot
end Computability
end OAI
