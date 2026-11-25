import OAI.Computability.BorderVNP.PackedHistoryCircuit

/-! # Every accepted circuit transcript is one and only one adaptive tensor history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open Shortening.Adaptive VPVNP.VerifierNetwork

variable {k b : ℕ} {A : ℕ → Type*} {W G : ℕ → Type}
variable [∀ j, Fintype (W j)] [∀ j, Fintype (G j)] {S : System k b A}

/-- Physical state representation at a given round. A relation permits irrelevant padding
registers, whereas profile guess pins themselves have a unique canonical encoding. -/
abbrev Represents (A : ℕ → Type*) (W : ℕ → Type) := ∀ n, (W n → Bool) → A n → Prop

/-- The local per-round compiler checks exactly the actual term words and writes the successor
layout represented by that term. Both fields are stated on all valid child representations. -/
structure LocalCorrect (C : Codec S G) (rep : Represents A W) (step : Steps k b W G) : Prop where
  /-- The local guard accepts precisely the images of the profile indices. -/
  valid : ∀ n (hn : n<b) (c : Fin k → A n) (y : Fin k → W n → Bool) (g : G n → Bool),
    (∀ i, rep n (y i) (c i)) →
    ((step n hn).eval (Sum.elim (fun p => y p.1 p.2) g) (.inr ()) = true ↔
      ∃ q, g = C.word n hn c q)
  /-- The implemented state on every accepted local term is the successor specified by the system. -/
  next : ∀ n (hn : n<b) (c : Fin k → A n) (y : Fin k → W n → Bool) (g : G n → Bool)
    (q : (S.choose n hn c).Index), (∀ i, rep n (y i) (c i)) → g = C.word n hn c q →
    rep (n+1) (fun j => (step n hn).eval (Sum.elim (fun p => y p.1 p.2) g) (.inl j)) ((S.choose n hn c).term q)

variable {σ : Type*} [Fintype σ] (C : Codec S G) (rep : Represents A W) (step : Steps k b W G)

/-- The actual circuits preparing the bottom bundles compute their respective leaf states. -/
def LeafState (x : σ → Bool) : (n : ℕ) → Leaves k (A 0) n → Leaves k (Frame σ (W 0)) n → Prop
  | 0, a, f => rep 0 (f.eval x) a
  | n+1, a, fs => ∀ i, LeafState x n (a i) (fs i)

/-- Soundness and completeness together with the state at every node. In particular an invalid
ancestor cannot certify a transcript containing a malformed profile further down the tree. -/
theorem semantics (correct : LocalCorrect C rep step) (n : ℕ) (hn : n ≤ b)
    (a : Leaves k (A 0) n) (fs : Leaves k (Frame σ (W 0)) n) (x : σ → Bool)
    (hl : LeafState rep x n a fs) (g : Slot k G n → Bool) :
    (flag step n hn fs x g = true ↔ ∃ q, g = encode C n hn a q) ∧
      ∀ q, g = encode C n hn a q → rep n (output step n hn fs x g) (state n hn a q) := by
  induction n with
  | zero =>
    constructor
    · exact ⟨fun _ => ⟨PUnit.unit, funext fun z => z.elim⟩, fun _ => flag_zero step fs x g⟩
    · intro q _
      rw [show output step 0 hn fs x g = fs.eval x from output_zero step fs x g]
      exact hl
  | succ n ih =>
    have hs (i : Fin k) := ih (by omega) (a i) (fs i) (hl i) (childGuess g i)
    let H (i : Fin k) := S.histories n (by omega) (a i)
    let y (i : Fin k) := output step n (by omega) (fs i) x (childGuess g i)
    let vals (c : ∀ i, (H i).Index) (i : Fin k) := state n (by omega) (a i) (c i)
    have splitC (q : (S.histories (n+1) hn a).Index) (he : g = encode C (n+1) hn a q) (i : Fin k) :
        childGuess g i = encode C n (by omega) (a i) (q.1 i) := funext (fun j => congrFun he (.inl (i,j)))
    have splitG (q : (S.histories (n+1) hn a).Index) (he : g = encode C (n+1) hn a q) :
        nodeGuess g = C.word n hn (vals q.1) q.2 := funext (fun j => congrFun he (.inr j))
    constructor
    · rw [flag_succ]
      constructor
      · rintro ⟨children,root⟩
        choose c hc using fun i => (hs i).1.mp (children i)
        have reps (i) : rep n (y i) (vals c i) := (hs i).2 (c i) (hc i)
        obtain ⟨q,hq⟩ := (correct.valid n hn (vals c) y (nodeGuess g) reps).mp root
        refine ⟨⟨c,q⟩,?_⟩
        funext j
        rcases j with ⟨i,l⟩ | l
        · exact congrFun (hc i) l
        · exact congrFun hq l
      · rintro ⟨q,he⟩
        have hchild (i) := splitC q he i
        have reps (i) : rep n (y i) (vals q.1 i) := (hs i).2 (q.1 i) (hchild i)
        exact ⟨fun i => (hs i).1.mpr ⟨q.1 i, hchild i⟩,
          (correct.valid n hn (vals q.1) y (nodeGuess g) reps).mpr ⟨q.2,splitG q he⟩⟩
    · intro q he
      have reps (i) : rep n (y i) (vals q.1 i) := (hs i).2 (q.1 i) (splitC q he i)
      have hout : output step (n+1) hn fs x g = fun j =>
          (step n hn).eval (Sum.elim (fun p => y p.1 p.2) (nodeGuess g)) (.inl j) := funext (output_succ step n hn fs x g)
      rw [hout]
      exact correct.next n hn (vals q.1) y (nodeGuess g) q.2 reps (splitG q he)

/-- Bijection from the genuine dependent histories to exactly the accepted static guesses. -/
noncomputable def acceptedEquiv (correct : LocalCorrect C rep step) (n : ℕ) (hn : n ≤ b)
    (a : Leaves k (A 0) n) (fs : Leaves k (Frame σ (W 0)) n) (x : σ → Bool)
    (hl : LeafState rep x n a fs) :
    (S.histories n hn a).Index ≃ {g : Slot k G n → Bool // flag step n hn fs x g = true} :=
  let f := fun q : (S.histories n hn a).Index => (⟨encode C n hn a q,
    (semantics C rep step correct n hn a fs x hl _).1.mpr ⟨q,rfl⟩⟩ :
      {g : Slot k G n → Bool // flag step n hn fs x g = true})
  Equiv.ofBijective f ⟨fun _ _ he => encode_injective C n hn a (congrArg Subtype.val he),
    fun g => by
      obtain ⟨q,hq⟩ := (semantics C rep step correct n hn a fs x hl g.val).1.mp g.property
      exact ⟨q,Subtype.ext hq.symm⟩⟩

/-- The public assignment attached to a history is its recursively encoded word. -/
theorem acceptedEquiv_word (correct : LocalCorrect C rep step) (n : ℕ) (hn : n ≤ b)
    (a : Leaves k (A 0) n) (fs : Leaves k (Frame σ (W 0)) n) (x : σ → Bool)
    (hl : LeafState rep x n a fs) (q : (S.histories n hn a).Index) :
    ((acceptedEquiv C rep step correct n hn a fs x hl) q).val = encode C n hn a q := rfl

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
