import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct

/-! # Compile-time folds of an effectively indexed sequence of commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveFamily

open IntegerMultiplication Code CommonRegisters GeneratorSyntax

variable {P X Y Z : Type} [Primcodable P] [Codec X] [Codec Y] [Codec Z] {R : ℕ}

/-- Emits the last selected step first, as required by a right fold. -/
def unroll (s : P × ℕ → Cmd) (p : P) : ℕ → Cmd
  | 0 => .pass
  | n+1 => (s (p,n)).join (unroll s p n)

theorem effective_unroll {s : P × ℕ → Cmd} (hs : Effective ltr s) (n : P → ℕ)
    (hn : Computable n) : Effective ltr (fun p => unroll s p (n p)) := by
  have step : Computable₂ (fun (p : P) (t : ℕ × File) => joinFile (file ltr (s (p,t.1))) t.2) :=
    (primrec_joinFile.to_comp.comp (hs.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)).to₂
  apply (Computable.nat_rec hn (Computable.const (file ltr (.pass : Cmd))) step).of_eq
  intro p
  change Nat.rec (file ltr (.pass : Cmd)) (fun k acc => joinFile (file ltr (s (p,k))) acc)
    (n p) = file ltr (unroll s p (n p))
  generalize n p = k
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (congrArg (joinFile (file ltr (s (p,k)))) ih).trans (joinFile_file ..)

theorem Family.unroll {step : P × ℕ → X → X} (hs : Family R step) (n : P → ℕ)
    (hn : Computable n) :
    Family R (fun p x => (List.range (n p)).foldr (fun k a => step (p,k) a) x) := by
  obtain ⟨s,se,sc⟩ := hs
  refine ⟨_,effective_unroll se n hn,fun p => ?_⟩
  dsimp only
  generalize n p = k
  induction k with
  | zero => exact ⟨trivial,1,fun x env r => (Fits.pass _).mono (by simp)⟩
  | succ i ih =>
    refine ⟨⟨(sc (p,i)).1,ih.1⟩,?_⟩
    rw [NearSquareRoot.KernelEffectiveFamily.unroll]
    simpa only [List.range_succ,List.foldr_append,List.foldr_cons,List.foldr_nil] using
      Runs.comp (sc (p,i)).2 ih.2

omit [Codec Z] in
private theorem range_map {n : ℕ} (g : ℕ → Z) :
    (List.range n).map g = List.ofFn (fun j : Fin n => g j.val) := by
  apply List.ext_getElem <;> simp

theorem Family.foldList (hR : 4 ≤ R) (n : P → ℕ) (hn : Computable n)
    {v : P × ℕ → X → Z} (hv : Family R v) (op : Z × Y → Y)
    (hop : RegisterWitness.Easy R op) (y : Y) :
    Family R (fun p x => (List.ofFn (fun j : Fin (n p) => v (p,j.val) x)).foldr
      (fun a b => op (a,b)) y) := by
  have fst : Family R (fun _ : P × ℕ => Prod.fst : P × ℕ → X × Y → X) :=
    Family.fixed (RegisterWitness.Easy.fst hR)
  have act := (Family.left (by omega : 1 ≤ R) hv (Z := Y)).comp (Family.fixed hop)
  have step := Family.pair (by omega : 3 ≤ R) fst act
  have all := step.unroll n hn
  have init := Family.pair (by omega : 3 ≤ R) (Family.identity (X := X) (P := P))
    (Family.const (by omega : 1 ≤ R) y)
  apply ((init.comp all).comp (Family.fixed (RegisterWitness.Easy.snd (by omega)))).congr
  intro p x
  rw [← range_map (fun j => v (p,j) x),List.foldr_map]
  let s := fun j (z : X × Y) => (z.1,op (v (p,j) z.1,z.2))
  have h (l : List ℕ) (w : Y) : l.foldr s (x,w) = (x,l.foldr (fun j a => op (v (p,j) x,a)) w) := by
    induction l with
    | nil => rfl
    | cons j l ih => simp [s,List.foldr_cons,ih]
  exact congrArg Prod.snd (h _ y)

end KernelEffectiveFamily

end NearSquareRoot
end Computability
end OAI
