import OAI.Computability.BorderVNP.CellPacketReader

/-! # Reading the actual binary word framing of a sparse packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Native

open ExactQuantumFactoring.BitStackProgram
open RationalHitting.StackLanguage (codeWord)


private def view (s : Store Register) (dst : Register) (src acc token : List Bool) :=
  Function.update (Function.update (Function.update s Register.input src) dst acc) Register.control token

private theorem write_source (s : Store Register) (dst : Register) (hd : dst ≠ Register.input)
    (src acc token xs : List Bool) : Function.update (view s dst src acc token) Register.input xs = view s dst xs acc token := by
  funext k; by_cases hi : k = Register.input <;> by_cases h : k = dst <;> simp_all [view, Function.update]

private theorem write_target (s : Store Register) (dst : Register) (hd : dst ≠ Register.control)
    (src acc token xs : List Bool) : Function.update (view s dst src acc token) dst xs = view s dst src xs token := by
  funext k; by_cases h : k = dst <;> simp_all [view, Function.update]

private theorem write_token (s : Store Register) (dst : Register) (src acc token xs : List Bool) :
    Function.update (view s dst src acc token) Register.control xs = view s dst src acc xs := Function.update_idem ..

private def part (dst : Register) (emit : Emit) (b : Bool) : Program Register :=
  .seq (pushWord dst (emit b).reverse) (.push Register.control true)

private def tick (dst : Register) (emit : Emit) : Program Register :=
  .cases Register.input .skip (.cases Register.input .skip (part dst emit false) (part dst emit true)) .skip

private def wordLoop (dst : Register) (emit : Emit) : Program Register :=
  .loop Register.control (tick dst emit) (tick dst emit)

private def cost (emit : Emit) : List Bool → ℕ
  | [] => 4
  | b :: bs => cost emit bs + (emit b).length + 5

private theorem part_run (s : Store Register) (dst : Register) (hd : dst ≠ Register.control)
    (emit : Emit) (b : Bool) (src acc : List Bool) :
    Runs (part dst emit b) (view s dst src acc []) (view s dst src ((emit b).reverse ++ acc) [true])
      ((emit b).length+2) := by
  have hr := pushWord_runs dst (emit b).reverse (view s dst src acc [])
  simp only [view, Function.update_of_ne hd, Function.update_self, List.length_reverse] at hr
  change Runs _ _ (Function.update (view s dst src acc []) dst _) _ at hr
  rw [write_target s dst hd] at hr
  have ht := Runs.push (view s dst src ((emit b).reverse ++ acc) []) Register.control true
  rw [write_token] at ht
  change Runs _ _ (view s dst src ((emit b).reverse ++ acc) [true]) _ at ht
  have h := Runs.seq hr ht
  rw [show 1 + ((emit b).length+1) = (emit b).length+2 by omega] at h
  exact h

private theorem loop_run (s : Store Register) (dst : Register) (hi : dst ≠ Register.input) (hc : dst ≠ Register.control)
    (emit : Emit) (bs rest acc : List Bool) :
    Runs (wordLoop dst emit) (view s dst (codeWord bs ++ rest) acc [true])
      (view s dst rest ((bs.flatMap emit).reverse ++ acc) []) (cost emit bs) := by
  induction bs generalizing acc with
  | nil =>
    let u := view s dst (true :: rest) acc []
    have hr : Runs (tick dst emit) u (view s dst rest acc []) 2 := by
      apply Runs.cases_true (xs := rest)
      · simp [u,view,hi.symm]
      · simpa only [u,write_source s dst hi] using Runs.skip (view s dst rest acc [])
    apply Runs.loop_true (xs := []) (a := 2) (b := 1)
    · rfl
    · simpa only [u, codeWord, List.singleton_append, write_token] using hr
    · exact Runs.loop_nil rfl
  | cons b bs ih =>
    let src := codeWord bs ++ rest
    have hr : Runs (tick dst emit) (view s dst (false::b::src) acc [])
        (view s dst src ((emit b).reverse ++ acc) [true]) ((emit b).length+4) := by
      apply Runs.cases_false (xs := b::src)
      · simp [view,hi.symm]
      · rw [write_source s dst hi]
        cases b with
        | false => apply Runs.cases_false (xs := src) (by simp [view,hi.symm]); rw [write_source s dst hi]; exact part_run s dst hc emit false src acc
        | true => apply Runs.cases_true (xs := src) (by simp [view,hi.symm]); rw [write_source s dst hi]; exact part_run s dst hc emit true src acc
    have ht := ih ((emit b).reverse ++ acc)
    have hh := Runs.loop_true (p := tick dst emit) (xs := []) (s := view s dst (false::b::src) acc [true])
      (by rfl : view s dst (false::b::src) acc [true] Register.control = true :: []) (by simpa only [write_token] using hr) ht
    simpa only [src, cost, wordLoop, codeWord, List.cons_append, List.flatMap_cons,
      List.reverse_append, List.append_assoc, Nat.add_assoc] using hh

private theorem cost_bound (emit : Emit) (w : List Bool) :
    cost emit w+2 ≤ (max (emit false).length (emit true).length+6)*(w.length+1) := by
  induction w with
  | nil => simp [cost]
  | cons b bs ih =>
    have hb : (emit b).length ≤ max (emit false).length (emit true).length := by cases b <;> simp
    simp only [cost, List.length_cons]
    rw [Nat.mul_succ]
    omega

/-- Parse one row marker, its quoted binary payload and its terminator. The supplied static
map expands each payload bit directly to the appropriate output framing. -/
def readScalarCode (dst : Register) (emit : Emit) : Program Register :=
  .cases Register.input .skip .skip (.seq (.push Register.control true) (wordLoop dst emit))

/-- The scalar reader preserves the suffix, emits exactly the payload bits and returns its
control stack to empty. It can instead load the reversed payload onto the digit scratch stack. -/
theorem readScalarCode_runs (s : Store Register) (dst : Register) (hi : dst ≠ Register.input) (hc : dst ≠ Register.control)
    (emit : Emit) (w rest : List Bool) (hsrc : s Register.input = true :: (codeWord w ++ rest)) (hctrl : s Register.control = []) :
    ∃ c ≤ (max (emit false).length (emit true).length + 6)*(w.length+1),
    Runs (readScalarCode dst emit) s
      (Function.update (Function.update s Register.input rest) dst ((w.flatMap emit).reverse ++ s dst)) c := by
  have hv (src out : List Bool) : view s dst src out [] = Function.update (Function.update s Register.input src) dst out := by
    funext k; by_cases hk : k = Register.control <;> simp_all [view,Function.update, hc.symm]
  have hu : Function.update s Register.input (codeWord w ++ rest) = view s dst (codeWord w ++ rest) (s dst) [] := by
    rw [hv]
    have he : Function.update s Register.input (codeWord w ++ rest) dst = s dst := Function.update_of_ne hi ..
    rw [← he, Function.update_eq_self]
  have hr := loop_run s dst hi hc emit w rest (s dst)
  rw [hv] at hr
  have ht := Runs.push (view s dst (codeWord w ++ rest) (s dst) []) Register.control true
  rw [write_token] at ht
  change Runs _ _ (view s dst (codeWord w ++ rest) (s dst) [true]) _ at ht
  refine ⟨cost emit w+2,?_,?_⟩
  · exact cost_bound emit w
  · apply Runs.cases_true hsrc
    rw [hu]
    exact Runs.seq ht hr

/-- Uniform streaming reader for a scalar in the outer packet. -/
def scalarReader (emit : Emit) :
    Reader (fun n : ℕ => wire [n]) (fun n => n.bits.flatMap emit) ∅ where
  program := readScalarCode Register.output emit
  scale := max (emit false).length (emit true).length + 6
  runs n rest out ct _ := by
    let s := bank (wire [n] ++ rest) out ct
    obtain ⟨c,hc,hr⟩ := readScalarCode_runs s Register.output (by decide) (by decide) emit n.bits rest
      (by simp [s,bank]) rfl
    refine ⟨c,hc.trans (Nat.mul_le_mul_left _ ?_),?_⟩
    · simp [wire, CellMacro.Generator.records]
      nlinarith [Nat.zero_le (n.bits.length^2)]
    · convert hr using 1
      funext k; cases k <;> rfl

end CellSparse.Packet.Native

end BorderVNP
end Computability
end OAI
