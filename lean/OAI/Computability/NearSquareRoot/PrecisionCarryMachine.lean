import OAI.Computability.IntegerMultiplication.Interface
import OAI.Computability.NearSquareRoot.InterchangeSplitVisits

/-! # Release an encoded arithmetic packet with plain bit output

P192's stack-program compiler supplies the physical machine. The final
recursive scan strips the list constructors and leaves only bit letters before
the output tape is written. Its continuation stack is part of the compiled run.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication IntegerMultiplication.Code

/-- The input is the serialized query tree. The separate output tape holds
exactly the reply bits. The constants cover the full machine trace and the
union of tape cells visited along it. -/
def TreeToPlainBits {Y : Type*} (query : Y → Tree) (reply : Y → List Bool)
    (budget : Y → ℕ) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (sym : Ltr → A) (blank : A) (inp out : I) (start : Q)
    (m : TM.Rule A Q I) (C S : ℕ),
    inp ≠ out ∧ Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧
    ∀ y, ∃ (initTape : I → TM.Tape A) (finish : TM.Config A Q I) (t : ℕ),
      initTape inp = TM.Tape.loaded blank ((query y).spell.map sym) ∧
      (∀ i, i ≠ inp → initTape i = TM.Tape.loaded blank []) ∧
      Trace (TM.advance m) ⟨start, initTape⟩ t finish ∧ TM.advance m finish = none ∧
      TM.whole blank ((reply y).map (sym ∘ Ltr.bit)) (finish.tape out) ∧
      t ≤ C*(budget y+1) ∧ VisitsAtMost m ⟨start, initTape⟩ t (S*(budget y+1))

private def bitPile : List Bool → Deck → Deck
  | [], r => r
  | b::bs, r => pile 0 (.atom b) (bitPile bs r)

private def stripBody : Cmd :=
  splitRoot 0 (fun _ => .pass)
    (splitRoot 0 (fun b => .join (.again 0) (give 0 b)) .pass)

private theorem strip_run (bs : List Bool) (env : Env) (r : Deck) :
    Fits (stripBody :: env) stripBody (pile 0 (send bs) r) (bitPile bs r)
      (12*bs.length+5) := by
  induction bs with
  | nil => exact fits_bit (Fits.pass _)
  | cons b bs ih =>
    change Fits _ (splitRoot 0 _ _) (pile 0 (.fork (.atom b) (send bs)) r) _ _
    apply (fits_pair (fits_bit ((Fits.again0 ih).join (fits_give b _ 0 _)))).mono
    simp only [List.length_cons]
    omega

private def raw (s : List Ltr) : Reg Ltr := fun i => if i=0 then s else []

private theorem input_frame (x : Tree) :
    letters (pile 0 x (fun _ => [])) = raw x.spell := by
  funext i
  by_cases hi : i=0
  · subst i; simp [raw, letters]
  · simp [raw, letters, hi]

private theorem plain_frame (w : List Bool) :
    letters (bitPile w (fun _ => [])) = raw (w.map Ltr.bit) := by
  induction w with
  | nil => funext i; simp [letters,bitPile,raw]
  | cons b bs ih =>
    rw [bitPile,letters_pile,ih]
    funext i
    by_cases hi : i=0
    · subst i; simp [raw, Tree.spell]
    · simp [raw,hi]

/-- Convert a compositional `Code.Task` on an encoded packet to an actual
halting deterministic tape execution. The overhead includes the conversion
and copying of the whole output. -/
theorem treeToPlainBits_of_task {Y : Type*} {b : Y → ℕ} {query : Y → Tree}
    {reply : Y → List Bool} (h : Task b query (fun y => send (reply y))) :
    TreeToPlainBits query reply (fun y => b y + (reply y).length) := by
  classical
  obtain ⟨c, C, hc⟩ := h
  obtain ⟨A,Q,I,_,_,_,sym,blank,inp,out,different,start,m,hinj,hblank,release⟩ :=
    Prog.release (c.join (.tie stripBody))
  let _ := Fintype.ofFinite I
  refine ⟨A,Q,I,inferInstance,inferInstance,inferInstance,sym,blank,inp,out,start,m,
    2*C+32, Fintype.card I * (2*C+33), different,hinj,hblank,fun y => ?_⟩
  obtain ⟨u,hu,run⟩ := hc y [] (fun _ => [])
  obtain ⟨v,hv,strip⟩ := strip_run (reply y) [] (fun _ => [])
  have wholeRun := run.join strip.tie
  rw [input_frame,plain_frame] at wholeRun
  obtain ⟨finish,initTape,loaded,spare,trace,halt,written⟩ := release _ _ _ wholeRun
  simp only [raw, ite_true, List.length_map] at trace written
  refine ⟨initTape,finish,_,loaded,spare,trace,halt,?_,?_,?_⟩
  · simpa only [List.map_map] using written
  · simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at hu ⊢
    omega
  · obtain ⟨cover, hc, hcover⟩ := visitsAtMost_of_step_count m ⟨start,initTape⟩ _
    refine ⟨cover, hc.trans ?_, hcover⟩
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc] at hu ⊢
    omega

end NearSquareRoot
end Computability
end OAI
