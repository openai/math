import OAI.Computability.IntegerMultiplication.Interface
import OAI.Computability.IntegerMultiplication.Code.Carry
import OAI.Computability.NearSquareRoot.InterchangeSplitVisits

/-! # Loading conventional binary operands into a bounded stack computation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace DigitPacking

open IntegerMultiplication IntegerMultiplication.Code

/-- A physical scan from the two conventional MSF operands into a serialized
tree on a distinct output tape. The resource constant is uniform over inputs. -/
def PairToTree {Y : Type*} (p : Y → Interface.Pair) (reply : Y → Tree) (n : Y → ℕ) : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (sym : Ltr → A) (blank : A) (inp out : I) (start : Q)
    (m : TM.Rule A Q I) (C : ℕ),
    Function.Injective sym ∧ (∀ a, sym a ≠ blank) ∧ inp ≠ out ∧
    ∀ y, let init := initialConfig start inp (sym ∘ Ltr.bit) (sym .sep) blank (p y).1 (p y).2
      ∃ t finish, Trace (TM.advance m) init t finish ∧ TM.advance m finish = none ∧
        TM.whole blank ((reply y).spell.map sym) (finish.tape out) ∧
        t ≤ C*(n y+1) ∧ VisitsAtMost m init t (C*(n y+1))

private def frame (s : List Ltr) : Reg Ltr := fun i => if i=0 then s else []

private theorem frame_spelling (z : Tree) :
    letters (pile 0 z (fun _ => [])) = frame z.spell := by
  funext i
  by_cases hi : i=0
  · subst i; simp [letters,frame]
  · simp [letters,frame,hi]

/-- Release a linear-time binary pair scan. The total includes the delimiter
parser, the stack computation, and the final copying of its serialized output. -/
theorem release_pair_scan {Y : Type*} (p : Y → Interface.Pair) (reply : Y → Tree) (n : Y → ℕ)
    (h₁ : ∀ y, (p y).1.length = n y) (h₂ : ∀ y, (p y).2.length = n y)
    (h : Carries (fun y => (n y : ℝ)+1) (send ∘ p) reply) : PairToTree p reply n := by
  classical
  have loader : ∃ c : Cmd, ∀ u v : List Bool,
      Prog.Run [] c (frame (u.map Ltr.bit ++ .sep :: v.map Ltr.bit))
        (17+11*(u.length+v.length)) (frame (send (u,v)).spell) :=
    ⟨_, fun u v => Interface.load u v []⟩
  obtain ⟨load,hload⟩ := loader
  obtain ⟨K,hK⟩ := h.out
  obtain ⟨_,b,⟨cmd,J,hcmd⟩,L,hL⟩ := h.runs
  obtain ⟨A,Q,I,_,_,_,sym,blank,inp,out,hne,start,m,hsym,hnonblank,release⟩ :=
    Prog.release (load.join cmd)
  let _ := Fintype.ofFinite I
  let D := 2*(40+J*L)+1+K
  refine ⟨A,Q,I,inferInstance,inferInstance,inferInstance,sym,blank,inp,out,start,m,
    (1+Fintype.card I)*(D+1),hsym,hnonblank,hne,fun y => ?_⟩
  dsimp only
  obtain ⟨u,hu,hrun⟩ := hcmd y [] (fun _ => [])
  rw [frame_spelling,frame_spelling] at hrun
  have hpair := hload (p y).1 (p y).2
  have both := hpair.join hrun
  obtain ⟨finish,initial,hin,hothers,ht,halt,word⟩ := release _ _ _ both
  simp only [frame,ite_true,Tree.spell_length] at ht word
  let init := initialConfig start inp (sym ∘ Ltr.bit) (sym .sep) blank (p y).1 (p y).2
  have heq : TM.Config.mk start initial = init := by
    congr 1
    funext i
    by_cases hi : i=inp
    · subst i
      simpa [init,initialConfig,List.map_append,List.map_map] using hin
    · simpa [init,initialConfig,hi] using hothers i hi
  rw [heq] at ht
  have hby := hL y
  have hwy := hK y
  dsimp only at hby hwy
  have hb : b y + 1 ≤ L*(n y+1) := by exact_mod_cast hby
  have hw : (reply y).count ≤ K*(n y+1) := by exact_mod_cast hwy
  have hu' := hu.trans (Nat.mul_le_mul_left J hb)
  have bound : 2*(1+(17+11*((p y).1.length+(p y).2.length))+1+u)+1+(reply y).count ≤ D*(n y+1) := by
    rw [h₁,h₂]
    unfold D
    calc
      _ ≤ 2*(19+11*(n y+n y)+J*(L*(n y+1)))+1+K*(n y+1) := by omega
      _ ≤ _ := by
        simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]
        omega
  refine ⟨_,finish,ht,halt,word,?_,?_⟩
  · exact bound.trans (Nat.mul_le_mul_right _ ((Nat.le_succ _).trans
      (Nat.le_mul_of_pos_left _ (by omega : 0 < 1+Fintype.card I))))
  · obtain ⟨v,hv,covers⟩ := visitsAtMost_of_step_count m init _
    refine ⟨v,hv.trans ?_,covers⟩
    apply Nat.le_trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ bound))
    calc
      _ ≤ Fintype.card I * ((D+1)*(n y+1)) := by apply Nat.mul_le_mul_left; rw [Nat.succ_mul D]; omega
      _ ≤ _ := by rw [← Nat.mul_assoc]; gcongr; omega

end DigitPacking

end NearSquareRoot
end Computability
end OAI
