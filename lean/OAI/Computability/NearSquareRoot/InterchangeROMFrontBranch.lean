import OAI.Computability.NearSquareRoot.InterchangeROMFrontCost
import OAI.Computability.NearSquareRoot.BoundedBranch

/-! # A physical Boolean branch shared by all recursive front-end instances -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFront

open IntegerMultiplication IntegerMultiplication.Code

namespace Scale
variable {I J : Type} (s : Scale I)

def on (map : J → I) : Scale J := ⟨s.endpoint ∘ map,s.header ∘ map,s.payload ∘ map⟩
def work (d : ℕ) (i : I) := (s.endpoint i+1)^d*(s.payload i+1)+(s.header i+1)^d

theorem work_cost (d : ℕ) : s.Cost (s.work d) :=
  ⟨_,_,((Dom.base _).add (Dom.const _ 1)).pow d,((Dom.base _).add (Dom.const _ 1)).pow d,fun _ => le_rfl⟩

theorem work_le {d e : ℕ} (h : d ≤ e) (i : I) : s.work d i ≤ s.work e i := by
  unfold work
  gcongr

variable {s}

theorem Run.on {p q : I → Tree} (h : s.Run p q) (map : J → I) :
    (s.on map).Run (p ∘ map) (q ∘ map) := by
  obtain ⟨t,⟨a,z,ha,hz,h⟩,task⟩ := h
  exact ⟨_,⟨_,_,ha.map map,hz.map map,fun i => h (map i)⟩,task.on map⟩

private theorem branch_task (w : I → ℕ) (p q : I → Tree) (test : I → Prop) [DecidablePred test]
    (off : Task (fun z : {i // ¬ test i} => w z.val) (fun z => p z.val) (fun z => q z.val))
    (on_ : Task (fun z : {i // test i} => w z.val) (fun z => p z.val) (fun z => q z.val)) :
    Task w (fun i => .fork (.atom (decide (test i))) (p i)) q := by
  obtain ⟨c,C,hc⟩ := off; obtain ⟨d,D,hd⟩ := on_
  refine ⟨Space.decodeBit c d,max C D+8,fun i env deck => ?_⟩
  have chosen : Fits env (bif decide (test i) then d else c) (pile 0 (p i) deck)
      (pile 0 (q i) deck) (max C D*(w i+1)) := by
    by_cases b : test i
    · simpa only [decide_eq_true b,Bool.cond_true] using
        (hd ⟨i,b⟩ env deck).mono (Nat.mul_le_mul_right _ (le_max_right C D))
    · simpa only [decide_eq_false b,Bool.cond_false] using
        (hc ⟨i,b⟩ env deck).mono (Nat.mul_le_mul_right _ (le_max_left C D))
  exact (fits_pair (c:=fun _ => .pass) (fits_bit (c:=fun b => bif b then d else c) (d:=.pass)
    (b:=decide (test i)) chosen)).mono (by simp only [Nat.add_mul,Nat.mul_add]; omega)

/-- Both programs may be established on their corresponding subtype. The
machine tests the leading Boolean exactly once and enters the chosen arm. -/
theorem Run.branch (p q : I → Tree) (test : I → Prop) [DecidablePred test]
    (off : (s.on (fun z : {i // ¬ test i} => z.val)).Run (fun z => p z.val) (fun z => q z.val))
    (on_ : (s.on (fun z : {i // test i} => z.val)).Run (fun z => p z.val) (fun z => q z.val)) :
    s.Run (fun i => .fork (.atom (decide (test i))) (p i)) q := by
  obtain ⟨c,hc⟩ := off.extract
  obtain ⟨d,hd⟩ := on_.extract
  exact ⟨_,s.work_cost (max c d),branch_task _ p q test
    (hc.mono fun z => s.work_le (le_max_left c d) z.val)
    (hd.mono fun z => s.work_le (le_max_right c d) z.val)⟩

end Scale
end InterchangeROMFront

end NearSquareRoot
end Computability
end OAI
