import OAI.Hierarchy.ProbeStageFallback

namespace OAI
/-! # The native fallback returns the least jointly unsaturated color -/

namespace Hierarchy.ProbeStage.Fallback
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing

/-- The timestamp and result are the only cells written in a fallback scan. -/
def Frame {w : ℕ} (s : Layout) (m m' : Memory w) : Prop :=
  ∀ x, x≠(s.remaining:Word w).val → x≠s.chosen → m' x=m x

theorem frame {w : ℕ} (s : Layout) (n : ℕ) (m : Memory w) :
    Frame s m (WordStore.down (s.remaining:Word w) (next s) n m) := by
  induction n generalizing m with
  | zero => exact fun _ _ _=>rfl
  | succ n ih =>
    intro x hx hc
    rw [WordStore.down,ih _ x hx hc]
    simp only [next,Function.update_of_ne hc,writeMemory,ite_eq_right hx]

/-- The two block pointers and the two words for this color all lie outside the two scratch
locations. This finite address condition makes the computed comparison invariant during a scan. -/
def Separate {w : ℕ} (s : Layout) (m : Memory w) (c : Word w) : Prop :=
  ∀ x∈[(s.left:Word w).val,(s.right:Word w).val,(m (s.left:Word w).val+c).val,
      (m (s.right:Word w).val+c).val], x≠(s.remaining:Word w).val ∧ x≠s.chosen

theorem possible_frame {w : ℕ} (s : Layout) (m m' : Memory w) (c : Word w)
    (fr : Frame s m m') (apart : Separate s m c) : possible s m' c ↔ possible s m c := by
  have at_ (x) (hx : x∈[(s.left:Word w).val,(s.right:Word w).val,(m (s.left:Word w).val+c).val,
      (m (s.right:Word w).val+c).val]) : m' x=m x := fr x (apart x hx).1 (apart x hx).2
  simp only [possible,at_ (s.left:Word w).val (by simp),at_ (s.right:Word w).val (by simp),
    at_ (m (s.left:Word w).val+c).val (by simp),at_ (m (s.right:Word w).val+c).val (by simp)]

theorem chosen_value {w : ℕ} (s : Layout) (m : Memory w)
    (chosenFit : s.chosen<2^w) (other : (s.remaining:Word w).val ≠ s.chosen)
    (apart : ∀ i<(m (s.remaining:Word w).val).val,Separate s m (i:Word w)) :
    image s m s.chosen = (pick (fun i => decide (possible s m (i:Word w)))
      (m (s.remaining:Word w).val).val (m s.chosen).val : ℕ) := by
  let cell := (s.remaining : Word w)
  let N := (m cell.val).val
  let good := fun i : ℕ => decide (possible s m (i:Word w))
  have aux (t : ℕ) (ht : t≤N) (mem : Memory w) (cur : mem cell.val=(t:Word w)) (fr : Frame s m mem) :
      WordStore.down cell (next s) t mem s.chosen=(pick good t (mem s.chosen).val:ℕ) := by
    induction t generalizing mem with
    | zero => simp [WordStore.down,pick]
    | succ t ih =>
      let mem' := writeMemory mem cell (mem cell.val-1)
      have pre : mem' cell.val=(t:Word w) := by simp [mem',writeMemory,cur,Nat.cast_add]
      have frem : Frame s m mem' := by
        intro x hx hc
        change x≠cell.val at hx
        change (if x=cell.val then mem cell.val-1 else mem x)=m x
        exact (ite_eq_right hx).trans (fr x hx hc)
      have frnext : Frame s m (next s mem') := fun x hx hc=>by
        simpa only [next,Function.update_of_ne hc] using frem x hx hc
      have countNext : next s mem' cell.val=(t:Word w) := by
        rw [next,Function.update_of_ne other,pre]
      have valNext : (next s mem' s.chosen).val = (if good t then t else (mem s.chosen).val) := by
        simp only [next,Function.update_self,result,Fin.val_cast_of_lt chosenFit]
        change (if possible s mem' (mem' cell.val) then mem' cell.val else mem' s.chosen).val = _
        rw [pre]
        have same := possible_frame s m mem' _ frem (apart _ (by omega : t<N))
        by_cases h : possible s m (t:Word w)
        · have tfit : t<2^w := (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ht).trans (m cell.val).isLt
          simp only [ite_eq_left (same.mpr h),good,decide_eq_true h,ite_true,Fin.val_cast_of_lt tfit]
        · have diff : s.chosen≠cell.val := other.symm
          have stable : mem' s.chosen=mem s.chosen := by
            change (if s.chosen=cell.val then mem cell.val-1 else mem s.chosen)=_
            exact ite_eq_right diff
          simp only [ite_eq_right (h ∘ same.mp),good,decide_eq_false h,Bool.false_eq_true,ite_false,stable]
      change WordStore.down cell (next s) t (next s mem') s.chosen = _
      rw [ih (by omega) _ countNext frnext,valNext]
      rfl
  exact aux N le_rfl m (by simp [N]) (fun _ _ _=>rfl)

end Hierarchy.ProbeStage.Fallback

end OAI
