import OAI.Hierarchy.ProtocolRAMCalendarPrior
import OAI.Hierarchy.ProtocolRAMCalendar

namespace OAI
/-! # Address bounds for the actual stop program's chronological conditionals -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical

private theorem any_before (xs : List ℕ) (code : ℕ) (y n : Expr) (cut : ℕ)
    (hy : y.inputEnd≤cut) (hn : n.inputEnd≤cut) (hx : ∀x∈xs,x<cut) :
    (anyMode xs code y n).inputEnd≤cut := by
  induction xs with
  | nil=>exact hn
  | cons a l ih=>
    change max (max (word a).inputEnd (Expr.lit code).inputEnd)
      (max y.inputEnd (anyMode l code y n).inputEnd)≤cut
    have prior:=hx a (List.mem_cons_self ..)
    have read : (word a).inputEnd≤cut := by change max (a+1) 0≤cut;omega
    exact max_le (max_le read (Nat.zero_le _)) (max_le hy (ih (fun b h=>hx b (List.mem_cons_of_mem _ h))))

private theorem earlier_range (f : ℕ→ℕ) (n cut : ℕ) (h : ∀i<n,f i<cut) :
    ∀a∈(List.range n).map f,a<cut := by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
  exact h i (List.mem_range.mp hi)

theorem stop_before (c : Mesh) (modeAt : Attempt→ℕ) (a : Attempt) (cut : ℕ)
    (older : ∀b,position c (.attempt b)<position c (.attempt a)→modeAt b<cut) :
    (stop c modeAt a).inputEnd≤cut := by
  let bit (b : Attempt) : ℕ:=if modeAt b<cut then 0 else 1
  have prior:=agrees_earlier c bit (fun _=>0) a (fun b hb=>ite_eq_left (older b hb))
  have ltOf (b : Attempt) (h : bit b=0) : modeAt b<cut := by
    by_contra hp
    simp [bit,hp] at h
  cases a with
  | outer p a=>
    rcases prior with ⟨saturated,closed⟩
    have sat:=earlier_range (fun i=>modeAt (.outer i (c.outerFuel-1))) p cut (fun i hi=>ltOf _ (saturated i hi))
    have last:=any_before _ 1 (.lit 1) (.lit 0) cut (Nat.zero_le _) (Nat.zero_le _)
      (earlier_range (fun i=>modeAt (.outer p i)) a cut (fun i hi=>ltOf _ (closed i hi)))
    by_cases spent : c.outerFuel=0
    · simpa only [stop,outerSaturated,spent,ite_true,Expr.inputEnd] using Nat.zero_le cut
    · simp only [stop,outerSaturated,spent,ite_false]
      have byThree:=any_before _ 3 (.lit 1) _ cut (Nat.zero_le _) last sat
      exact any_before _ 2 (.lit 1) _ cut (Nat.zero_le _) byThree sat
  | inner p a j b=>
    rcases prior with ⟨outer,each,last⟩
    have read:=ltOf _ outer
    have sat:=earlier_range (fun t=>modeAt (.inner p a t (c.innerFuel-1))) j cut (fun i hi=>ltOf _ (each i hi))
    have last':=any_before _ 1 (.lit 1) (.lit 0) cut (Nat.zero_le _) (Nat.zero_le _)
      (earlier_range (fun i=>modeAt (.inner p a j i)) b cut (fun i hi=>ltOf _ (last i hi)))
    change max (max (max (modeAt (.outer p a)+1) 0) 0)
      (max (innerSaturated c modeAt p a j (.lit 1) _).inputEnd 0)≤cut
    refine max_le (by omega) (max_le ?_ (Nat.zero_le _))
    unfold innerSaturated
    split
    · exact Nat.zero_le _
    · exact any_before _ 2 _ _ _ (Nat.zero_le _) last' sat

end Hierarchy.ProtocolRAM.Calendar

end OAI
