import OAI.Hierarchy.DescentWholeItemsRAM

namespace OAI
/-! # Recorded chronological first-fit allocations for an entire stream of whole items -/

namespace Hierarchy.DescentPacking.FirstFitRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} {I V : Type*} [Fintype V] [DecidableEq V]

def capacityBase (bits base t : ℕ) := base+t*(2^bits+1)
def choiceWord (bits base t : ℕ) := capacityBase bits base t+2^bits

@[simp] theorem capacity_next (bits base t : ℕ) :
    capacityBase bits base (t+1)=choiceWord bits base t+1 := by
  simp [capacityBase,choiceWord,Nat.add_mul,Nat.add_assoc]

def sweep (w n bits base : ℕ) (need : ℕ→ℕ) : ℕ→ℕ→Procedure w
  | pos,0 => scan w (capacityBase bits base pos) 0 (.lit 0)
  | pos,count+1 => (procedure w n bits (capacityBase bits base pos) (need pos)
      (choiceWord bits base pos) (capacityBase bits base (pos+1))).seq (sweep w n bits base need (pos+1) count)

def history (n bits base : ℕ) (need : ℕ→ℕ) : ℕ→ℕ→Memory w→Memory w
  | _,0,m => m
  | pos,count+1,m => history n bits base need (pos+1) count
      (output n bits (capacityBase bits base pos) (need pos) (choiceWord bits base pos)
        (capacityBase bits base (pos+1)) m)

def rowCost (n : ℕ) := (4+1*(2*(1+14*n)+4))+(4+n*(2*30+4))

private theorem residual_work (bits caps need chosen : ℕ) : (residual bits caps need chosen).work=30 := rfl

private theorem geometry {n bits base t count : ℕ} (table : n≤2^bits) (src : ℕ→ℕ)
    (prefixInputs : ∀i,src i<base) (end_ : capacityBase bits base (t+(count+1))+n<2^w) :
    Room w n bits (capacityBase bits base t) (src t) (choiceWord bits base t) (capacityBase bits base (t+1)) := by
  have incl := Nat.mul_le_mul_right (2^bits+1) (show t+1≤t+(count+1) by omega)
  have pre := prefixInputs t
  exact ⟨table,le_rfl,by dsimp [capacityBase,choiceWord];omega,by rw [capacity_next];omega,
    by dsimp [capacityBase] at *;omega⟩

theorem sweep_exec (n bits base : ℕ) (src : ℕ→ℕ) (m : Memory w) (t count : ℕ)
    (table : n≤2^bits) (prefixInputs : ∀i,src i<base) (end_ : capacityBase bits base (t+count)+n<2^w) :
    (sweep w n bits base src t count).Exec m (history n bits base src t count m) (count*rowCost n+4) := by
  induction count generalizing t m with
  | zero =>
    have room : capacityBase bits base t+0<2^w := by simpa using (show capacityBase bits base (t+0)<2^w by omega)
    have run : (scan w (capacityBase bits base t) 0 (.lit 0)).Exec m
        (image (capacityBase bits base t) 0 (.lit 0) m) 4 :=
      scan_exec (capacityBase bits base t) 0 (.lit 0) m trivial room
    rw [image,fillSegment_zero] at run
    rw [Nat.zero_mul,Nat.zero_add]
    intro P R K machine pc reg pub exit installed params cfg mem entry initial
    exact run machine pc reg pub exit installed params cfg mem entry initial
  | succ c ih =>
    let mid := output n bits (capacityBase bits base t) (src t) (choiceWord bits base t)
      (capacityBase bits base (t+1)) m
    have phase := geometry table src prefixInputs end_
    have one : (procedure w n bits (capacityBase bits base t) (src t)
        (choiceWord bits base t) (capacityBase bits base (t+1))).Exec m mid (rowCost n) :=
      execute _ _ _ _ _ _ m phase
    have shift : (t+1)+c=t+(c+1) := by omega
    have tail : (sweep w n bits base src (t+1) c).Exec mid (history n bits base src (t+1) c mid)
        (c*rowCost n+4) :=
      ih (m:=mid) (t:=t+1) (by rw [shift]; exact end_)
    have clock : (c+1)*rowCost n+4 = rowCost n+(c*rowCost n+4) := by
      rw [Nat.succ_mul]
      omega
    rw [clock]
    intro P R K machine pc reg pub exit installed params cfg mem entry initial
    exact Procedure.Exec.then one tail machine pc reg pub exit installed params cfg mem entry initial

theorem history_before (n bits base : ℕ) (src : ℕ→ℕ) (m : Memory w) (t count a : ℕ)
    (early : a<capacityBase bits base t) : history n bits base src t count m a=m a := by
  induction count generalizing t m with
  | zero => rfl
  | succ c ih =>
    have above : capacityBase bits base t≤choiceWord bits base t := Nat.le_add_right _ _
    exact (ih (m:=_) (t:=t+1) (by rw [capacity_next];omega)).trans
      (frame _ _ _ _ _ _ m a (by omega) (by rw [capacity_next];omega))

/-- Actual capacity and menu words of a successful or skipped whole pack, with all
earlier choices available in exactly the same final memory. -/
theorem history_pack (bits base t : ℕ) (src : ℕ→ℕ) (amount : I→ℕ) (items : List I)
    (cap : V→ℕ) (m : Memory w) (table : Fintype.card V≤2^bits) (prefixInputs : ∀i,src i<base)
    (end_ : capacityBase bits base (t+items.length)+Fintype.card V<2^w)
    (values : capacityWords (capacityBase bits base t) cap m) (bounded : ∀v,cap v<2^w)
    (amounts : ∀i : Fin items.length,m (src (t+i.val))=(amount (items.get i):Word w))
    (widths : ∀i∈items,amount i<2^w) :
    let o := history (Fintype.card V) bits base src t items.length m
    let p := pack amount items cap
    capacityWords (capacityBase bits base (t+items.length)) p.remaining o ∧
    ∀ i : Fin p.decisions.length,o (choiceWord bits base (t+i.val))=(binTag (p.decisions.get i).2:Word w) := by
  induction items generalizing t cap m with
  | nil =>
    refine ⟨by simpa [history,pack] using values,?_⟩
    intro i
    exact Fin.elim0 i
  | cons x xs ih =>
    let n := Fintype.card V
    let a := capacityBase bits base t
    let c := choiceWord bits base t
    let b := capacityBase bits base (t+1)
    let win := firstFit (amount x) cap
    let rem := consume (amount x) cap win
    let m₁ := output n bits a (src t) c b m
    have phase := geometry table src prefixInputs (show capacityBase bits base (t+(xs.length+1))+n<2^w from end_)
    have input : m (src t)=(amount x:Word w) := by simpa using amounts (0:Fin (x::xs).length)
    obtain ⟨chosen,left⟩ := publishes cap m phase values bounded input (widths _ List.mem_cons_self)
    have keep (i : ℕ) : m₁ (src i)=m (src i) := by
      apply frame
      · have q := prefixInputs i; dsimp [a,c,capacityBase,choiceWord];omega
      · have q := prefixInputs i; dsimp [b,capacityBase];omega
    have capBound (v : V) : rem v<2^w := by
      cases which : win with
      | none => simpa [rem,which,consume] using bounded v
      | some j =>
        by_cases eqn : v=j
        · subst v; simpa [rem,which,consume] using (Nat.sub_le (cap j) (amount x)).trans_lt (bounded j)
        · simpa [rem,which,consume,Function.update_of_ne eqn] using bounded v
    have shift (j : ℕ) : t+(j+1)=(t+1)+j := by omega
    have tailEnd : capacityBase bits base ((t+1)+xs.length)+n<2^w := by
      rw [←shift xs.length]
      exact end_
    have tailAmounts (i : Fin xs.length) : m₁ (src ((t+1)+i.val))=(amount (xs.get i):Word w) := by
      rw [keep (t+1+i.val),←shift i.val]
      exact amounts i.succ
    have next := ih (t+1) rem m₁ tailEnd left capBound tailAmounts
      (fun i hi=>widths i (List.mem_cons_of_mem _ hi))
    dsimp only
    refine ⟨?_,?_⟩
    · rw [pack_remaining_cons]
      change capacityWords (capacityBase bits base (t+(xs.length+1))) (pack amount xs rem).remaining
        (history n bits base src (t+1) xs.length m₁)
      rw [shift xs.length]
      exact next.1
    · rw [pack_decisions_cons]
      intro index
      refine Fin.cases ?_ (fun i=>?_) index
      · change history n bits base src (t+1) xs.length m₁ c=(binTag win : Word w)
        exact (history_before n bits base src m₁ (t+1) xs.length c
          (by dsimp [c];rw [capacity_next];omega)).trans chosen
      · change history n bits base src (t+1) xs.length m₁ (choiceWord bits base (t+(i.val+1))) =
          (binTag ((pack amount xs rem).decisions.get i).2 : Word w)
        rw [shift i.val]
        exact next.2 i

end
end Hierarchy.DescentPacking.FirstFitRAM

end OAI
