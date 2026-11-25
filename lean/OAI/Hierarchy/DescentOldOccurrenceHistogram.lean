import OAI.Hierarchy.ProtocolRAMSiteCounts
import OAI.Hierarchy.ProtocolRAMEndpointPrefix
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentOccurrenceCount

namespace OAI
/-! # A measured occurrence histogram and its inclusive final prefix word -/

namespace Hierarchy.DescentOldOccurrenceRAM.Histogram
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w n bins : ℕ}

def counts (base n : ℕ) := base+n
def starts (base n bins : ℕ) := counts base n+bins
def stop (base n bins : ℕ) := starts base n bins+bins+1

def program (w base n bins : ℕ) (key : Expr) : Procedure w :=
  ((scan w base n key).seq (ProtocolRAMSiteCounts.program w base (counts base n) n bins)).seq
    (ProtocolRAMEndpointPrefix.exclusive w (counts base n) (starts base n bins) bins)

def ticks (n bins : ℕ) (key : Expr) :=
  (4+n*(2*key.work+4)+((4+6*bins)+(3+11*n)))+(10+(3+12*bins))

def after (base : ℕ) (key : Expr) (tag : Fin n→Fin bins) (m : Memory w) :=
  ProtocolRAMEndpointPrefix.image (starts base n bins) (Computability.BorderVNP.FragmentBucket.start tag)
    (ProtocolRAMSiteCounts.image (counts base n) tag (ProtocolRAM.image base n key m)) bins

private theorem bucket (tag : Fin n→Fin bins) (b : Fin bins) :
    Computability.BorderVNP.FragmentBucket.count tag b=count (fun i=>tag i=b) := by
  unfold Computability.BorderVNP.FragmentBucket.count Computability.BorderVNP.Crossing.Profile.histogram Computability.BorderVNP.Crossing.Profile.positions count
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

theorem run (base : ℕ) (key : Expr) (tag : Fin n→Fin bins) (m : Memory w)
    (read : ∀i,key.eval m (i.val:Word w)=((tag i).val:Word w))
    (low : key.Fits w base) (space : stop base n bins < 2^w) :
    (program w base n bins key).Exec m (after base key tag m) (ticks n bins key) := by
  let mem := ProtocolRAM.image base n key m
  let mass := ProtocolRAMSiteCounts.image (counts base n) tag mem
  have big := space
  dsimp [stop,starts,counts] at big
  have writable : (scan w base n key).Exec m mem _ := scan_exec base n key m low (by omega)
  have counted : (ProtocolRAMSiteCounts.program w base (counts base n) n bins).Exec mem mass _ :=
    ProtocolRAMSiteCounts.run base (counts base n) tag mem le_rfl (by unfold counts;omega)
      (fun i=>(ProtocolRAMGeneratedWrite.read_image base n key m i).trans (read i))
  have pref : (ProtocolRAMEndpointPrefix.exclusive w (counts base n) (starts base n bins) bins).Exec
      mass (ProtocolRAMEndpointPrefix.image (starts base n bins) (Computability.BorderVNP.FragmentBucket.start tag) mass bins) (10+(3+12*bins)) :=
    ProtocolRAMEndpointPrefix.run (counts base n) (starts base n bins) bins
    (Computability.BorderVNP.FragmentBucket.start tag) mass le_rfl space (Computability.BorderVNP.FragmentBucket.start_zero tag) (by
      intro i hi
      let slot : Fin bins := ⟨i,hi⟩
      have step := Computability.BorderVNP.FragmentBucket.start_step tag slot
      change (Computability.BorderVNP.FragmentBucket.start tag (slot.val+1):Word w)=_
      rw [step,Nat.cast_add]
      exact congrArg ((Computability.BorderVNP.FragmentBucket.start tag i:Word w)+·)
        (ProtocolRAMSiteCounts.bin (counts base n) tag mem slot).symm)
  unfold program after ticks
  apply Procedure.Exec.then (b:=mass)
  · apply Procedure.Exec.then (b:=mem)
    · exact writable
    · exact counted
  · exact pref

theorem mass (base : ℕ) (key : Expr) (tag : Fin n→Fin bins) (m : Memory w) (b : Fin bins) :
    after base key tag m (counts base n+b.val)=(count (fun i=>tag i=b):Word w) := by
  unfold after
  rw [ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by unfold starts;have := b.isLt;omega))]
  exact (ProtocolRAMSiteCounts.bin (counts base n) tag (ProtocolRAM.image base n key m) b).trans
    (congrArg (fun t : ℕ=>(t:Word w)) (bucket tag b))

theorem prefix_count (tag : Fin n→Fin bins) (i : ℕ) (bound : i≤bins) :
    Computability.BorderVNP.FragmentBucket.start tag i = count (fun j=>(tag j).val < i) := by
  induction i with
  | zero => simp [Computability.BorderVNP.FragmentBucket.start_zero,count]
  | succ i ih =>
    let v : Fin bins := ⟨i,by omega⟩
    have step := Computability.BorderVNP.FragmentBucket.start_step tag v
    change Computability.BorderVNP.FragmentBucket.start tag (i+1)=Computability.BorderVNP.FragmentBucket.start tag i+_ at step
    rw [step,ih (by omega),bucket tag v]
    change count _ + count (fun j=>tag j=v)=count _
    simp only [count_eq_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases lt : (tag j).val < i
    · simp [lt,(show tag j≠v by intro eqn;rw [eqn] at lt;exact (lt_irrefl i) lt),
        Nat.lt_succ_of_lt lt]
    · by_cases eqn : tag j=v
      · simp [eqn,v]
      · have diff : (tag j).val≠i := fun same=>eqn (Fin.ext same)
        simp [lt,eqn,show ¬(tag j).val < i+1 by omega]

theorem prefix_read (base : ℕ) (key : Expr) (tag : Fin n→Fin bins) (m : Memory w) (i : ℕ) (hi : i≤bins) :
    after base key tag m (starts base n bins+i)=(count (fun j=>(tag j).val < i):Word w) := by
  unfold after
  rw [ProtocolRAMEndpointPrefix.read _ _ _ _ _ hi,prefix_count tag i hi]

theorem frame (base : ℕ) (key : Expr) (tag : Fin n→Fin bins) (m : Memory w) (a : ℕ) (h : a<base) :
    after base key tag m a=m a := by
  unfold after
  have hl : a < counts base n := by unfold counts;omega
  rw [ProtocolRAMEndpointPrefix.frame (starts base n bins) _ _ _ a (.inl (by unfold starts;omega)),
    ProtocolRAMSiteCounts.frame _ _ _ _ (.inl hl),ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h)]

end
end Hierarchy.DescentOldOccurrenceRAM.Histogram

end OAI
