import OAI.Hierarchy.DescentPaddedRawField

namespace OAI
/-! # Five simultaneously resident raw field columns from one fixed, padded native program -/

namespace Hierarchy.DescentOrdinaryRawRows.Five
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM
open scoped Fin.CommRing Classical
noncomputable section

def column : ℕ → Column
  | 0=>.src | 1=>.dst | 2=>.width | 3=>.core | _=>.repeats

def index : Column→ℕ
  | .src=>0 | .dst=>1 | .width=>2 | .core=>3 | .repeats=>4

@[simp] theorem column_index (f : Column) : column (index f)=f := by cases f <;> rfl
theorem index_lt (f : Column) : index f<5 := by cases f <;> decide

def capacity (oldCap pairCap : ℕ) := oldCap+10*pairCap

/-- The five true columns are disjoint contiguous regions. The two scratch vectors
are shared by all fifty generated-write passes. -/
def output (base oldCap pairCap j : ℕ) : Output where
  base:=base+j*capacity oldCap pairCap
  dest:=base+5*capacity oldCap pairCap
  vals:=base+5*capacity oldCap pairCap+pairCap

variable (S : Sources) (lens : Padded.Counts) (b w base oldCap pairCap : ℕ)
local notation "outAt" => output base oldCap pairCap
local notation "cap" => capacity oldCap pairCap

def program : ℕ→Procedure w
  | 0=>scan w base 0 (.lit 0)
  | j+1=>(program j).seq (Padded.field S (outAt j) lens b (column j) w oldCap pairCap)

def steps : ℕ→ℕ
  | 0=>4
  | j+1=>steps j+Padded.field_cost S (outAt j) lens b (column j) oldCap pairCap

variable {S lens b w base oldCap pairCap}

structure Bounds (S : Sources) (lens : Padded.Counts) (b w base oldCap pairCap : ℕ) : Prop where
  field : ∀ j, j<5→Padded.Bounds S (output base oldCap pairCap j) lens b (column j) w oldCap pairCap
  boot : base<2^w
  oldSource : ∀f,(S.old b f).Fits w base
  bornSource : ∀s f,(S.born b s f).Fits w base
  oldCount : lens.old<base
  pairCount : lens.pairs<base

variable {n ne : ℕ}
variable (raw : Column→Fin ne→Word w) (born : Column→Born→Fin n→Word w)

structure Wrote (base oldCap pairCap : ℕ) (m o : Memory w) (t : ℕ) : Prop where
  frame : ∀a, a<base→ o a=m a
  original : ∀j, j<t→∀i : Fin ne,o ((output base oldCap pairCap j).base+i.val)=raw (column j) i
  fresh : ∀j, j<t→∀s i,o ((output base oldCap pairCap j).addr ne s.index.val i.val)=born (column j) s i
  padding : ∀ (j : ℕ), j < t → ∀ (i : ℕ), ne + 10*n ≤ i → i < capacity oldCap pairCap → o ((output base oldCap pairCap j).base+i)=0

private theorem previous {i j x : ℕ} (prior : i<j) (small : x<cap) :
    (outAt i).base+x < (outAt j).base := by
  have le:=Nat.mul_le_mul_right cap (Nat.succ_le_of_lt prior)
  simp only [Nat.succ_mul] at le
  dsimp only [output]
  omega

theorem publish (S : Sources) (lens : Padded.Counts) (b w base oldCap pairCap : ℕ)
    (raw : Column→Fin ne→Word w) (born : Column→Born→Fin n→Word w)
    (m : Memory w) (room : Bounds S lens b w base oldCap pairCap)
    (smallO : ne≤oldCap) (smallP : n≤pairCap) (oldR : m lens.old=(ne:Word w)) (pairR : m lens.pairs=(n:Word w))
    (org : ∀f i,(S.old b f).eval m (i.val:Word w)=raw f i)
    (new : ∀f s i,(S.born b s f).eval m (i.val:Word w)=born f s i)
    (t : ℕ) (legal : t≤5) :
    ∃o, (program S lens b w base oldCap pairCap t).Exec m o (steps S lens b base oldCap pairCap t) ∧
      Wrote raw born base oldCap pairCap m o t := by
  induction t with
  | zero=>
    refine ⟨m,?_,⟨fun _ _=>rfl,fun _ h=>by omega,fun _ h=>by omega,fun _ h=>by omega⟩⟩
    have same : ProtocolRAM.image base 0 (.lit 0) m=m := by
      funext index
      simp [ProtocolRAM.image,fillSegment]
    intro P R C M pc reg pub exit rom advice cfg raw enter equal
    have boot := scan_exec base 0 (.lit 0) m trivial (by simpa using room.boot) M pc reg pub exit rom advice cfg raw enter equal
    simpa only [steps,Nat.zero_mul,Nat.add_zero,same] using boot
  | succ t ih=>
    obtain ⟨prev,run,prior⟩:=ih (by omega)
    have fieldOrg (i : Fin ne) := (eval_below (S.old b (column t)) (i.val:Word w) m prev
      (room.oldSource _) prior.frame).trans (org _ i)
    have fieldNew (s : Born) (i : Fin n) := (eval_below (S.born b s (column t)) (i.val:Word w) m prev
      (room.bornSource _ _) prior.frame).trans (new _ s i)
    obtain ⟨o,next,done⟩:=Padded.publish S (output base oldCap pairCap t) lens b (column t) w oldCap pairCap ne n
      (raw (column t)) (born (column t)) prev (room.field t (by omega)) smallO smallP
      ((prior.frame _ room.oldCount).trans oldR) ((prior.frame _ room.pairCount).trans pairR) fieldOrg fieldNew
    refine ⟨o,?_,⟨?_,?_,?_,?_⟩⟩
    · intro P R C M pc reg pub exit rom advice cfg raw enter equal
      exact Procedure.Exec.then run next M pc reg pub exit rom advice cfg raw enter equal
    · intro a h
      exact (done.before a (by dsimp [output];omega)).trans (prior.frame a h)
    · intro j hj i
      rcases Nat.lt_or_eq_of_le (by omega : j≤t) with lt|rfl
      · exact (done.before _ (previous (base:=base) (oldCap:=oldCap) (pairCap:=pairCap) lt (by have:=i.isLt;dsimp [capacity];omega))).trans (prior.original j lt i)
      · exact done.original i
    · intro j hj s i
      rcases Nat.lt_or_eq_of_le (by omega : j≤t) with lt|rfl
      · have p : ne+10*i.val+s.index.val < capacity oldCap pairCap := by
          have:=i.isLt;have:=s.index.isLt;dsimp [capacity];omega
        rw [done.before _ (by simpa [addr,Nat.add_assoc] using previous (base:=base) lt p)]
        exact prior.fresh j lt s i
      · exact done.added s i
    · intro j hj i left right
      rcases Nat.lt_or_eq_of_le (by omega : j≤t) with lt|rfl
      · exact (done.before _ (previous lt right)).trans (prior.padding j lt i left right)
      · exact done.padding i left right

end
end Hierarchy.DescentOrdinaryRawRows.Five

end OAI
