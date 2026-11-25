import OAI.Hierarchy.DescentWholeItemsRAM

namespace OAI
/-! # Writing compact nine-word replacement records for a matched whole item -/

namespace Hierarchy.DescentPacking.PairRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
variable {w n : ℕ}

/-- Scalar addresses are supplied by the first-fit row and its cumulative input
directory. Both old-edge directories and the incidence arrays are immutable. -/
structure Inputs where
  choice : ℕ
  amount : ℕ
  acceptedBefore : ℕ
  thinBefore : ℕ
  binStart : Bank
  initialCapacity : Bank
  remainingBefore : Bank
  thickEdges : Bank
  thinEdges : Bank
  oldSource : Bank
  oldTarget : Bank
  profiles : Bank

def scalar (a : ℕ) : Expr := .lookup ⟨a,0⟩ (.lit 0)
def add (a b : Expr) : Expr := .op .add a b
def nine (e : Expr) : Expr :=
  let double (x : Expr) := add x x
  add (double (double (double e))) e

def ordinal (s : Inputs) := add (scalar s.acceptedBefore) .row
def thin (s : Inputs) : Expr := .lookup s.thinEdges (add (scalar s.thinBefore) .row)
def thick (s : Inputs) : Expr :=
  let tag := scalar s.choice
  let used := Expr.op .sub (.lookup s.initialCapacity tag) (.lookup s.remainingBefore tag)
  .lookup s.thickEdges (add (.lookup s.binStart tag) (add used .row))

/-- The last two fields are the stage's scheduled scale word and the profile code
selected by the corresponding occurrence on its own branch tape. -/
def field (s : Inputs) (z : ℕ) : Fin 9→Expr :=
  ![ordinal s,thick s,thin s,.lookup s.oldSource (thick s),.lookup s.oldTarget (thick s),
    .lookup s.oldSource (thin s),.lookup s.oldTarget (thin s),.lit z,.lookup s.profiles (ordinal s)]

def address (s : Inputs) (bins dest dead f : ℕ) : Expr :=
  let inactive := add (.lit dead) .row
  let live := add (.lit (dest+f)) (nine (ordinal s))
  .branch .lt (scalar s.choice) (.lit bins)
    (.branch .lt .row (scalar s.amount) live inactive) inactive

def target (s : Inputs) (bins dest dead f : ℕ) (m : Memory w) (q : Fin n) :=
  if (m s.choice).val < bins ∧ q.val < (m s.amount).val then
    dest+9*((m s.acceptedBefore).val+q.val)+f
  else dead+q.val

@[simp] theorem scalar_eval (a : ℕ) (m : Memory w) (r : Word w) :
    (scalar a).eval m r=m a := by simp [scalar,Expr.eval,Bank.read,Bank.size]

@[simp] theorem add_eval (x y : Expr) (m : Memory w) (r : Word w) :
    (add x y).eval m r=x.eval m r+y.eval m r := rfl

private theorem eval_nine (e : Expr) (m : Memory w) (r : Word w) :
    (nine e).eval m r=9*e.eval m r := by simp [nine];ring

theorem target_eval (s : Inputs) (bins dest dead f : ℕ) (m : Memory w) (q : Fin n)
    (rows : n < 2^w) (count : bins < 2^w) :
    (address s bins dest dead f).eval m (q.val:Word w)=(target s bins dest dead f m q:Word w) := by
  have hq := q.isLt.trans rows
  have choice_lt : m s.choice < (bins : Word w) ↔ (m s.choice).val < bins := by
    change (m s.choice).val < (bins : Word w).val ↔ _
    rw [Fin.val_cast_of_lt count]
  have row_lt : (q.val : Word w) < m s.amount ↔ q.val < (m s.amount).val := by
    change (q.val : Word w).val < (m s.amount).val ↔ _
    rw [Fin.val_cast_of_lt hq]
  simp only [address,Expr.eval,scalar_eval,Comparison.test,decide_eq_true_eq,choice_lt,row_lt,
    add_eval,eval_nine,ordinal,target]
  by_cases chosen : (m s.choice).val < bins <;> by_cases small : q.val < (m s.amount).val <;>
    simp [chosen,small,Nat.cast_add,Nat.cast_mul,Fin.cast_val_eq_self]; ring

theorem target_injective (s : Inputs) (bins dest dead : ℕ) (f : Fin 9) (m : Memory w)
    (apart : dest+9*((m s.acceptedBefore).val+n)≤dead) :
    Function.Injective (target (n:=n) s bins dest dead f.val m) := by
  intro i j hit
  unfold target at hit
  split_ifs at hit <;> apply Fin.ext <;> have := i.isLt <;> have := j.isLt <;> have := f.isLt <;> omega

def pass (w n : ℕ) (s : Inputs) (z bins dest dead scratch : ℕ) (f : Fin 9) :=
  ProtocolRAMGeneratedWrite.program w scratch (scratch+n) n (address s bins dest dead f.val) (field s z f)

def time (n : ℕ) (s : Inputs) (z bins dest dead : ℕ) (f : Fin 9) :=
  ProtocolRAMGeneratedWrite.work n (address s bins dest dead f.val) (field s z f)

def writes (s : Inputs) (z bins dest dead scratch : ℕ) (f : Fin 9) (m : Memory w) :=
  ProtocolRAMGeneratedWrite.image scratch (scratch+n) (address s bins dest dead f.val) (field s z f)
    (target (n:=n) s bins dest dead f.val m) (fun q=>(field s z f).eval m (q.val:Word w)) m

structure Early (w : ℕ) (s : Inputs) (cut : ℕ) : Prop where
  choice : (Bank.mk s.choice 0).Fits w cut
  amount : (Bank.mk s.amount 0).Fits w cut
  acceptedBefore : (Bank.mk s.acceptedBefore 0).Fits w cut
  thinBefore : (Bank.mk s.thinBefore 0).Fits w cut
  binStart : s.binStart.Fits w cut
  initialCapacity : s.initialCapacity.Fits w cut
  remainingBefore : s.remainingBefore.Fits w cut
  thickEdges : s.thickEdges.Fits w cut
  thinEdges : s.thinEdges.Fits w cut
  oldSource : s.oldSource.Fits w cut
  oldTarget : s.oldTarget.Fits w cut
  profiles : s.profiles.Fits w cut

structure Space (w n : ℕ) (s : Inputs) (bins dest dead scratch : ℕ) (m : Memory w) : Prop
    extends Early w s dest where
  count : bins < 2^w
  dense : dest+9*((m s.acceptedBefore).val+n)≤dead
  padding : dead+n≤ scratch
  end_ : scratch+2*n < 2^w

theorem fits {s : Inputs} {z bins dest dead : ℕ}
    (b : Early w s dest) (f : Fin 9) :
    (address s bins dest dead f.val).Fits w dest ∧ (field s z f).Fits w dest := by
  have choice : (scalar s.choice).Fits w dest := ⟨b.choice,trivial⟩
  have need : (scalar s.amount).Fits w dest := ⟨b.amount,trivial⟩
  have idx : (ordinal s).Fits w dest := ⟨⟨b.acceptedBefore,trivial⟩,trivial⟩
  have t : (thin s).Fits w dest := ⟨b.thinEdges,⟨b.thinBefore,trivial⟩,trivial⟩
  have h : (thick s).Fits w dest := ⟨b.thickEdges,⟨b.binStart,choice⟩,
    ⟨⟨b.initialCapacity,choice⟩,⟨b.remainingBefore,choice⟩⟩,trivial⟩
  have nineOK : (nine (ordinal s)).Fits w dest := by simp [nine,add,Expr.Fits,idx]
  constructor
  · exact ⟨choice,trivial,⟨trivial,need,⟨trivial,nineOK⟩,⟨trivial,trivial⟩⟩,⟨trivial,trivial⟩⟩
  · fin_cases f
    · exact idx
    · exact h
    · exact t
    · exact ⟨b.oldSource,h⟩
    · exact ⟨b.oldTarget,h⟩
    · exact ⟨b.oldSource,t⟩
    · exact ⟨b.oldTarget,t⟩
    · trivial
    · exact ⟨b.profiles,idx⟩

private theorem target_below {s : Inputs} {bins dest dead scratch : ℕ} {m : Memory w}
    (space : Space w n s bins dest dead scratch m) (f : Fin 9) (q : Fin n) :
    target s bins dest dead f.val m q < scratch := by
  have := space.dense
  have := space.padding
  have := q.isLt
  have := f.isLt
  unfold target
  split <;> omega

theorem execute {s : Inputs} {z bins dest dead scratch : ℕ} (m : Memory w)
    (space : Space w n s bins dest dead scratch m) (f : Fin 9) :
    (pass w n s z bins dest dead scratch f).Exec m (writes (n:=n) s z bins dest dead scratch f m)
      (time n s z bins dest dead f) := by
  have end_ := space.end_
  obtain ⟨a,v⟩ := fits (z:=z) (bins:=bins) (dead:=dead) space.toEarly f
  have le : dest≤ scratch := by have := space.dense;have := space.padding;omega
  intro P R K machine
  exact ProtocolRAMGeneratedWrite.run _ _ _ _ _ _ m (ProtocolRAMGeneratedWrite.fits_mono _ le a) (ProtocolRAMGeneratedWrite.fits_mono _ le v) le_rfl (by omega)
    (target_eval s bins dest dead f.val m · (by omega) space.count) (fun _=>rfl)
    (fun i=>(target_below space f i).trans (by omega))
    (fun i j=>by have := target_below space f j;omega) (fun i j=>by have := target_below space f j;omega)
    machine

theorem stored {s : Inputs} {z bins dest dead scratch : ℕ} {m : Memory w}
    (space : Space w n s bins dest dead scratch m) (f : Fin 9) (q : Fin n)
    (chosen : (m s.choice).val < bins) (small : q.val < (m s.amount).val) :
    writes (n:=n) s z bins dest dead scratch f m (dest+9*((m s.acceptedBefore).val+q.val)+f.val)=
      (field s z f).eval m (q.val:Word w) := by
  rw [show dest+9*((m s.acceptedBefore).val+q.val)+f.val=target s bins dest dead f.val m q by
    simp [target,chosen,small]]
  exact ProtocolRAMGeneratedWrite.read _ _ _ _ _ _ _ (target_injective s bins dest dead f m space.dense) q

theorem keeps (s : Inputs) (z bins dest dead scratch : ℕ) (f : Fin 9) (m : Memory w) (a : ℕ)
    (away : ∀q : Fin n, a≠target s bins dest dead f.val m q)
    (outside : a < scratch ∨ scratch+2*n≤a) :
    writes (n:=n) s z bins dest dead scratch f m a=m a :=
  ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ away (by omega) (by omega)

end Hierarchy.DescentPacking.PairRAM

end OAI
