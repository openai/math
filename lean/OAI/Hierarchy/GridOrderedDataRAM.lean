import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.ThreeFlat.RAM.OrdinalOpLoop
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # A native indexed scatter of the two endpoints of each touched rail -/

namespace Hierarchy.GridOrderedDataRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w K R : ℕ}

structure Banks where
  literal : ℕ
  dest : ℕ
  data : ℕ
  center : ℕ

def ops : List (Op 6 4) :=
  [.publicWord 2 0,.binary .add 2 2 0,.read 2 2,.publicWord 3 1,
   .binary .add 2 3 2,.publicWord 4 2,.binary .add 4 4 0,.write 2 4,
   .constant 5 1,.binary .add 0 0 5]

def words (w : ℕ) (S : Banks) (count : ℕ) : Fin 4 → Word w :=
  ![S.dest,S.data,S.center,count]

def scatter (w : ℕ) (S : Banks) (count : ℕ) : Procedure w :=
  ⟨13,6,4,OrdinalOpLoop.block w ops 0 1 3,words w S count⟩

def image (S : Banks) (slot : ℕ → ℕ) (m : Memory w) : ℕ → Memory w
  | 0 => m
  | i+1 => Function.update (image S slot m i) (S.data+slot i) ((S.center+i:ℕ):Word w)

theorem image_unchanged (S : Banks) (slot : ℕ → ℕ) (m : Memory w) (n a : ℕ)
    (away : ∀ i < n, a≠S.data+slot i) : image S slot m n a=m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [image,Function.update_of_ne (away n (Nat.lt_succ_self _))]
    exact ih (fun i hi => away i (Nat.lt_succ_of_lt hi))

theorem image_hit (S : Banks) (slot : ℕ → ℕ) (m : Memory w) (n j : ℕ)
    (hit : j < n) (uniq : ∀ i < n, slot i=slot j → i=j) :
    image S slot m n (S.data+slot j)=((S.center+j:ℕ):Word w) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases eq : j=n
    · subst j; simp [image]
    · have diff : S.data+slot j≠S.data+slot n :=
        fun same => eq ((uniq n (Nat.lt_succ_self _) (Nat.add_left_cancel same.symm)).symm)
      rw [image,Function.update_of_ne diff]
      exact ih (by omega) (fun i hi => uniq i (by omega))

set_option maxRecDepth 65536 in
private theorem trace_row (reg : Fin 6 ↪ Fin R) (pub : Fin 4 → Fin K) (v : Fin K → Word w)
    (state : Word w) (rs : Regs w R) (m : Memory w) :
    ∃ es out, trace v state (ops.map (OrdinalOpLoop.relocate reg pub)) rs m =
      some (es,out,writeMemory m (v (pub 1)+m ((v (pub 0)+rs (reg 0)).val)) (v (pub 2)+rs (reg 0))) ∧
      out (reg 0)=rs (reg 0)+1 ∧ out (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem scatter_spec (S : Banks) (n d : ℕ) (slot : ℕ → ℕ) (fit : n < 2^w)
    (destFit : S.dest+n ≤ 2^w) (dataFit : S.data+d ≤ 2^w) (inside : ∀ i < n,slot i < d)
    (separate : S.data+d ≤ S.dest ∨ S.dest+n ≤ S.data) :
    (scatter w S n).Spec (fun m => ∀ i < n, m (S.dest+i)=(slot i:Word w))
      (fun m o => o=image S slot m n) (3+11*n) := by
  intro pcs regs pubs M pc reg pub exit rom data c m entry mounted
  change Fin 6↪Fin regs at reg
  change Fin 4→Fin pubs at pub
  change ∀ i,M.publicData (pub i)=words w S n i at data
  obtain ⟨out,act,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 3 M pc reg pub exit rom n fit
    (data 3) (image S slot m) (by
      intro i hi state rs cur bound
      obtain ⟨es,z,run,next,keep⟩ := trace_row reg pub M.publicData state rs (image S slot m i)
      refine ⟨es,z,?_,by simpa [cur] using next,keep.trans bound⟩
      rw [data 0,data 1,data 2,cur] at run
      change trace _ _ _ _ _ = some (_,_,writeMemory (image S slot m i)
        ((S.data:Word w)+image S slot m i (((S.dest:Word w)+(i:Word w)).val))
        ((S.center:Word w)+(i:Word w))) at run
      have read := image_unchanged S slot m i (S.dest+i) (by
        intro j hj
        have s := inside j (by omega)
        omega)
      have ipos : S.dest+i < 2^w := by omega
      have opos : S.data+slot i < 2^w := by have s := inside i hi; omega
      have op : writeMemory (image S slot m i) ((S.data+slot i:ℕ):Word w) ((S.center+i:ℕ):Word w) =
          image S slot m (i+1) := by
        funext a
        simp only [writeMemory,Fin.val_cast_of_lt opos,image]
        by_cases eq : a=S.data+slot i
        · subst a; rw [ite_eq_left rfl,Function.update_self]
        · rw [ite_eq_right eq,Function.update_of_ne eq]
      simpa only [←Nat.cast_add,Fin.val_cast_of_lt ipos,read,mounted i hi,op] using run)
    c entry
  exact ⟨_,by change 3+n*11 ≤ 3+11*n; omega,out,_,act,stop,rfl⟩

def prepare (w : ℕ) (S : Banks) (d n : ℕ) : Procedure w :=
  (PhysicalInputPhases.copying w S.literal d S.data).seq (scatter w S n)

def prepared (S : Banks) (d n : ℕ) (slot : ℕ → ℕ) (m : Memory w) :=
  image S slot (PhysicalInputCopy.copied S.literal d S.data m) n

theorem prepared_frame (S : Banks) (d n : ℕ) (slot : ℕ → ℕ) (m : Memory w) (a : ℕ)
    (within : ∀ i < n,slot i < d) (away : a < S.data ∨ S.data+d ≤ a) :
    prepared S d n slot m a=m a := by
  unfold prepared
  rw [image_unchanged S slot _ n _ (by intro i hi; have := within i hi; omega)]
  exact PhysicalInputCopy.copied_outside _ _ _ _ _ away

/-- Copy one literal pointer per data pin, then replace the destinations of
the supplied touched endpoint records with the corresponding center pointers. -/
theorem prepare_spec (S : Banks) (d n : ℕ) (slot : ℕ → ℕ)
    (nf : n < 2^w) (dstFit : S.dest+n ≤ 2^w) (dataFit : S.data+d < 2^w)
    (litFit : S.literal+d < 2^w) (within : ∀ i < n,slot i < d)
    (away : S.data+d ≤ S.dest ∨ S.dest+n ≤ S.data) (input : S.data ≤ S.literal ∨ S.literal+d ≤ S.data) :
    (prepare w S d n).Spec (fun m => ∀ i < n,m (S.dest+i)=(slot i:Word w))
      (fun m o => o=prepared S d n slot m) (9+5*d+11*n) := by
  intro pcs regs pubs M pc reg pub exit rom data c m entry mounted
  let A := PhysicalInputPhases.copying w S.literal d S.data
  let B := scatter w S n
  let mid := PhysicalInputCopy.copied S.literal d S.data m
  have copy : A.Exec m mid (6+5*d) :=
    Procedure.Spec.exec (PhysicalInputPhases.copying_spec S.literal d S.data litFit dataFit input) m trivial
  have ok : ∀ i < n, mid (S.dest+i)=(slot i:Word w) := by
    intro i hi
    rw [show mid (S.dest+i)=m (S.dest+i) from PhysicalInputCopy.copied_outside _ _ _ _ _ (by omega)]
    exact mounted i hi
  have put : B.Exec mid (image S slot mid n) (3+11*n) :=
    Procedure.Spec.exec (scatter_spec S n d slot nf dstFit dataFit.le within away) mid ok
  have run : (prepare w S d n).Exec m (prepared S d n slot m) (9+5*d+11*n) :=
    Procedure.Spec.mono (Procedure.Exec.then copy put) (fun _ h => h) (fun _ _ h => h) (by omega)
  exact run M pc reg pub exit rom data c m entry rfl

end Hierarchy.GridOrderedDataRAM

end OAI
