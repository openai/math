import OAI.Hierarchy.DescentWholeItems
import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native first-fit choice and immutable residual capacities of a whole-item pack -/

namespace Hierarchy.DescentPacking.FirstFitRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {w n : ℕ}

def atWord (a : ℕ) : Expr := .lookup ⟨a,0⟩ (.lit 0)

private theorem word_eval (a : ℕ) (m : Memory w) (r : Word w) : (atWord a).eval m r=m a := by
  simp [atWord,Expr.eval,Bank.read,Bank.size]

private theorem word_fits {a out : ℕ} (lo : a<out) (wide : 1<2^w) : (atWord a).Fits w out :=
  ⟨⟨Nat.zero_lt_one,wide,Nat.succ_le_of_lt lo⟩,trivial⟩

/-- Emit the first zero-based directory ordinal with sufficient residual capacity.
The sentinel n records that the genuine scan exhausted every bin. -/
def pick (caps need : ℕ) : List (Fin n)→Expr
  | [] => .lit n
  | i::is => .branch .lt (atWord (caps+i.val)) (atWord need) (pick caps need is) (.lit i.val)

def choose (n caps need : ℕ) := pick caps need (List.finRange n)

def tag (n : ℕ) (p : Option (Fin n)) := (p.map Fin.val).getD n

private theorem pick_eval (caps need x : ℕ) (m : Memory w) (r : Word w) (cap : Fin n→ℕ)
    (needWord : (m need).val=x) (values : ∀ i,(m (caps+i.val)).val=cap i) (is : List (Fin n)) :
    (pick caps need is).eval m r=(tag n (is.find? (fun i=>decide (x≤cap i))):Word w) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [pick,Expr.eval,word_eval,Comparison.test,decide_eq_true_eq,List.find?_cons]
    change (if (m (caps+i.val)).val<(m need).val then _ else _) = _
    rw [values,needWord]
    by_cases fits : x≤cap i
    · simp [fits,tag,not_lt_of_ge fits]
    · simp [fits,lt_of_not_ge fits,ih]

private theorem pick_fits {caps need out : ℕ} (room : caps+n≤out) (small : need<out) (wide : 1<2^w)
    (is : List (Fin n)) : (pick caps need is).Fits w out := by
  induction is with
  | nil => trivial
  | cons i is ih =>
    have hi := i.isLt
    exact ⟨word_fits (by omega) wide,word_fits small wide,ih,trivial⟩

theorem pick_work (caps need : ℕ) (is : List (Fin n)) :
    (pick caps need is).work=1+14*is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [pick,atWord,Expr.work,ih];omega

def binTag (picked : Option V) :=
  tag (Fintype.card V) (picked.map (Fintype.equivFin V))

omit [DecidableEq V] in
private theorem tag_eq (x : ℕ) (cap : V→ℕ) :
    tag (Fintype.card V) ((List.finRange _).find? fun i=>decide (x≤cap ((Fintype.equivFin V).symm i))) =
      binTag (firstFit x cap) := by
  let e := Fintype.equivFin V
  change tag _ _ = tag _ ((((List.finRange _).map e.symm).find? (fun v=>decide (x≤cap v))).map e)
  rw [List.find?_map,Option.map_map]
  simp [Function.comp_def,e]

/-- An output row equals its old capacity minus this whole quantity precisely when
its ordinal is the winner in the preceding physical word. -/
def residual (bits caps need chosen : ℕ) : Expr :=
  let remaining := Expr.lookup ⟨caps,bits⟩ .row
  .branch .eq .row (atWord chosen) (.op .sub remaining (atWord need)) remaining

def interim (n caps need chosen : ℕ) (m : Memory w) :=
  image chosen 1 (choose n caps need) m

def output (n bits caps need chosen dest : ℕ) (m : Memory w) :=
  image dest n (residual bits caps need chosen) (interim n caps need chosen m)

def procedure (w n bits caps need chosen dest : ℕ) :=
  (scan w chosen 1 (choose n caps need)).seq (scan w dest n (residual bits caps need chosen))

structure Room (w n bits caps need chosen dest : ℕ) : Prop where
  count : n≤2^bits
  capEnd : caps+2^bits≤chosen
  amount : need<chosen
  choice : chosen<dest
  end_ : dest+n<2^w

theorem execute (n bits caps need chosen dest : ℕ) (m : Memory w) (space : Room w n bits caps need chosen dest) :
    (procedure w n bits caps need chosen dest).Exec m (output n bits caps need chosen dest m)
      ((4+1*(2*(1+14*n)+4))+(4+n*(2*(residual bits caps need chosen).work+4))) := by
  obtain ⟨count,ce,am,ch,end_⟩ := space
  have bnd : 2^bits<2^w := by omega
  have wide : 1<2^w := Nat.lt_of_le_of_lt (Nat.two_pow_pos bits) bnd
  have cp : (Bank.mk caps bits).Fits w dest := ⟨Nat.two_pow_pos _,bnd,ce.trans ch.le⟩
  have init : (scan w chosen 1 (choose n caps need)).Exec _ _ _ := scan_exec chosen 1 (choose n caps need) m
    (pick_fits (by omega) am wide (List.finRange n)) (by omega)
  simp only [choose,pick_work,List.length_finRange] at init
  apply Procedure.Exec.then init
  exact scan_exec dest n (residual bits caps need chosen) (interim n caps need chosen m)
    ⟨trivial,word_fits ch wide,
    ⟨⟨cp,trivial⟩,word_fits (am.trans ch) wide⟩,⟨cp,trivial⟩⟩ end_

def capacityWords (caps : ℕ) (cap : V→ℕ) (m : Memory w) : Prop :=
  ∀ v,m (caps+(Fintype.equivFin V v).val)=(cap v:Word w)

theorem publishes {bits caps need chosen dest x : ℕ} (cap : V→ℕ) (m : Memory w)
    (space : Room w (Fintype.card V) bits caps need chosen dest) (values : capacityWords caps cap m)
    (small : ∀v,cap v<2^w) (amount : m need=(x:Word w)) (fits : x<2^w) :
    let selected := firstFit x cap
    let o := output (Fintype.card V) bits caps need chosen dest m
    o chosen=(binTag selected:Word w) ∧ capacityWords dest (consume x cap selected) o := by
  obtain ⟨count,ce,am,ch,end_⟩ := space
  let n := Fintype.card V
  let ord := Fintype.equivFin V
  let m₁ := interim n caps need chosen m
  let win := firstFit x cap
  have raw (i : Fin n) : (m (caps+i.val)).val=cap (ord.symm i) := by
    simpa [ord,Fin.val_cast_of_lt (small (ord.symm i))] using congrArg Fin.val (values (ord.symm i))
  have selection : m₁ chosen=(binTag win:Word w) := by
    have read := ProtocolRAMGeneratedWrite.read_image chosen 1 (choose n caps need) m (0:Fin 1)
    rw [choose,pick_eval caps need x m _ (fun i : Fin n=>cap (ord.symm i))
      (by rw [amount,Fin.val_cast_of_lt fits]) raw,tag_eq] at read
    simpa [m₁,interim,choose,win] using read
  have frame (a : ℕ) (lt : a<chosen) : m₁ a=m a := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl lt)
  have got (v : V) : (Bank.mk caps bits).read m₁ ((ord v).val:Word w)=(cap v:Word w) := by
    have hi := (ord v).isLt
    have lives : (ord v).val < 2^bits := hi.trans_le count
    have width : (ord v).val<2^w := by omega
    simp only [Bank.read,Bank.size,Fin.val_cast_of_lt width,Nat.mod_eq_of_lt lives]
    exact (frame _ (by omega)).trans (values v)
  refine ⟨(ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ch)).trans selection,?_⟩
  intro v
  rw [output,ProtocolRAMGeneratedWrite.read_image]
  change (residual bits caps need chosen).eval m₁ ((ord v).val:Word w) = _
  simp only [residual,Expr.eval,word_eval,Comparison.test,beq_iff_eq,RowOp.opcode,BinaryOp.eval,
    got,selection,frame need am,amount]
  have bounded : n<2^w := by dsimp [n];omega
  cases sel : win with
  | none =>
    have diff : ((ord v).val:Word w)≠(n:Word w) := by
      intro eqn
      have eqv := congrArg Fin.val eqn
      rw [Fin.val_cast_of_lt ((ord v).isLt.trans bounded),Fin.val_cast_of_lt bounded] at eqv
      exact (ord v).isLt.ne eqv
    simp [win] at sel
    simp [sel,binTag,tag,consume,ord,n] at diff ⊢
    simp_all [win,binTag,tag]
  | some b =>
    have enough : x≤cap b := firstFit_some sel
    have same : ((ord v).val:Word w)=((ord b).val:Word w) ↔ v=b := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt ((ord v).isLt.trans bounded),
        Fin.val_cast_of_lt ((ord b).isLt.trans bounded),←Fin.ext_iff,Equiv.apply_eq_iff_eq]
    by_cases isB : v=b
    · subst v
      simpa [win,sel,binTag,tag,ord,consume] using (Nat.cast_sub (R:=Word w) enough).symm
    · simp [win,sel,binTag,tag,ord,consume,isB,Function.update_of_ne,same] at *

theorem frame (n bits caps need chosen dest : ℕ) (m : Memory w) (a : ℕ)
    (earlier : a<chosen) (below : a<dest) : output n bits caps need chosen dest m a=m a :=
  (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl below)).trans
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl earlier))

end
end Hierarchy.DescentPacking.FirstFitRAM

end OAI
