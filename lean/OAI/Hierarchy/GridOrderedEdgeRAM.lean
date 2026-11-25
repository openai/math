import OAI.Hierarchy.GridTopologyRAM
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.GridThroughOrdered
import OAI.Hierarchy.GridWiringNetwork

namespace OAI
/-! # Native generation of every physical equality pointer -/

namespace Hierarchy.GridOrderedEdgeRAM
open GridThrough GridThrough.Ordered UniversalGrid ThreeFlat
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.BitLayout RAM.PhysicalProcedure RAM.DescriptorExpr GridTopologyRAM
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
open scoped Fin.CommRing

variable {k n p r w : ℕ} {width : Fin k → ℕ}

inductive Part | focus | neighbor | through | center deriving DecidableEq

def middle : Part → ℕ → ℕ
  | .focus,_ | .center,_ => 2
  | .neighbor,n => n
  | .through,n => n+1

def offset : Part → ℕ → ℕ → ℕ
  | .focus,_,_ => 0
  | .neighbor,r,_ => r*2
  | .through,r,n => r*2+r*n
  | .center,r,n => r*2+r*n+r*(n+1)

private def label (e : Fin r) : (part : Part) → Fin (middle part n) → Candidate r n
  | .focus,j => .inl (e,finTwoEquiv j)
  | .neighbor,t => .inr (.inl (e,t))
  | .through,t => .inr (.inr (.inl (e,t)))
  | .center,j => .inr (.inr (.inr (e,finTwoEquiv j)))

private theorem label_number (e : Fin r) (part : Part) (j : Fin (middle part n)) :
    (candidateCode (label e part j)).val = offset part r n+e.val*middle part n+j.val := by
  cases part <;> simp [candidateCode,label,Ordered.addCode,offset,middle,sides,
    finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] <;>
    rw [show finTwoEquiv.symm (finTwoEquiv j)=j from finTwoEquiv.symm_apply_apply j] <;> omega

structure Banks where
  output : ℕ
  touch : ℕ
  mark : ℕ

/-- No per-edge public data. All four expressions have these same scalar operands. -/
def words (S : Banks) (r n : ℕ) : Fin 4 → Word w :=
  ![(r:Word w),(n+1:ℕ),(S.touch:Word w),(S.mark:Word w)]

abbrev T (w : ℕ) := Term3 w 4
private abbrev plus (a b : T w) : T w := .binary .add a b
private abbrev times (a b : T w) : T w := .binary .mul a b
private abbrev lit (i : ℕ) : T w := .literal (i:Word w)
private abbrev choose (x y a b : T w) : T w := .select .eq x y a b

private def rail : T w := .result 0
private def digit : T w := .result 1
private def side : T w := .result 2
private def g : T w := .parameter 1
private def hbase : T w := plus (lit 2) (times (lit 2) (.parameter 0))
private def portPtr (t b : T w) : T w :=
  plus hbase (plus (times (times rail g) (lit 2)) (plus (times (lit 2) t) b))
private def centerPtr (b : T w) : T w :=
  plus hbase (plus (times (.parameter 0) (times g (lit 2))) (plus (times (lit 2) rail) b))
private def extPtr (b : T w) : T w := plus (lit 2) (plus (times (lit 2) rail) b)
private def touch : T w := .load (plus (.parameter 2) rail)
private def marked : T w := .load (plus (.parameter 3) (plus (times rail g) digit))

def body : Part → T w
  | .focus => choose digit (lit 0)
      (choose side (lit 0) (extPtr (lit 0)) (portPtr (lit 0) (lit 0)))
      (choose side (lit 0) (portPtr (.binary .sub g (lit 1)) (lit 1)) (extPtr (lit 1)))
  | .neighbor => choose side (lit 0) (portPtr digit (lit 1)) (portPtr (plus digit (lit 1)) (lit 0))
  | .through => choose touch digit (lit 0) (choose marked (lit 1) (lit 0) (portPtr digit side))
  | .center => choose touch g (choose side (lit 0) (centerPtr digit) (lit 0))
      (choose side (lit 0) (portPtr touch digit) (centerPtr digit))

variable (P : GridThrough.Program (Fin r) n p width)

def touchValue (e : Fin r) := (P.touch e).elim (n+1) Fin.val

/-- Source banks read by the equality writer. Selection emits one mark at the
actual rail passage when the ranked catalyst slot is reserved. -/
structure Mounted (S : Banks) (m : Memory w) : Prop where
  longitudinal : ∀ e : Fin r, m (S.touch+e.val) = (touchValue P e:Word w)
  selected : ∀ (e : Fin r) (t : Fin (n+1)), m (S.mark+e.val*(n+1)+t.val) =
    (if (marks P)[(finProdFinEquiv (e,t)).val] then (1:Word w) else 0)

private def ptr (a : Addr r n) := sourceAddress (Wiring.source a)

@[simp] private theorem ptr_port (e : Fin r) (t : Fin (n+1)) (b : Bool) :
    ptr (port e t b)= 2+r*2 + (e.val*((n+1)*2)+(2*t.val+b.toNat)) := by
  simp [ptr,port,Wiring.source,sourceAddress,hiddenBase,port_number]
  ring

@[simp] private theorem ptr_center (e : Fin r) (b : Bool) :
    ptr (center (n:=n) e b) = 2+r*2 + (r*((n+1)*2)+(2*e.val+b.toNat)) := by
  simp [ptr,center,Wiring.source,sourceAddress,hiddenBase,center_number]
  ring

@[simp] private theorem ptr_ext (e : Fin r) (b : Bool) :
    ptr (n:=n) (.inr (.inl (e,b))) = 2+(2*e.val+b.toNat) := by
  simp [ptr,Wiring.source,sourceAddress,Wiring.railPin_val]

private def pick {A : Type} (s : Fin 2) (u : A×A) : A := if s=0 then u.1 else u.2
private def setting (i j s : ℕ) : Fin 3 → Word w := ![(i:Word w),(j:Word w),(s:Word w)]

private theorem touch_at (S : Banks) (m : Memory w) (mounted : Mounted P S m)
    (fit : S.touch+r ≤ 2^w) (e : Fin r) (j z : ℕ) :
    touch.eval (words S r n) m (setting e.val j z) = (touchValue P e : Word w) := by
  change m (((S.touch:Word w)+(e.val:Word w)).val) = _
  rw [← Nat.cast_add,Fin.val_cast_of_lt (show S.touch+e.val < 2^w by have := e.isLt; omega)]
  exact mounted.longitudinal e

private theorem mark_at (S : Banks) (m : Memory w) (mounted : Mounted P S m)
    (fit : S.mark+r*(n+1) ≤ 2^w) (e : Fin r) (j : Fin (n+1)) (z : ℕ) :
    marked.eval (words S r n) m (setting e.val j.val z) =
      (if (marks P)[(finProdFinEquiv (e,j)).val] then (1:Word w) else 0) := by
  have a : S.mark+(e.val*(n+1)+j.val) < 2^w := by
    have b := Nat.mul_le_mul_right (n+1) e.isLt
    rw [Nat.succ_mul] at b
    have := j.isLt
    omega
  change m (((S.mark:Word w)+((e.val:Word w)*((n+1:ℕ):Word w)+(j.val:Word w))).val) = _
  rw [←Nat.cast_mul,←Nat.cast_add,←Nat.cast_add,Fin.val_cast_of_lt a]
  simpa [Nat.add_assoc] using mounted.selected e j

private theorem choose_at (a b yes no : T w) (S : Banks) (r n : ℕ) (m : Memory w) (v : Fin 3 → Word w) :
    (choose a b yes no).eval (words S r n) m v = if a.eval (words S r n) m v = b.eval (words S r n) m v
      then yes.eval (words S r n) m v else no.eval (words S r n) m v := by
  simp only [Term.eval_select,Comparison.test,beq_iff_eq]

private theorem port_at (a b : T w) (S : Banks) (r n i j z : ℕ) (m : Memory w) :
    (portPtr a b).eval (words S r n) m (setting i j z) =
      (2+r*2+i*((n+1)*2):ℕ) + (2:Word w)*a.eval (words S r n) m (setting i j z)+
        b.eval (words S r n) m (setting i j z) := by
  simp [portPtr,hbase,rail,g,words,setting,Term.eval,BinaryOp.eval]; ring

private theorem center_at (b : T w) (S : Banks) (r n i j z : ℕ) (m : Memory w) :
    (centerPtr b).eval (words S r n) m (setting i j z) =
      (2+r*2+r*((n+1)*2)+2*i:ℕ) + b.eval (words S r n) m (setting i j z) := by
  simp [centerPtr,hbase,rail,g,words,setting,Term.eval,BinaryOp.eval]; ring

private theorem ext_at (b : T w) (S : Banks) (r n i j z : ℕ) (m : Memory w) :
    (extPtr b).eval (words S r n) m (setting i j z) =
      (2+2*i:ℕ) + b.eval (words S r n) m (setting i j z) := by
  simp [extPtr,rail,words,setting,Term.eval,BinaryOp.eval]; ring

private theorem digit_at (S : Banks) (r n i j z : ℕ) (m : Memory w) :
    digit.eval (words S r n) m (setting i j z) = (j:Word w) := rfl
private theorem side_at (S : Banks) (r n i j z : ℕ) (m : Memory w) :
    side.eval (words S r n) m (setting i j z) = (z:Word w) := rfl
private theorem g_at (S : Banks) (r n i j z : ℕ) (m : Memory w) :
    g.eval (words S r n) m (setting i j z) = (n+1:ℕ) := rfl

private theorem ptr_zero : ptr (zeroAddr (r:=r) (n:=n)) = 0 := rfl
private theorem bit_zero : finTwoEquiv (0 : Fin 2) = false := rfl
private theorem bit_one : finTwoEquiv (1 : Fin 2) = true := rfl
private theorem one_ne (two : 2 < 2^w) : (1:Word w) ≠ 0 := by
  intro eq
  have h := congrArg Fin.val eq
  change (1:ℕ)%(2^w)=0 at h
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

private theorem same (a b : ℕ) (af : a < 2^w) (bf : b < 2^w) :
    ((a:Word w)=(b:Word w)) ↔ a=b := by
  constructor
  · intro eq; simpa only [Fin.val_cast_of_lt af,Fin.val_cast_of_lt bf] using congrArg Fin.val eq
  · rintro rfl; rfl

private theorem focus_at (S : Banks) (m : Memory w) (two : 2 < 2^w) (e : Fin r) (j z : Fin 2) :
    (body .focus).eval (words S r n) m (setting e.val j.val z.val) =
      (ptr (pick z (edge P (marks P) (label (n:=n) e .focus j))) : Word w) := by
  obtain rfl|rfl : j=0 ∨ j=1 := by fin_cases j <;> decide
  all_goals obtain rfl|rfl : z=0 ∨ z=1 := by fin_cases z <;> decide
  all_goals
    simp only [body,label,bit_zero,bit_one,edge,choose_at,digit_at,side_at,port_at,ext_at,
      g_at,Term.eval_literal,Term.eval_binary,BinaryOp.eval,Fin.val_zero,Fin.val_one]
    simp [pick,ptr_ext,ptr_port,one_ne two] <;> ring

private theorem neighbor_at (S : Banks) (m : Memory w) (two : 2 < 2^w) (e : Fin r) (j : Fin n) (z : Fin 2) :
    (body .neighbor).eval (words S r n) m (setting e.val j.val z.val) =
      (ptr (pick z (edge P (marks P) (label e .neighbor j))) : Word w) := by
  obtain rfl|rfl : z=0 ∨ z=1 := by fin_cases z <;> decide
  all_goals
    simp only [body,label,edge,choose_at,digit_at,side_at,port_at,Term.eval_literal,Term.eval_binary,
      BinaryOp.eval,Fin.val_zero,Fin.val_one]
    simp [pick,ptr_port,one_ne two,Fin.val_castSucc,Fin.val_succ]; ring

private theorem through_at (S : Banks) (m : Memory w) (mounted : Mounted P S m)
    (tf : S.touch+r ≤ 2^w) (mf : S.mark+r*(n+1) ≤ 2^w) (gf : n+1 < 2^w) (two : 2 < 2^w)
    (e : Fin r) (j : Fin (n+1)) (z : Fin 2) :
    (body .through).eval (words S r n) m (setting e.val j.val z.val) =
      (ptr (pick z (edge P (marks P) (label e .through j))) : Word w) := by
  have positive : w ≠ 0 := by
    rintro rfl
    norm_num at two
  have room : touchValue P e < 2^w := by
    cases h : P.touch e with
    | none => simpa [touchValue,h] using gf
    | some t => simpa [touchValue,h] using t.isLt.trans gf
  have atSite : touchValue P e=j.val ↔ P.touch e=some j := by
    cases h : P.touch e with
    | none => simp [touchValue,h,Nat.ne_of_gt j.isLt]
    | some t => simp [touchValue,h,Fin.ext_iff]
  obtain rfl|rfl : z=0 ∨ z=1 := by fin_cases z <;> decide
  all_goals
    simp only [body,label,edge,choose_at,digit_at,side_at,port_at,Term.eval_literal,
      touch_at P S m mounted tf,mark_at P S m mounted mf,same _ _ room (j.isLt.trans gf),atSite]
    by_cases touched : P.touch e=some j <;> cases markedBit : (marks P)[(finProdFinEquiv (e,j)).val] <;>
      simp only [touched,or_true,or_false,Bool.false_eq_true,ite_false,ite_eq_left]
    all_goals simp [pick,ptr_port,ptr_zero,positive] <;> ring

private theorem center_at_edge (S : Banks) (m : Memory w) (mounted : Mounted P S m)
    (tf : S.touch+r ≤ 2^w) (gf : n+1 < 2^w) (two : 2 < 2^w) (e : Fin r) (j z : Fin 2) :
    (body .center).eval (words S r n) m (setting e.val j.val z.val) =
      (ptr (pick z (edge P (marks P) (label (n:=n) e .center j))) : Word w) := by
  obtain rfl|rfl : j=0 ∨ j=1 := by fin_cases j <;> decide
  all_goals obtain rfl|rfl : z=0 ∨ z=1 := by fin_cases z <;> decide
  all_goals
    simp only [body,label,bit_zero,bit_one,edge,choose_at,digit_at,side_at,port_at,center_at,g_at,
      Term.eval_literal,touch_at P S m mounted tf]
    cases hit : P.touch e with
    | none => simp [hit,touchValue,pick,ptr_zero,ptr_center,one_ne two] <;> ring
    | some t =>
      have differs : (t.val : Word w) ≠ ((n+1 : ℕ) : Word w) :=
        fun eq => Nat.ne_of_lt t.isLt ((same _ _ (t.isLt.trans gf) gf).1 eq)
      simp only [touchValue,hit,Option.elim,ite_eq_right differs]
      simp [pick,ptr_port,ptr_center,one_ne two]; ring

/-- Decode every labeled row against the physical track, touched center, and exterior pin. -/
theorem body_at (part : Part) (S : Banks) (m : Memory w) (mounted : Mounted P S m)
    (tf : S.touch+r ≤ 2^w) (mf : S.mark+r*(n+1) ≤ 2^w) (gf : n+1 < 2^w) (two : 2 < 2^w)
    (e : Fin r) (j : Fin (middle part n)) (z : Fin 2) :
    (body part).eval (words S r n) m (setting e.val j.val z.val) =
      (ptr (pick z (edge P (marks P) (label e part j))) : Word w) := by
  cases part with
  | focus => exact focus_at P S m two e j z
  | neighbor => exact neighbor_at P S m two e j z
  | through => exact through_at P S m mounted tf mf gf two e j z
  | center => exact center_at_edge P S m mounted tf gf two e j z

def block (part : Part) (S : Banks) (r n w : ℕ) :=
  GridTopologyRAM.scan (body (w:=w) part) (words S r n) (S.output+2*offset part r n)
    r (middle part n) 2

/-- All phases use this one common address space. Outside the emitted bank its
value is immaterial. -/
noncomputable def word (S : Banks) (a : ℕ) : Word w :=
  let off := a-S.output
  if h : off/2 < (wiring P).equal.length then
    (ptr (pick (⟨off%2,Nat.mod_lt _ (by decide)⟩ : Fin 2) ((wiring P).equal.get ⟨_,h⟩)):Word w)
  else 0

theorem word_at (S : Banks) (i : Fin (wiring P).equal.length) (z : Fin 2) :
    word P S (S.output+i.val*2+z.val) =
      (ptr (pick z ((wiring P).equal.get i)):Word w) := by
  have d : (i.val*2+z.val)/2=i.val := by
    rw [Nat.mul_comm i.val 2,Nat.mul_add_div (by decide : 0 < 2),Nat.div_eq_of_lt z.isLt,Nat.add_zero]
  have live : i.val<edgeCount r n := by simpa only [wiring_count] using i.isLt
  simp [word,show S.output+i.val*2+z.val-S.output=i.val*2+z.val by omega,
    Nat.mod_eq_of_lt z.isLt,d,live]

private theorem word_label (S : Banks) (part : Part) (e : Fin r) (j : Fin (middle part n)) (z : Fin 2) :
    word P S (index (S.output+2*offset part r n) (middle part n) 2 e.val j.val z.val) =
      (ptr (pick z (edge P (marks P) (label e part j))):Word w) := by
  let i : Fin (wiring P).equal.length := (candidateCode (label e part j)).cast (wiring_count P).symm
  have ix : i.val=offset part r n+e.val*middle part n+j.val := label_number e part j
  rw [show index (S.output+2*offset part r n) (middle part n) 2 e.val j.val z.val =
    S.output+i.val*2+z.val by rw [index,ix]; ring,word_at]
  congr 2
  simp [i,wiring,emit]
  change pick z (edge P (marks P) (candidateCode.symm (candidateCode (label e part j))))=_
  rw [Equiv.symm_apply_apply]

theorem block_spec (S : Banks) (part : Part)
    (fit : S.output+2*offset part r n+r*middle part n*2 < 2^w)
    (away : S.output+2*offset part r n+r*middle part n*2 ≤ S.touch ∧
      S.output+2*offset part r n+r*middle part n*2 ≤ S.mark)
    (mf : S.mark+r*(n+1) ≤ 2^w) (tf : S.touch+r ≤ 2^w)
    (gf : n+1 < 2^w) (two : 2 < 2^w) :
    (block part S r n w).Spec (Mounted P S)
      (fun m o => o=fillSegment (S.output+2*offset part r n) (r*middle part n*2) (word P S) m)
      (4+r*middle part n*2*(2*((body (w:=w) part).binds+16)+4)) := by
  apply GridTopologyRAM.scan_spec _ _ _ _ _ _ fit (by cases part <;> simp [middle] <;> omega) two
  intro init yes m frame e j z
  have now : Mounted P S m := by
    constructor
    · intro u; exact (frame _ (.inr (by omega))).trans (yes.longitudinal _)
    · intro u t; exact (frame _ (.inr (by omega))).trans (yes.selected _ _)
  exact (body_at P part S m now tf mf gf two e j z).trans (word_label P S part e j z).symm

def build (S : Banks) (r n w : ℕ) :=
  (block .focus S r n w).seq ((block .neighbor S r n w).seq
    ((block .through S r n w).seq (block .center S r n w)))

theorem bind_bound (part : Part) : (body (w:=w) part).binds ≤ 160 := by
  cases part <;> simp [body,hbase,g,touch,marked,portPtr,extPtr,centerPtr,rail,digit,side,
    plus,times,choose,lit,Term.binary,Term.select,Term.load,Term.parameter,Term.literal,Term.binds]

/-- All four spans tile the single guarded-edge bank. -/
private theorem adjacent {W : ℕ} (a d e : ℕ) (f : ℕ → Word W) (m : Memory W) :
    fillSegment (a+d) e f (fillSegment a d f m) = fillSegment a (d+e) f m := by
  funext i
  simp only [fillSegment]
  split_ifs <;> first | rfl | omega

def totalWords (r n : ℕ) := 2*edgeCount r n

private noncomputable def sweep (part : Part) (S : Banks) (m : Memory w) : Memory w :=
  fillSegment (S.output+2*offset part r n) (r*middle part n*2) (word P S) m

private def cost (part : Part) (r n w : ℕ) :=
  4+r*middle part n*2*(2*((body (w:=w) part).binds+16)+4)

theorem build_exec (S : Banks) (m : Memory w) (mounted : Mounted P S m)
    (outFit : S.output+totalWords r n < 2^w)
    (away : S.output+totalWords r n ≤ S.touch ∧ S.output+totalWords r n ≤ S.mark)
    (mf : S.mark+r*(n+1) ≤ 2^w) (tf : S.touch+r ≤ 2^w) (gf : n+1 < 2^w) (two : 2 < 2^w) :
    (build S r n w).Exec m (fillSegment S.output (totalWords r n) (word P S) m)
      (16+356*totalWords r n) := by
  have covers (part : Part) : S.output+2*offset part r n+r*middle part n*2 ≤ S.output+totalWords r n := by
    cases part <;> simp [totalWords,edgeCount,offset,middle] <;> omega
  have step (part : Part) (input : Memory w) (loaded : Mounted P S input) :
      (block part S r n w).Exec input (sweep P part S input) (cost part r n w) :=
    Procedure.Spec.exec (block_spec P S part ((covers part).trans_lt outFit)
      ⟨(covers part).trans away.1,(covers part).trans away.2⟩ mf tf gf two) input loaded
  have keep (part : Part) (input : Memory w) (loaded : Mounted P S input) :
      Mounted P S (sweep P part S input) := by
    have frame (a : ℕ) (valid : S.output+totalWords r n ≤ a) : sweep P part S input a=input a := by
      unfold sweep fillSegment
      exact ite_eq_right (by have h := covers part; omega)
    constructor
    · intro e; exact (frame _ (by have := away.1; omega)).trans (loaded.longitudinal e)
    · intro e t; exact (frame _ (by have := away.2; omega)).trans (loaded.selected e t)
  let a := sweep P .focus S m
  let b := sweep P .neighbor S a
  let c := sweep P .through S b
  have ma := keep .focus m mounted
  have mb := keep .neighbor a ma
  have mc := keep .through b mb
  have runs : Procedure.Exec _ _ _ _ := Procedure.Exec.then (step .focus m mounted) (Procedure.Exec.then (step .neighbor a ma)
    (Procedure.Exec.then (step .through b mb) (step .center c mc)))
  have expected : sweep P .center S c=fillSegment S.output (totalWords r n) (word P S) m := by
    let f := word (w:=w) P S
    let a0 := r*2*2
    let a1 := r*n*2
    let a2 := r*(n+1)*2
    change fillSegment (S.output+2*(r*2+r*n+r*(n+1))) (r*2*2) f
      (fillSegment (S.output+2*(r*2+r*n)) a2 f
        (fillSegment (S.output+2*(r*2)) a1 f (fillSegment (S.output+2*0) a0 f m))) = _
    rw [show S.output+2*(r*2+r*n+r*(n+1))=S.output+a0+a1+a2 by dsimp [a0,a1,a2]; ring,
      show S.output+2*(r*2+r*n)=S.output+a0+a1 by dsimp [a0,a1]; ring,
      show S.output+2*(r*2)=S.output+a0 by dsimp [a0]; ring,
      Nat.mul_zero,Nat.add_zero,adjacent,adjacent,adjacent]
    congr 1
    simp [totalWords,edgeCount,a0,a1,a2]
    ring
  change (build S r n w).Exec m (sweep P .center S c)
    (cost .focus r n w+(cost .neighbor r n w+(cost .through r n w+cost .center r n w))) at runs
  rw [expected] at runs
  suffices late : cost .focus r n w+(cost .neighbor r n w+(cost .through r n w+cost .center r n w))≤
      16+356*totalWords r n by
    intro P' R' K' machine pc reg pub exit installed values cfg raw entry eqn
    obtain ⟨t,ht,cf,mm,run,stop,final⟩ := runs machine pc reg pub exit installed values cfg raw entry eqn
    exact ⟨t,ht.trans late,cf,mm,run,stop,final⟩
  have hi (p : Part) : cost p r n w ≤ 4+r*middle p n*2*356 := by
    have a := bind_bound (w:=w) p
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) 4
  calc
    _ ≤ _ := Nat.add_le_add (hi .focus) (Nat.add_le_add (hi .neighbor) (Nat.add_le_add (hi .through) (hi .center)))
    _ = _ := by simp [middle,totalWords,edgeCount]; ring

theorem emitted_at (S : Banks) (m : Memory w) (i : Fin (wiring P).equal.length) (z : Fin 2) :
    fillSegment S.output (totalWords r n) (word P S) m (S.output+2*i.val+z.val) =
      (ptr (pick z ((wiring P).equal.get i)):Word w) := by
  have le : i.val < edgeCount r n := by simpa using i.isLt
  have lt := z.isLt
  have pos : S.output+2*i.val+z.val < S.output+totalWords r n := by dsimp [totalWords]; omega
  rw [fillSegment,ite_eq_left ⟨by omega,pos⟩,Nat.mul_comm 2 i.val,word_at]

end Hierarchy.GridOrderedEdgeRAM

end OAI
