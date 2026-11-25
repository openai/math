import OAI.ThreeFlat.RAM.HistoryGatherBody

namespace OAI
/-! # Ordered physical joins over the selected parties and motifs of a site -/

namespace ThreeFlat.RAM.HistoryMotifJoin

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalProcedure HistoryGatherBody
open scoped Fin.CommRing

noncomputable section
variable {W : ℕ}
private abbrev T (W : ℕ) := Term W 0 1
private def l (x : ℕ) : T W := .literal (x : Word W)
private def a (x y : T W) : T W := .binary .add x y
private def times (x y : T W) : T W := .binary .mul x y
private def rd (x : T W) (j : ℕ) := (a x (l j)).load
private def cut (x y : T W) : T W := .select .lt x y (l 0) (.binary .sub x y)
def select (key : T W) : ℕ → List (T W) → T W
  | _,[] => l 0
  | j,x::xs => .select .eq key (l j) x (select key (j+1) xs)

variable (A : HistoryGatherBody.Layout)
private def id_ : T W := HeaderScan.closed (HistoryNodePorts.id A.nodePorts)
private def kr : T W := HeaderScan.closed (HistoryNodePorts.kernel A.nodePorts)
private def inc : T W := a (rd (kr A) 4) (l (6*A.party.motif))
private def live (x : T W) : T W := .select .lt (l A.party.motif) (rd (kr A) 3) x (l 0)
private def test (mask : T W) (j : ℕ) : T W := .binary .mod (.binary .div mask (l (2^j))) (l 2)

private def total (f : ℕ→T W) : ℕ → T W
  | 0 => l 0
  | k+1 => a (total f k) (f k)

private def bit (j : ℕ) : T W := test (live A (rd (inc A) 5)) j

private def partyOrdinal (slot : ℕ) : T W :=
  ((List.range A.party.parties).reverse).foldl
    (fun fallback j => .select .eq (bit A j) (l 1)
      (.select .eq (total (bit A) j) (l slot) (l j) fallback) fallback) (l 0)

private def srcWidth (j : ℕ) : T W := match A.mode with
  | .refresh .. => l 0
  | .shrink _ =>
    let stage := (kr A).load
    let hist := .binary .div (cut (rd (inc A) 1) (rd stage 1)) (l A.histogramStride)
    live A ((a (rd stage 3) (a (times (l 8) hist) (l j))).load)

private def absorbed (j : ℕ) : T W :=
  .select .eq (test (live A (rd (inc A) 4)) j) (l 1) (srcWidth A j) (l 0)

/-- Private edge prefixes are in ascending raw Fin 8 order, including the
empty holes. Their total is the exact shared hidden count of the occupied
motif join. At a refresh node all its real factors have zero absorbed edges. -/
def privateHeader (W : ℕ) : T W :=
  let key := cut (.result 0) (l A.privateStarts)
  let values := (List.range 9).map (total (absorbed A))
  select key 0 values

private theorem total_eval_zero (f : ℕ → T W) (m : Memory W) (vs : Fin 1 → Word W)
    (zero : ∀ j, (f j).eval Fin.elim0 m vs = 0) (n : ℕ) :
    (total f n).eval Fin.elim0 m vs = 0 := by
  induction n with
  | zero => simp only [total, l, Term.eval_literal, Nat.cast_zero]
  | succ n ih =>
    simp only [total, a, Term.eval_binary, PrivateRAM.BinaryOp.eval, ih, zero, add_zero]

private theorem select_zero_prefixes (f : ℕ → T W) (m : Memory W) (vs : Fin 1 → Word W)
    (zero : ∀ j, (f j).eval Fin.elim0 m vs = 0) (key : T W) (idx : ℕ) (ns : List ℕ) :
    (select key idx (ns.map (total f))).eval Fin.elim0 m vs = 0 := by
  induction ns generalizing idx with
  | nil => simp only [List.map_nil, select, l, Term.eval_literal, Nat.cast_zero]
  | cons n ns ih =>
    simp only [List.map_cons, select, Term.eval_select, total_eval_zero f m vs zero n,
      ih (idx + 1), ite_self]

/-- Every issued private-edge prefix is zero for a refresh, including the ninth word. -/
theorem privateHeader_refresh_zero {p h pad : ℕ} (mode : A.mode=.refresh p h pad)
    (m : Memory W) (addr : Word W) :
    (privateHeader A W).eval Fin.elim0 m (fun _=>addr)=0 := by
  have empty (j : ℕ) : (absorbed (W := W) A j).eval Fin.elim0 m (fun _ => addr) = 0 := by
    simp only [absorbed, srcWidth, mode, l, Term.eval_select, Term.eval_literal, ite_self, Nat.cast_zero]
  exact select_zero_prefixes (absorbed A) m (fun _ => addr) empty
    (cut (.result 0) (l A.privateStarts)) 0 (List.range 9)

def privateRows (W : ℕ) : Procedure W :=
  PhysicalInputPhases.writing (privateHeader A W) Fin.elim0 A.privateStarts 9

private def bank (motif party family b : T W) := a (l A.party.arena) (times
  (a (times (id_ A) (l A.party.V))
     (a (times (a (times (a (times motif (l (A.party.parties+2))) party) (l 8)) family) (l 32)) b))
  (l A.party.V))

private def motifBank (j : T W) (b : ℕ) := bank A (a j (l 2)) (l 0) (l 3) (l b)
private def rootBank (b : ℕ) : T W := bank A (l 0) (l 0) (l 4) (l b)

private def portCount : T W :=
  let c := HeaderScan.closed (HistoryNodePorts.childCount A.nodePorts)
  a (a (l A.nodePorts.starts) c).load (HeaderScan.closed (HistoryNodePorts.fresh A.nodePorts))

private def rootData (group : Bool) (slot : ℕ) (bankIndex : ℕ) : T W :=
  if group then
    bank A (l (A.party.motif+2)) (a (partyOrdinal A slot) (l 2)) (l 2) (l bankIndex)
  else motifBank A (l slot) bankIndex

/-- In a motif join the pin map was computed by reading actual geometric
addresses; its map step copies that per-party cache. A global site kernel
uses an identity public pin map at each of its occupied motif factors. -/
def rows (W : ℕ) (group : Bool) : List (T W) :=
  let cap := if group then A.party.parties else A.party.motifs
  let count := if group then total (bit A) A.party.parties else rd (kr A) 3
  let shared := if group then (l (A.privateStarts+8)).load else l 0
  let out (b : ℕ) := if group then motifBank A (l A.party.motif) b else rootBank A b
  let h := A.party.seed+64
  let children := h+7
  let args := children+4*cap
  let link (j : ℕ) := [rootData A group j 1,rootData A group j 3,l (if group then 10 else 11),l (args+3*j)]
  let operand (j : ℕ) := [rootData A group j 3,rd (rootData A group j 1) 1,
    if group then rootData A group j 2 else l 2]
  [out 0,portCount A,shared,count,l children,l A.party.arguments,out 1] ++
    (List.range cap).flatMap link ++ (List.range cap).flatMap operand

def joinHeader (W : ℕ) (group : Bool) : T W :=
  select (cut (.result 0) (l (A.party.seed+64))) 0 (rows A W group)

def join (W : ℕ) (group : Bool) : Procedure W :=
  let table := rows A W group
  let h := A.party.seed+64
  let init := PhysicalInputPhases.writing (joinHeader A W group) Fin.elim0 h table.length
  let cap := if group then A.party.parties else A.party.motifs
  init.seq (HistoryBoundedBody.procedure W ⟨h,A.party.seed,A.party.commands⟩ cap)


open private select_binds binary_binds load_binds from
  OAI.ThreeFlat.RAM.HistoryGatherBody

private theorem lit_cost (n : ℕ) : (l (W:=W) n).binds = 1 := rfl

private theorem cursor_cost : (Term.result 0 : T W).binds = 0 := rfl

private theorem kernel_field_cost (P : HistoryNodePorts.Layout) : (HistoryNodePorts.kernel P).work = 16 := rfl
private theorem id_field_cost (P : HistoryNodePorts.Layout) : (HistoryNodePorts.id P).work = 9 := rfl
private theorem count_field_cost (P : HistoryNodePorts.Layout) : (HistoryNodePorts.childCount P).work = 16 := rfl
set_option maxRecDepth 10000 in
private theorem fresh_field_cost (P : HistoryNodePorts.Layout) : (HistoryNodePorts.fresh P).work = 149 := rfl

local macro "motif_cost" : tactic => `(tactic|
  simp (config := {failIfUnchanged := false}) only [portCount, rootBank, motifBank, bank, test, live,
    inc, kr, id_, rd, a, times, cut, select_binds, binary_binds, load_binds, lit_cost, cursor_cost,
    HeaderScan.binds_closed, kernel_field_cost, id_field_cost, count_field_cost, fresh_field_cost])

private theorem bit_cost_fixed {U : ℕ} (B : HistoryGatherBody.Layout) (i j : ℕ) :
    (bit (W:=W) A i).binds = (bit (W:=U) B j).binds := by
  unfold bit
  motif_cost

private theorem index_cost {U : ℕ} (i j : ℕ) :
    (cut (Term.result 0) (l i) : T W).binds = (cut (Term.result 0) (l j) : T U).binds := by
  motif_cost

private theorem select_size {U : ℕ} (x : T W) (y : T U) (i j : ℕ) (xs : List (T W)) (ys : List (T U))
    (h : x.binds=y.binds) (rows : xs.map Term.binds=ys.map Term.binds) :
    (select x i xs).binds=(select y j ys).binds := by
  induction xs generalizing i j ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b ys => simp at rows
  | cons a xs ih =>
    cases ys with
    | nil => simp at rows
    | cons b ys =>
      simp only [List.map_cons,List.cons.injEq] at rows
      simp only [select, select_binds, lit_cost, h, rows.1, ih (i+1) (j+1) ys rows.2]

private theorem total_size {U : ℕ} (f : ℕ→T W) (g : ℕ→T U) (same : ∀j,(f j).binds=(g j).binds)
    (n : ℕ) : (total f n).binds=(total g n).binds := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [total,a,Term.binary,Term.binds_letThen,Term.binds_rename,same,ih]
    all_goals rfl

private theorem ordinal_size {U : ℕ} (B : HistoryGatherBody.Layout) (h : A.party.parties=B.party.parties)
    (i j : ℕ) : (partyOrdinal (W:=W) A i).binds=(partyOrdinal (W:=U) B j).binds := by
  let step {v : ℕ} (P : HistoryGatherBody.Layout) (slot : ℕ) (prev : T v) (k : ℕ) :=
    Term.select .eq (bit P k) (l 1) (.select .eq (total (bit P) k) (l slot) (l k) prev) prev
  change (((List.range A.party.parties).reverse).foldl (step A i) (l 0 : T W)).binds=
    (((List.range B.party.parties).reverse).foldl (step B j) (l 0 : T U)).binds
  rw [h]
  generalize (List.range B.party.parties).reverse=xs
  suffices go : ∀ (a : T W) (b : T U),a.binds=b.binds →
      (xs.foldl (step A i) a).binds=(xs.foldl (step B j) b).binds by exact go _ _ rfl
  induction xs with
  | nil => exact fun _ _ eq=>eq
  | cons k xs ih =>
    intro x y eq
    apply ih
    have same (n : ℕ) : (bit (W:=W) A n).binds = (bit (W:=U) B n).binds :=
      bit_cost_fixed (W:=W) (U:=U) A B n n
    have sumCost := total_size (W:=W) (U:=U) (bit A) (bit B) same k
    simp only [step, select_binds, lit_cost, same k, sumCost, eq]

set_option maxRecDepth 10000 in
theorem privateHeader_work {U : ℕ} (B : HistoryGatherBody.Layout) (h : A.mode=B.mode) :
    (privateHeader A W).binds=(privateHeader B U).binds := by
  have bitPrice (i : ℕ) : (absorbed (W:=W) A i).binds = (absorbed (W:=U) B i).binds := by
    cases hA : A.mode <;> have hB := h.symm.trans hA <;>
      simp only [absorbed, srcWidth, hA, hB] <;> motif_cost
  have same : ((List.range 9).map (total (absorbed (W:=W) A))).map Term.binds =
      ((List.range 9).map (total (absorbed (W:=U) B))).map Term.binds := by
    simp only [List.map_map, Function.comp_def]
    exact congrArg (fun f : ℕ → ℕ => (List.range 9).map f)
      (funext (total_size (W:=W) (U:=U) (absorbed A) (absorbed B) bitPrice))
  exact select_size (W:=W) (U:=U) (cut (.result 0) (l A.privateStarts)) (cut (.result 0) (l B.privateStarts))
    0 0 ((List.range 9).map (total (absorbed A))) ((List.range 9).map (total (absorbed B)))
    (index_cost (W:=W) (U:=U) A.privateStarts B.privateStarts) same

set_option maxHeartbeats 1000000 in
theorem joinHeader_work {U : ℕ} (B : HistoryGatherBody.Layout) (g : Bool)
    (hp : A.party.parties=B.party.parties) (hm : A.party.motifs=B.party.motifs) :
    (joinHeader A W g).binds=(joinHeader B U g).binds := by
  have bits (j : ℕ) : (bit (W:=W) A j).binds = (bit (W:=U) B j).binds :=
    bit_cost_fixed A B j j
  have totals (n : ℕ) := total_size (W:=W) (U:=U) (bit A) (bit B) bits n
  have ordinals (j : ℕ) := ordinal_size (W:=W) (U:=U) A B hp j j
  have costs : (rows A W g).map Term.binds = (rows B U g).map Term.binds := by
    cases g <;> simp only [rows, rootData, Bool.false_eq_true, ite_false, ite_true,
      List.map_flatMap, List.map_append, List.map_nil, List.map_cons, hp, hm]
    all_goals motif_cost
    all_goals simp only [ordinals, totals]
  exact select_size (W:=W) (U:=U)
    (cut (.result 0) (l (A.party.seed+64))) (cut (.result 0) (l (B.party.seed+64)))
    0 0 (rows A W g) (rows B U g)
    (index_cost (W:=W) (U:=U) (A.party.seed+64) (B.party.seed+64)) costs

def withParty (j : ℕ) : HistoryGatherBody.Layout := {A with party := {A.party with party := j}}
def withMotif (j : ℕ) : HistoryGatherBody.Layout := {A with party := {A.party with motif := j}}

/-- One selected occupied motif, with the six/elected parties enumerated
in increasing raw party-bit order. All local source apertures are reused. -/
def motif (W : ℕ) : Procedure W :=
  let each («prefix» : Procedure W) (j : ℕ) :=
    let B := withParty A j
    («prefix».seq (HistoryPartyPair.procedure W B.party)).seq (HistoryGatherBody.procedure W B)
  let all := (List.range A.party.parties).foldl each (privateRows A W)
  all.seq (join A W true)

/-- The physical kernel result is stored at the site root for a shrink and
at its single direct party join for a refresh. The two representations match
the differing tree definitions in ShrinkSiteTree and RefreshSiteTree. -/
def kernelProcedure (W oldCap : ℕ) : Procedure W :=
  let «prefix» := HistoryNodePorts.phase W A.nodePorts oldCap
  match A.mode with
  | .shrink _ =>
    let many := (List.range A.party.motifs).foldl
      (fun prev j => prev.seq (motif (withMotif A j) W)) «prefix»
    many.seq (join A W false)
  | .refresh .. => «prefix».seq (motif (withMotif A 0) W)

section Execution
open Computability.VPVNP.BurstRAM.PrivateRAM PhysicalPinsExpr BitNetwork.Ordered HistoryBoundedBody HistoryPartyBatchExec HistoryJoinScan BitLayout

open scoped BigOperators Classical

namespace Roles
variable {P : ℕ} (active : Fin P→Prop)

def rank (k : ℕ) := (Finset.univ.filter (fun j : Fin P=>active j ∧ j.val<k)).card

theorem rank_zero : rank active 0=0 := by simp [rank]

theorem rank_next (k : Fin P) : rank active (k.val+1)=rank active k.val+(if active k then 1 else 0) := by
  classical
  by_cases live : active k
  · have step : Finset.univ.filter (fun j : Fin P=>active j ∧ j.val<k.val+1)=
        insert k (Finset.univ.filter (fun j : Fin P=>active j ∧ j.val<k.val)) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · rintro ⟨ha,hk⟩
        by_cases e : j.val=k.val
        · exact Or.inl (Fin.ext e)
        · exact Or.inr ⟨ha,by omega⟩
      · rintro (rfl|⟨ha,hk⟩)
        · exact ⟨live,by omega⟩
        · exact ⟨ha,by omega⟩
    have fresh : k ∉ Finset.univ.filter (fun j : Fin P => active j ∧ j.val < k.val) := by simp
    unfold rank
    rw [step, Finset.card_insert_of_notMem fresh, ite_eq_left live]
  · have step : Finset.univ.filter (fun j : Fin P=>active j ∧ j.val<k.val+1)=
        Finset.univ.filter (fun j : Fin P=>active j ∧ j.val<k.val) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      apply and_congr_right
      intro ha
      have e : j.val≠k.val := by intro h;exact live ((Fin.ext h) ▸ ha)
      omega
    unfold rank
    rw [step, ite_eq_right live, Nat.add_zero]

theorem rank_le (k : ℕ) (hk : k≤P) : rank active k≤k := by
  induction k with
  | zero=>simp [rank_zero]
  | succ k ih=>
    have eqn := rank_next active ⟨k,by omega⟩
    have bound := ih (by omega)
    dsimp only at eqn
    split_ifs at eqn <;> omega

theorem rank_full : rank active P=Fintype.card {i // active i} := by
  classical
  let mask := Finset.univ.filter active
  have eqn : Finset.univ.filter (fun i : Fin P=>active i ∧ i.val<P)=mask := by ext i;simp [mask]
  rw [rank,eqn]
  let e : {i // i∈mask}≃{i // active i} :=
    ⟨fun i=>⟨i.val,(Finset.mem_filter.mp i.property).2⟩,fun i=>⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩⟩,
      fun _=>rfl,fun _=>rfl⟩
  simpa using Fintype.card_congr e

theorem rank_key (i : Fin (Fintype.card {i // active i})) :
    rank active (Diagonal.HistoryMaskOrder.order active i).val.val=i.val :=
  Diagonal.HistoryMaskOrder.ordinal active i

end Roles

def selectedBit (mem : Memory W) (j : ℕ) : Prop :=
  let I := HistoryGatherBody.selected A mem
  (A.party.motif:Word W)<HistoryGatherBody.wordAt mem I.kernel 3 ∧
    (HistoryGatherBody.wordAt mem I.incident 5).val.testBit j=true

private theorem bit_value (mem : Memory W) (p : Word W) (j : ℕ)
    (mask : 2^j<2^W) (two : 2<2^W) :
    (bit A j).eval Fin.elim0 mem (fun _=>p)=((if selectedBit A mem j then 1 else 0 : ℕ):Word W) := by
  classical
  let R := HistoryGatherBody.selected A mem
  have kernel : (kr A : T W).eval Fin.elim0 mem (fun _=>p)=R.kernel := by
    rw [kr,HeaderScan.eval_closed]
    rfl
  have incident : (inc A : T W).eval Fin.elim0 mem (fun _=>p)=R.incident := by
    simp [inc,rd,a,l,Term.eval_binary,Term.eval_load,Term.eval_literal,kernel,
      R,HistoryGatherBody.selected,HistoryGatherBody.wordAt,BinaryOp.eval]
  let u := HistoryGatherBody.wordAt mem R.incident 5
  have q : u.val/2^j<2^W := (Nat.div_le_self ..).trans_lt u.isLt
  have dd := WordQuotients.div_at u.val (2^j) u.isLt mask
  have mm := WordQuotients.mod_at (u.val/2^j) 2 q two
  simp only [Fin.cast_val_eq_self] at dd
  dsimp only [bit,test,live]
  have addWord (x y : Word W) : BinaryOp.eval .add x y=x+y := rfl
  simp only [rd,a,l,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval_load,kernel,incident,
    addWord,Comparison.test,decide_eq_true_eq,Nat.cast_zero]
  change BinaryOp.eval .mod (BinaryOp.eval .div
    (if (A.party.motif:Word W)<HistoryGatherBody.wordAt mem R.kernel 3 then u else 0)
    ((2^j:ℕ):Word W)) ((2:ℕ):Word W)=_
  have flag : selectedBit A mem j ↔
      (A.party.motif:Word W)<HistoryGatherBody.wordAt mem R.kernel 3 ∧ u.val.testBit j=true := Iff.rfl
  by_cases yes : (A.party.motif:Word W)<HistoryGatherBody.wordAt mem R.kernel 3
  · rw [ite_eq_left yes,dd,mm]
    have split := Nat.mod_two_eq_zero_or_one (u.val/2^j)
    rcases split with h|h <;> simp [flag,yes,Nat.testBit_eq_decide_div_mod_eq,h]
  · simp [flag,yes,BinaryOp.eval]

theorem total_bits (m : Memory W) (p : Word W) (small : 2^A.party.parties<2^W) (two : 2<2^W)
    (k : ℕ) (bound : k≤A.party.parties) :
    (total (bit A) k).eval Fin.elim0 m (fun _=>p)=(Roles.rank
      (fun i : Fin A.party.parties=>selectedBit A m i.val) k:Word W) := by
  classical
  induction k with
  | zero=>simp [total,l,Roles.rank_zero,Term.eval_literal]
  | succ k ih=>
    have eqn := Roles.rank_next (fun i : Fin A.party.parties=>selectedBit A m i.val) ⟨k,by omega⟩
    dsimp only at eqn
    rw [total,a,Term.eval_binary,ih (by omega),bit_value A m p k (lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega)) small) two,eqn,Nat.cast_add]
    rfl

theorem occupied_count (m : Memory W) (p : Word W) (small : 2^A.party.parties<2^W) (two : 2<2^W) :
    (total (bit A) A.party.parties).eval Fin.elim0 m (fun _=>p)=
      (Fintype.card {i : Fin A.party.parties // selectedBit A m i.val}:Word W) := by
  rw [total_bits A m p small two _ le_rfl,Roles.rank_full]

theorem occupied_ordinal (m : Memory W) (p : Word W) (small : 2^A.party.parties<2^W) (two : 2<2^W)
    (i : Fin (Fintype.card {j : Fin A.party.parties // selectedBit A m j.val})) :
    (partyOrdinal A i.val).eval Fin.elim0 m (fun _=>p)=
      ((Diagonal.HistoryMaskOrder.order (fun j : Fin A.party.parties=>selectedBit A m j.val) i).val.val:Word W) := by
  classical
  let P := A.party.parties
  let act (j : Fin P) := selectedBit A m j.val
  let e := Diagonal.HistoryMaskOrder.order act
  let target := (e i).val
  have Pfit : P<2^W := (Nat.lt_two_pow_self (n:=P)).trans small
  have key := Roles.rank_key act i
  have good := (e i).property
  have ir : i.val<2^W := by have v:=Roles.rank_le act target.val target.isLt.le;change Roles.rank act target.val=i.val at key;omega
  let step (prev : T W) (j : ℕ) := Term.select .eq (bit A j) (l 1)
    (.select .eq (total (bit A) j) (l i.val) (l j) prev) prev
  have exactStep (prev : T W) (j : ℕ) (hj : j<P) :
    (step prev j).eval Fin.elim0 m (fun _=>p)=
      if j=target.val then (target.val:Word W) else prev.eval Fin.elim0 m (fun _=>p) := by
    dsimp only [step]
    rw [Term.eval_select,Term.eval_select,bit_value A m p j (lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) hj.le) small) two,
      total_bits A m p small two j hj.le]
    simp only [l,Term.eval_literal,Nat.cast_one]
    change (if Comparison.test .eq ((if act ⟨j,hj⟩ then 1 else 0:ℕ):Word W) 1 then
      if Comparison.test .eq ((Roles.rank act j:ℕ):Word W) (i.val:Word W) then (j:Word W) else _ else _)=_
    have rfit : Roles.rank act j<2^W := (Roles.rank_le act j hj.le).trans_lt (hj.trans Pfit)
    have valEq : ((Roles.rank act j:ℕ):Word W)=(i.val:Word W) ↔ Roles.rank act j=i.val := by
      constructor
      · intro h;have he:=congrArg Fin.val h;simpa [Fin.val_cast_of_lt rfit,Fin.val_cast_of_lt ir] using he
      · rintro h;rw [h]
    by_cases yes : act ⟨j,hj⟩
    · have which : Roles.rank act j=i.val ↔ j=target.val := by
        let k := e.symm ⟨⟨j,hj⟩,yes⟩
        have atK := Roles.rank_key act k
        have loc : (e k).val.val=j := congrArg (fun u=>u.val.val) (e.apply_symm_apply _)
        change Roles.rank act (e k).val.val=k.val at atK
        rw [loc] at atK
        constructor
        · intro h
          have eqK : k=i := Fin.ext (atK.symm.trans h)
          simpa [eqK,target] using loc.symm
        · intro h;rw [h];exact key
      simp [yes,Comparison.test,valEq,which]
      split <;> rename_i h <;> simp_all
    · have ne : j≠target.val := by
        intro h
        have eqIndex : (⟨j,hj⟩ : Fin P) = target := Fin.ext h
        exact yes (eqIndex.symm ▸ (show act target from good))
      have nz : (0:Word W)≠1 := by
        intro h
        have hv:=congrArg Fin.val h
        change 0=1%2^W at hv
        rw [Nat.mod_eq_of_lt (by omega : 1<2^W)] at hv
        omega
      simp [yes,Comparison.test,nz,ne]
  have fold (xs : List ℕ) (prev : T W) (ok : ∀ j∈xs,j<P) :
    (xs.foldl step prev).eval Fin.elim0 m (fun _=>p)=
      if target.val∈xs then (target.val:Word W) else prev.eval Fin.elim0 m (fun _=>p) := by
    induction xs generalizing prev with
    | nil=>simp
    | cons j js ih=>
      rw [List.foldl_cons,ih _ (fun a h=>ok _ (List.mem_cons_of_mem _ h)),exactStep prev j (ok _ (by simp))]
      by_cases h:j=target.val <;> simp [h,eq_comm]
  have result:=fold (List.range P).reverse (l 0) (by simp)
  simpa [partyOrdinal,step,P,target,e,act] using result

/-- Exact output of the static header writer on the current native memory. -/
def headerImage (term : Term W 0 1) (start count : ℕ) (m : Memory W) :=
  fillSegment start count (fun a=>term.eval Fin.elim0 m (fun _=>(a:Word W))) m

theorem write_header (term : Term W 0 1) (start count : ℕ) (m : Memory W)
    (room : start+count<2^W) (safe : Protected term m start count) :
    (PhysicalInputPhases.writing term Fin.elim0 start count).Exec m (headerImage term start count m)
      (4+count*(2*term.binds+4)) := by
  apply fixed_exec _ _ _ _ _ room safe
  intro a _ _
  rw [Fin.cast_val_eq_self]

abbrev childPrefix := HistoryNodePorts.clipped

def childWidth (A : HistoryNodePorts.Layout) (_cap : ℕ) (m : ℕ→ℕ) (j : ℕ) :=
  HistoryNodePorts.sum A m (min (j-A.starts) (m (A.nodes+8*(m A.cursor-1)+4)))

theorem childPrefix_word (A : HistoryNodePorts.Layout) (cap : ℕ) (m : ℕ→ℕ) (j : ℕ)
    (count : m (A.nodes+8*(m A.cursor-1)+4)≤cap) :
    (childPrefix A cap).natural W (fun _=>0) m (fun _=>j)=childWidth A cap m j := HistoryNodePorts.clipped_word A cap W m j count


theorem child_starts (A : HistoryNodePorts.Layout) (cap : ℕ) (m : Memory W)
    (count : numeric m (A.nodes+8*(numeric m A.cursor-1)+4)≤cap)
    (room : A.starts+(cap+1)<2^W)
    (safe : Protected (HeaderScan.closed (childPrefix A cap)) m A.starts (cap+1))
    (fits : ∀ i : Fin (cap+1),(childPrefix A cap).Fits W (fun _=>0) (numeric m) (fun _=>A.starts+i.val)) :
    (HistoryNodePorts.phase W A cap).Exec m
      (fillSegment A.starts (cap+1) (fun j=>(childWidth A cap (numeric m) j:Word W)) m)
      (4+(cap+1)*(2*(HeaderScan.closed (w:=W) (childPrefix A cap)).binds+4)) := by
  apply fixed_exec _ _ _ _ _ room safe
  intro a lo hi
  let i : Fin (cap+1) := ⟨a.val-A.starts,by omega⟩
  have hj : A.starts+i.val=a.val := by dsimp [i];omega
  have ok := fits i
  rw [hj] at ok
  have val := closed_eval (childPrefix A cap) (numeric m) (fun _=>a.val) ok
  simp only [word_numeric,Fin.cast_val_eq_self] at val
  exact val.trans (congrArg Nat.cast (childPrefix_word A cap (numeric m) a.val count))

def groupBuild (group : Bool) (T : HistoryBoundedJoin.Hub) (m : Memory W) : HistoryBoundedBody.Build W :=
  let b := A.party.seed+64
  ⟨⟨b,A.party.seed,A.party.commands⟩,T,if group then A.party.parties else A.party.motifs,
    headerImage (joinHeader A W group) b (rows A W group).length m⟩

theorem select_at (m : Memory W) (p : Word W) (t : T W) (start idx : ℕ) (xs : List (T W))
    (pos : idx<xs.length) (room : start+idx<2^W)
    (key : t.eval Fin.elim0 m (fun _=>p)=((start+idx:ℕ):Word W)) :
    (select t start xs).eval Fin.elim0 m (fun _=>p)=(xs[idx]).eval Fin.elim0 m (fun _=>p) := by
  induction xs generalizing start idx with
  | nil => simp at pos
  | cons a xs ih =>
    rw [select,Term.eval_select,l,Term.eval_literal,key]
    cases idx with
    | zero => simp [Comparison.test]
    | succ idx =>
      have loc : start<2^W := by omega
      have ne : ((start+(idx+1):ℕ):Word W)≠(start:Word W) := by
        intro eq
        have diff := congrArg Fin.val eq
        rw [Fin.val_cast_of_lt room,Fin.val_cast_of_lt loc] at diff
        omega
      simp only [Comparison.test,beq_iff_eq,ite_eq_right ne,List.getElem_cons_succ]
      exact ih (start+1) idx (by simpa using pos) (by omega) (by convert key using 2; omega)

/-- Read one word of the actual bounded gather/identity join control. -/
theorem header_at (g : Bool) (m : Memory W) (j : Fin (rows A W g).length)
    (room : A.party.seed+64+(rows A W g).length<2^W) :
    let base := A.party.seed+64
    let p : Word W := ((base+j.val:ℕ):Word W)
    let T := rows A W g
    headerImage (joinHeader A W g) base T.length m (base+j.val)=(T.get j).eval Fin.elim0 m (fun _=>p) := by
  let b := A.party.seed+64
  let p : Word W := ((b+j.val:ℕ):Word W)
  have jl:=j.isLt
  have fits : b+j.val<2^W := by dsimp [b];omega
  have inside : b≤b+j.val ∧ b+j.val<b+(rows A W g).length := by omega
  change fillSegment b (rows A W g).length _ m (b+j.val)=_
  rw [fillSegment,ite_eq_left inside]
  apply select_at m p _ 0 j.val _ j.isLt (by omega)
  have ptr : p.val=b+j.val := Fin.val_cast_of_lt fits
  have base : (b:Word W).val=b := Fin.val_cast_of_lt (by omega)
  simp only [cut,l,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval,Comparison.test,
    BinaryOp.eval,decide_eq_true_eq,Nat.zero_add]
  change (if p<(b:Word W) then 0 else p-(b:Word W))=(j.val:Word W)
  rw [ite_eq_right (by change ¬p.val<(b:Word W).val;rw [ptr,base];omega)]
  simp [p,Nat.cast_add]

def privateWidth (m : Memory W) (j : ℕ) : Word W :=
  let q:=HistoryGatherBody.selected A m
  let live := (A.party.motif:Word W)<HistoryGatherBody.wordAt m q.kernel 3
  let mask := if live then HistoryGatherBody.wordAt m q.incident 4 else 0
  let use := BinaryOp.eval .mod (BinaryOp.eval .div mask ((2^j:ℕ):Word W)) 2
  let space := m q.kernel.val
  let hist := BinaryOp.eval .div (HistoryGatherBody.cutWord (HistoryGatherBody.wordAt m q.incident 1)
    (HistoryGatherBody.wordAt m space 1)) (A.histogramStride:Word W)
  if use=1 then
    match A.mode with
    | .refresh .. => 0
    | .shrink _ => if live then m (HistoryGatherBody.wordAt m space 3+(8*hist+(j:Word W))).val else 0
  else 0

theorem private_width (m : Memory W) (p : Word W) (j : ℕ) :
    (absorbed A j).eval Fin.elim0 m (fun _=>p)=privateWidth A m j := by
  cases h:A.mode <;>
    simp only [absorbed,srcWidth,privateWidth,h,test,live,rd,inc,kr,a,times,l,cut,
      Term.eval_select,Term.eval_binary,Term.eval_load,Term.eval_literal,HeaderScan.eval_closed,
      Comparison.test,decide_eq_true_eq,beq_iff_eq] <;>
    dsimp only [HistoryGatherBody.selected,HistoryGatherBody.wordAt,HistoryGatherBody.cutWord] <;>
    rfl

theorem private_prefix (m : Memory W) (j : Fin 9) (room : A.privateStarts+9<2^W) :
    headerImage (privateHeader A W) A.privateStarts 9 m (A.privateStarts+j.val)=
      ∑ i∈Finset.range j.val,privateWidth A m i := by
  let dest:=A.privateStarts
  let p : Word W := ((dest+j.val:ℕ):Word W)
  have ij:=j.isLt
  have lead : dest≤dest+j.val ∧ dest+j.val<dest+9 := by omega
  have hp : p.val=dest+j.val := Fin.val_cast_of_lt (by dsimp [dest];omega)
  have hd : (dest:Word W).val=dest := Fin.val_cast_of_lt (by dsimp [dest];omega)
  have key : (cut (.result 0) (l dest)).eval Fin.elim0 m (fun _=>p)=((0+j.val:ℕ):Word W) := by
    simp only [cut,l,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval,Comparison.test,
      BinaryOp.eval,decide_eq_true_eq,Nat.zero_add]
    change (if p<(dest:Word W) then 0 else p-(dest:Word W))=(j.val:Word W)
    rw [ite_eq_right (by change ¬p.val<(dest:Word W).val;rw [hp,hd];omega)]
    simp [p,Nat.cast_add]
  have sum (n : ℕ) : (total (absorbed A) n).eval Fin.elim0 m (fun _=>p)=∑ i∈Finset.range n,privateWidth A m i := by
    induction n with
    | zero=>simp [total,l,Term.eval_literal]
    | succ j ih=>rw [total,a,Term.eval_binary,ih,private_width,Finset.sum_range_succ];rfl
  have body := select_at m p (cut (.result 0) (l dest)) 0 j.val ((List.range 9).map (total (absorbed A)))
    (by simp) (by omega) key
  change fillSegment dest 9 _ m _=_
  rw [fillSegment,ite_eq_left lead]
  exact body.trans (by simpa only [List.getElem_map,List.getElem_range] using sum j.val)

section PrivateSite
variable {geo : Diagonal.CompressorPacking.Native.Graph.Stage}

structure PrivateSite (m : Memory W) (owns : Fin 8→Prop) (issued : Fin 8→ℕ) where
  counts : ℕ
  supply : ℕ
  row : ℕ
  shrink : A.mode=.shrink geo
  occupied : A.party.motif<(HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3).val
  countBase : let r:=HistoryGatherBody.selected A m
    HistoryGatherBody.wordAt m (m r.kernel.val) 1=(counts:Word W)
  rowCount : HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 1=
    ((counts+row*A.histogramStride:ℕ):Word W)
  widthBase : let r:=HistoryGatherBody.selected A m
    HistoryGatherBody.wordAt m (m r.kernel.val) 3=(supply:Word W)
  widthWords : ∀ j:Fin 8,m (supply+(8*row+j.val))=(issued j:Word W)
  absorbed : ∀ j:Fin 8,(HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 4).val.testBit j.val=decide (owns j)
  width : 8≤W
  stridePos : 0<A.histogramStride
  strideRoom : A.histogramStride<2^W
  countsRoom : counts+row*A.histogramStride<2^W
  supplyRoom : supply+8*row+8≤2^W

theorem PrivateSite.field {m : Memory W} {owns : Fin 8→Prop} {issued : Fin 8→ℕ}
    (R : PrivateSite (geo:=geo) A m owns issued) (j : Fin 8) :
    privateWidth A m j.val=((if owns j then issued j else 0:ℕ):Word W) := by
  let q:=HistoryGatherBody.selected A m
  let b:=HistoryGatherBody.wordAt m q.incident 4
  have fitMotif : A.party.motif<2^W := R.occupied.trans (HistoryGatherBody.wordAt m q.kernel 3).isLt
  have live : (A.party.motif:Word W)<HistoryGatherBody.wordAt m q.kernel 3 := by
    change (A.party.motif:Word W).val<_;rw [Fin.val_cast_of_lt fitMotif];exact R.occupied
  have eight := R.width
  have small: 2^j.val<2^W := Nat.pow_lt_pow_right (by decide) (j.isLt.trans_le eight)
  have two : 2<2^W := calc
    2 < 2^8 := by decide
    _ ≤ 2^W := Nat.pow_le_pow_right (by decide) eight
  have quo : b.val/2^j.val<2^W := (Nat.div_le_self ..).trans_lt b.isLt
  have use : BinaryOp.eval .mod (BinaryOp.eval .div b ((2^j.val:ℕ):Word W)) 2=1 ↔ owns j := by
    have h:=R.absorbed j
    change b.val.testBit j.val=decide (owns j) at h
    rw [Nat.testBit_eq_decide_div_mod_eq] at h
    have one : (b.val/2^j.val%2=1) ↔ owns j := by simpa only [decide_eq_decide] using h
    have divWord : BinaryOp.eval .div b ((2^j.val:ℕ):Word W) = ((b.val/2^j.val:ℕ):Word W) := by
      simpa only [Fin.cast_val_eq_self] using WordQuotients.div_at b.val (2^j.val) b.isLt small
    have modWord : BinaryOp.eval .mod ((b.val/2^j.val:ℕ):Word W) 2 = ((b.val/2^j.val%2:ℕ):Word W) := by
      simpa only [Nat.cast_ofNat] using WordQuotients.mod_at (b.val/2^j.val) 2 quo two
    rw [divWord,modWord,←one]
    constructor
    · intro eqn
      have eqv:=congrArg Fin.val eqn
      simpa [Fin.val_cast_of_lt ((Nat.mod_lt _ (by decide : 0<2)).trans two),
        Fin.val_one',Nat.mod_eq_of_lt (by omega:1<2^W)] using eqv
    · intro eqn;rw [eqn];rfl
  have histRoom : R.row*A.histogramStride<2^W := by have:=R.countsRoom;omega
  have cutOK : HistoryGatherBody.cutWord (((R.counts+R.row*A.histogramStride:ℕ):Word W)) (R.counts:Word W)=
      ((R.row*A.histogramStride:ℕ):Word W) := by
    have base : R.counts<2^W := by have:=R.countsRoom;omega
    have h : ¬(((R.counts+R.row*A.histogramStride:ℕ):Word W)<(R.counts:Word W)) := by
      change ¬(_ : Word W).val<(_ : Word W).val;rw [Fin.val_cast_of_lt R.countsRoom,Fin.val_cast_of_lt base];omega
    rw [HistoryGatherBody.cutWord, ite_eq_right h, Nat.cast_add]
    exact add_sub_cancel_left _ _
  have div := WordQuotients.div_at (R.row*A.histogramStride) A.histogramStride histRoom R.strideRoom
  have eqn : (R.row*A.histogramStride)/A.histogramStride=R.row := Nat.mul_div_cancel _ R.stridePos
  rw [eqn] at div
  unfold privateWidth
  change (if BinaryOp.eval .mod (BinaryOp.eval .div (if _ then b else 0) _) _=1 then _ else _)=_
  rw [ite_eq_left live]
  by_cases yes : owns j
  · have selected := use.mpr yes
    simp only [ite_eq_left selected, ite_eq_left yes, R.shrink, R.rowCount,
      R.countBase, R.widthBase, cutOK, div]
    have addr : ((R.supply:Word W)+(8*(R.row:Word W)+(j.val:Word W))).val=R.supply+(8*R.row+j.val) := by
      have fit : R.supply+(8*R.row+j.val)<2^W := by
        have := R.supplyRoom
        have := j.isLt
        omega
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using Fin.val_cast_of_lt fit
    rw [addr,R.widthWords]
    exact ite_eq_left live
  · simp only [ite_eq_right (mt use.mp yes), ite_eq_right yes, Nat.cast_zero]

theorem PrivateSite.prefix {m : Memory W} {owns : Fin 8→Prop} {issued : Fin 8→ℕ}
    (R : PrivateSite (geo:=geo) A m owns issued) (j : Fin 9)
    (room : A.privateStarts+9<2^W) :
    headerImage (privateHeader A W) A.privateStarts 9 m (A.privateStarts+j.val)=
      ((∑ e∈Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<j.val),issued e:ℕ):Word W) := by
  rw [private_prefix A m j room]
  have prefixSum (n : ℕ) (hn : n≤8) :
      (∑ i∈Finset.range n,privateWidth A m i)=
      ((∑ e∈Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<n),issued e:ℕ):Word W) := by
    induction n with
    | zero=>simp
    | succ k ih=>
      let z:Fin 8:=⟨k,by omega⟩
      rw [Finset.sum_range_succ,ih (by omega),show privateWidth A m k=_ from PrivateSite.field A R z]
      by_cases yes:owns z
      · have setEq : Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<k+1)=
            insert z (Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<k)) := by
          ext e
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
          constructor
          · rintro ⟨h,v⟩
            by_cases eqn:e.val=k
            · exact Or.inl (Fin.ext eqn)
            · exact Or.inr ⟨h,by omega⟩
          · rintro (rfl|⟨h,v⟩)
            · exact ⟨yes,by simp [z]⟩
            · exact ⟨h,by omega⟩
        have out : z∉Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<k) := by simp [z]
        rw [setEq,Finset.sum_insert out,ite_eq_left yes,Nat.cast_add,add_comm]
      · have setEq : Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<k+1)=
            Finset.univ.filter (fun e:Fin 8=>owns e ∧ e.val<k) := by
          ext e;simp only [Finset.mem_filter,Finset.mem_univ,true_and];apply and_congr_right
          intro h
          have ne:e.val≠k := by intro eqn;exact yes ((show e=z from Fin.ext eqn) ▸ h)
          omega
        rw [setEq,ite_eq_right yes,Nat.cast_zero,add_zero]
  exact prefixSum j.val (by have:=j.isLt;omega)

end PrivateSite

theorem occupied_iff {m : Memory W} {roleCount : ℕ} (party : Fin roleCount→Prop)
    (selected : A.party.motif<(HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3).val)
    (room : A.party.motif<2^W) (masks : ∀ j:Fin roleCount,
      (HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).incident 5).val.testBit j.val=decide (party j))
    (j : Fin roleCount) : selectedBit A m j.val ↔ party j := by
  change ((A.party.motif:Word W).val<_ ∧ _=true) ↔ _
  rw [Fin.val_cast_of_lt room,masks]
  simp [selected]

def bankAddr (node motif party family bank : ℕ) :=
    HistoryScratch.atWord A.party.arena A.party.V A.party.motifs A.party.parties node ⟨motif,party,family,bank⟩ 0

def sourceBank (node : ℕ) (group : Bool) (slot : ℕ) (role : ℕ) (b : ℕ) :=
  if group then bankAddr A node (A.party.motif+2) (role+2) 2 b
  else bankAddr A node (slot+2) 0 3 b

def resultBank (node : ℕ) (group : Bool) (b : ℕ) :=
  if group then bankAddr A node (A.party.motif+2) 0 3 b else bankAddr A node 0 0 4 b

def role (m : Memory W) (ord : ℕ) :=
  let pred := fun i : Fin A.party.parties => selectedBit A m i.val
  if h : ord<Fintype.card {j // pred j} then (Diagonal.HistoryMaskOrder.order pred ⟨ord,h⟩).val.val else 0

private theorem bank_value (m : Memory W) (p : Word W) (node : ℕ)
    (nodeId : (id_ A : T W).eval Fin.elim0 m (fun _=>p)=(node:Word W))
    (x y z t : T W) (vx vy vz vt : ℕ)
    (hx : x.eval Fin.elim0 m (fun _=>p)=(vx:Word W)) (hy : y.eval Fin.elim0 m (fun _=>p)=(vy:Word W))
    (hz : z.eval Fin.elim0 m (fun _=>p)=(vz:Word W)) (ht : t.eval Fin.elim0 m (fun _=>p)=(vt:Word W)) :
    (bank A x y z t).eval Fin.elim0 m (fun _=>p)=(bankAddr A node vx vy vz vt:Word W) := by
  simp [bank,bankAddr,HistoryScratch.atWord,HistoryScratch.sector,a,times,l,Term.eval_binary,Term.eval_literal,
    BinaryOp.eval,nodeId,hx,hy,hz,ht,Nat.cast_add,Nat.cast_mul]

private theorem root_value (g : Bool) (m : Memory W) (p : Word W) (node i b : ℕ)
    (nodeId : (id_ A : T W).eval Fin.elim0 m (fun _=>p)=(node:Word W))
    (small : 2^A.party.parties<2^W) (two : 2<2^W)
    (valid : g=true→i<Fintype.card {j : Fin A.party.parties // selectedBit A m j.val}) :
    (rootData A g i b).eval Fin.elim0 m (fun _=>p)=(sourceBank A node g i (role A m i) b:Word W) := by
  cases g with
  | false =>
    dsimp only [rootData,motifBank,sourceBank]
    apply bank_value A m p node nodeId
    · simp [a,l,Term.eval_binary,BinaryOp.eval,Nat.cast_add]
    · rfl
    · rfl
    · rfl
  | true =>
    have hi:=valid rfl
    have val:=occupied_ordinal A m p small two ⟨i,hi⟩
    dsimp only [rootData,sourceBank]
    apply bank_value A m p node nodeId
    · rfl
    · simp [a,l,Term.eval_binary,BinaryOp.eval,val,role,hi,Nat.cast_add]
    · rfl
    · rfl

/-- The seven hub words and the two physical child arrays. The third operand is a
gather-array pointer for a party and the literal two for an identity-wired motif. -/
def groupHub (_m : Memory W) (g : Bool) (node pins share count : ℕ) : HistoryBoundedJoin.Hub :=
  ⟨resultBank A node g 0,pins,if g then share else 0,count,A.party.seed+64+7,A.party.arguments⟩

def groupLink (m : Memory W) (g : Bool) (node i : ℕ) : HistoryBoundedJoin.Child :=
  let root := sourceBank A node g i (role A m i)
  let cap := if g then A.party.parties else A.party.motifs
  ⟨root 1,root 3,if g then 10 else 11,A.party.seed+64+7+4*cap+3*i⟩

def groupArgs (m : Memory W) (g : Bool) (node i : ℕ) : Fin 3→Word W :=
  let root := sourceBank A node g i (role A m i)
  ![((root 3:ℕ):Word W),m (root 1+1),((if g then root 2 else 2:ℕ):Word W)]

structure GroupRead (g : Bool) (m : Memory W) where
  node : ℕ
  pins : ℕ
  shared : ℕ
  count : ℕ
  nodeWord : ∀ p : Word W,(id_ A : T W).eval Fin.elim0 m (fun _=>p)=(node:Word W)
  ports : ∀ p : Word W,(portCount A : T W).eval Fin.elim0 m (fun _=>p)=(pins:Word W)
  free : g=true→m (((A.privateStarts+8:ℕ):Word W).val)=(shared:Word W)
  live : g=true→count=Fintype.card {j : Fin A.party.parties // selectedBit A m j.val}
  motifs : g=false→∀ p : Word W,(rd (kr A) 3:T W).eval Fin.elim0 m (fun _=>p)=(count:Word W)
  countCap : count≤ if g then A.party.parties else A.party.motifs
  maskRoom : 2^A.party.parties<2^W
  two : 2<2^W
  sourceRoom : ∀ i:Fin count,sourceBank A node g i.val (role A m i.val) 1+1<2^W

def GroupRead.of_values (g : Bool) (m : Memory W) (node pins shared count : ℕ)
    (cursor : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W))
    (ports : let r:=HistoryGatherBody.selected A m
      r.oldBits+r.newBits=(pins:Word W))
    (free : g=true→m (((A.privateStarts+8:ℕ):Word W).val)=(shared:Word W))
    (parties : g=true→count=Fintype.card {j : Fin A.party.parties // selectedBit A m j.val})
    (motifs : g=false→HistoryGatherBody.wordAt m (HistoryGatherBody.selected A m).kernel 3=(count:Word W))
    (bound : count≤ if g then A.party.parties else A.party.motifs) (small : 2^A.party.parties<2^W) (two : 2<2^W)
    (room : ∀ i:Fin count,sourceBank A node g i.val (role A m i.val) 1+1<2^W) :
    GroupRead A g m where
  node:=node
  pins:=pins
  shared:=shared
  count:=count
  nodeWord p:=by rw [id_,HeaderScan.eval_closed];exact cursor
  ports p:=by
    simp only [portCount,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,HeaderScan.eval_closed]
    exact ports
  free:=free
  live:=parties
  motifs:=by
    intro h p
    simp only [rd,kr,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,HeaderScan.eval_closed]
    exact motifs h
  countCap:=bound
  maskRoom:=small
  two:=two
  sourceRoom:=room

private theorem rect_row {α : Type*} (n k : ℕ) (f : ℕ→List α) (len : ∀ i,(f i).length=k)
    (i : Fin n) (j : Fin k) : ((List.range n).flatMap f)[k*i.val+j.val]?=(f i.val)[j.val]? := by
  induction n with
  | zero=>exact i.elim0
  | succ n ih=>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    have size (l : List ℕ) : (l.flatMap f).length=k*l.length := by
      induction l with
      | nil=>simp
      | cons a xs h=>simp [len,h,Nat.mul_succ,Nat.add_comm]
    have b : ((List.range n).flatMap f).length=k*n := by simp [size]
    by_cases less:i.val<n
    · rw [List.getElem?_append_left (by rw [b];calc
        k*i.val+j.val<k*i.val+k:=Nat.add_lt_add_left j.isLt _
        _=k*(i.val+1):=by rw [Nat.mul_succ]
        _≤k*n:=Nat.mul_le_mul_left k less)]
      exact ih ⟨i.val,less⟩
    · have atEnd : i.val=n := by have:=i.isLt;omega
      rw [List.getElem?_append_right (by rw [b,atEnd];omega),b,atEnd,Nat.add_sub_cancel_left]

private theorem listWords_length {α : Type*} (k : ℕ) (xs : List ℕ) (f : ℕ→List α) (cnt : ∀ i,(f i).length=k) :
    (xs.flatMap f).length=k*xs.length := by
  induction xs with
  | nil=>simp
  | cons j js ih=>simp [cnt,ih,Nat.mul_succ,Nat.add_comm]

theorem rows_len (g : Bool) : (rows A W g).length=7+7*(if g then A.party.parties else A.party.motifs) := by
  unfold rows
  let n:=if g then A.party.parties else A.party.motifs
  simp only [List.length_append,List.length_cons,List.length_nil]
  rw [listWords_length 4 _ _ (fun _=>rfl),listWords_length 3 _ _ (fun _=>rfl)]
  simp only [List.length_range]
  omega

private def subCap (g : Bool) := if g then A.party.parties else A.party.motifs

private def headFields (g : Bool) : List (T W) :=
  let out (b : ℕ) := if g then motifBank A (l A.party.motif) b else rootBank A b
  [out 0,portCount A,if g then (l (A.privateStarts+8)).load else l 0,
   if g then total (bit A) A.party.parties else rd (kr A) 3,l (A.party.seed+64+7),l A.party.arguments,out 1]

private def childFields (g : Bool) (i : ℕ) : List (T W) :=
  [rootData A g i 1,rootData A g i 3,l (if g then 10 else 11),l (A.party.seed+64+7+4*subCap A g+3*i)]

private def operandFields (g : Bool) (i : ℕ) : List (T W) :=
  [rootData A g i 3,rd (rootData A g i 1) 1,if g then rootData A g i 2 else l 2]

private theorem rows_unfold (g : Bool) : rows A W g = headFields A g ++
    (List.range (subCap A g)).flatMap (childFields A g) ++
    (List.range (subCap A g)).flatMap (operandFields A g) := rfl

private theorem result_bank_value (m : Memory W) (g : Bool) (p : Word W) (node b : ℕ)
    (nodeId : (id_ A : T W).eval Fin.elim0 m (fun _=>p)=(node:Word W)) :
    (if g then motifBank A (l A.party.motif) b else rootBank A b).eval Fin.elim0 m (fun _=>p)=(resultBank A node g b:Word W) := by
  cases g <;> dsimp only [resultBank,motifBank,rootBank,ite_false,ite_true]
  · exact bank_value A m p node nodeId _ _ _ _ _ _ _ _ rfl rfl rfl rfl
  · apply bank_value A m p node nodeId
    · simp [a,l,Term.eval_binary,BinaryOp.eval,Nat.cast_add]
    all_goals rfl

set_option maxHeartbeats 1000000 in
private theorem GroupRead.head_value {g : Bool} {m : Memory W} (S : GroupRead A g m) (p : Word W) (j : Fin 7) :
    ((headFields A g)[j.val]'(show j.val<7 from j.isLt)).eval Fin.elim0 m (fun _=>p)=
      (if hj : j.val<6 then ((groupHub A m g S.node S.pins S.shared S.count).words ⟨j.val,by omega⟩ : Word W)
       else (resultBank A S.node g 1:Word W)) := by
  classical
  have first := result_bank_value A m g p S.node 0 (S.nodeWord p)
  have last := result_bank_value A m g p S.node 1 (S.nodeWord p)
  have third : (if g then (l (A.privateStarts+8)).load else l 0:T W).eval Fin.elim0 m (fun _=>p)=
      ((if g then S.shared else 0:ℕ):Word W) := by cases g <;> first | rfl | exact S.free rfl
  have fourth : (if g then total (bit A) A.party.parties else rd (kr A) 3:T W).eval Fin.elim0 m (fun _=>p)=(S.count:Word W) := by
    cases g
    · exact S.motifs rfl p
    · rw [S.live rfl];exact occupied_count A m p S.maskRoom S.two
  fin_cases j
  · exact first
  · exact S.ports p
  · exact third
  · exact fourth
  · rfl
  · rfl
  · exact last

private theorem GroupRead.child_value {g : Bool} {m : Memory W} (S : GroupRead A g m) (p : Word W)
    (i : Fin S.count) (j : Fin 4) :
    ((childFields A g i.val)[j.val]'(show j.val<4 from j.isLt)).eval Fin.elim0 m (fun _=>p)=
      ((groupLink A m g S.node i.val).words j:Word W) := by
  have live (h : g=true) : i.val < Fintype.card {k : Fin A.party.parties // selectedBit A m k.val} :=
    i.isLt.trans_eq (S.live h)
  fin_cases j
  · exact root_value A g m p S.node i.val 1 (S.nodeWord p) S.maskRoom S.two live
  · exact root_value A g m p S.node i.val 3 (S.nodeWord p) S.maskRoom S.two live
  · rfl
  · rfl

private theorem read_next (t : T W) (m : Memory W) (p : Word W) (n : ℕ)
    (value : t.eval Fin.elim0 m (fun _=>p)=(n:Word W)) (room : n+1<2^W) :
    (rd t 1).eval Fin.elim0 m (fun _=>p) = m (n+1) := by
  simp only [rd,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,BinaryOp.eval,value]
  apply congrArg m
  simpa only [Nat.cast_add,Nat.cast_one] using Fin.val_cast_of_lt room

set_option maxHeartbeats 1000000 in
private theorem GroupRead.argument_value {g : Bool} {m : Memory W} (S : GroupRead A g m) (p : Word W)
    (i : Fin S.count) (j : Fin 3) :
    ((operandFields A g i.val)[j.val]'(show j.val<3 from j.isLt)).eval Fin.elim0 m (fun _=>p)=groupArgs A m g S.node i.val j := by
  have live (h : g=true) : i.val < Fintype.card {k : Fin A.party.parties // selectedBit A m k.val} :=
    i.isLt.trans_eq (S.live h)
  have atRoot (b : ℕ) := root_value A g m p S.node i.val b (S.nodeWord p) S.maskRoom S.two live
  fin_cases j
  · exact atRoot 3
  · exact read_next (rootData A g i.val 1) m p _ (atRoot 1) (S.sourceRoom i)
  · cases g with
    | false =>
      change (l 2 : T W).eval Fin.elim0 m (fun _=>p) = 2
      simp only [l,Term.eval_literal,Nat.cast_ofNat]
    | true => exact atRoot 2

theorem GroupRead.group_image {g : Bool} {m : Memory W} (S : GroupRead A g m)
    (room : A.party.seed+64+(rows A W g).length<2^W) :
    let H := groupHub A m g S.node S.pins S.shared S.count
    let B := groupBuild (W:=W) A g H m
    (∀ j : Fin 6,B.input (B.layout.hub+j.val)=(H.words j:Word W)) ∧
    B.input (B.layout.hub+6)=(resultBank A S.node g 1:Word W) ∧
    (∀ (i : Fin S.count) (j : Fin 4),B.input (H.children+(4*i.val+j.val))=
      ((groupLink A m g S.node i.val).words j:Word W)) ∧
    (∀ (i : Fin S.count) (j : Fin 3),B.input ((groupLink A m g S.node i.val).operand+j.val)=
      groupArgs A m g S.node i.val j) := by
  let n := subCap A g
  let children := (List.range n).flatMap (childFields (W:=W) A g)
  let operands := (List.range n).flatMap (operandFields (W:=W) A g)
  let H := (headFields (W:=W) A g)
  have headLen : H.length=7 := rfl
  have childLen : children.length=4*n := by
    exact (listWords_length 4 (List.range n) (childFields (W:=W) A g) (fun _=>rfl)).trans
      (by rw [List.length_range])
  have dataLen := rows_len (W:=W) A g
  change (rows A W g).length=7+7*n at dataLen
  have fmt : rows A W g = (H++children)++operands := rows_unfold A g
  have value (k : ℕ) (f : T W) (eqn : (rows A W g)[k]?=some f) :
      headerImage (joinHeader A W g) (A.party.seed+64) (rows A W g).length m (A.party.seed+64+k)=
      f.eval Fin.elim0 m (fun _=>((A.party.seed+64+k:ℕ):Word W)) := by
    obtain ⟨hk,atK⟩ := List.getElem?_eq_some_iff.mp eqn
    exact (header_at A g m ⟨k,hk⟩ room).trans (by rw [List.get_eq_getElem,atK])
  have readhead (j : Fin 7) : (rows A W g)[j.val]?=H[j.val]? := by
    have hj:=j.isLt
    have atLeft : j.val < (H++children).length := by rw [List.length_append,headLen]; omega
    have atFirst : j.val < H.length := by rw [headLen]; exact hj
    rw [fmt,List.getElem?_append_left atLeft,List.getElem?_append_left atFirst]
  have atHead (j : Fin 7) := value j.val _ ((readhead j).trans (List.getElem?_eq_getElem (by rw [headLen];exact j.isLt)))
  refine ⟨fun j=>?_,?_,fun i j=>?_,fun i j=>?_⟩
  · have field := GroupRead.head_value A S ((A.party.seed+64+j.val:ℕ):Word W) j.castSucc
    exact (atHead j.castSucc).trans (by simpa [j.isLt] using field)
  · exact (atHead 6).trans (GroupRead.head_value A S ((A.party.seed+64+6:ℕ):Word W) 6)
  · have hi : i.val<n := i.isLt.trans_le S.countCap
    have pos : 4*i.val+j.val<4*n := by omega
    have row := rect_row n 4 (childFields (W:=W) A g) (fun _=>rfl) ⟨i.val,hi⟩ j
    change children[4*i.val+j.val]?=_ at row
    have atK : (rows A W g)[7+(4*i.val+j.val)]?=(childFields (W:=W) A g i.val)[j.val]? := by
      rw [fmt,List.getElem?_append_left (by simp [headLen,childLen];omega),
        List.getElem?_append_right (by omega),headLen,Nat.add_sub_cancel_left]
      exact row
    have out:=value _ _ (atK.trans (List.getElem?_eq_getElem (show j.val<4 from j.isLt)))
    have field := GroupRead.child_value A S ((A.party.seed+64+(7+(4*i.val+j.val)):ℕ):Word W) i j
    change headerImage (joinHeader A W g) (A.party.seed+64) (rows A W g).length m
      (A.party.seed+64+7+(4*i.val+j.val)) = _
    rw [show A.party.seed+64+7+(4*i.val+j.val) = A.party.seed+64+(7+(4*i.val+j.val)) by omega]
    exact out.trans field
  · have hi : i.val<n := i.isLt.trans_le S.countCap
    have row := rect_row n 3 (operandFields (W:=W) A g) (fun _=>rfl) ⟨i.val,hi⟩ j
    have atK : (rows A W g)[7+4*n+(3*i.val+j.val)]?=(operandFields (W:=W) A g i.val)[j.val]? := by
      rw [fmt,List.getElem?_append_right (by simp [headLen,childLen]),List.length_append,headLen,childLen,Nat.add_sub_cancel_left]
      exact row
    have out:=value _ _ (atK.trans (List.getElem?_eq_getElem (show j.val<3 from j.isLt)))
    have field := GroupRead.argument_value A S ((A.party.seed+64+(7+4*n+(3*i.val+j.val)):ℕ):Word W) i j
    change headerImage (joinHeader A W g) (A.party.seed+64) (rows A W g).length m
      (A.party.seed+64+7+4*n+3*i.val+j.val) = _
    rw [show A.party.seed+64+7+4*n+3*i.val+j.val =
      A.party.seed+64+(7+4*n+(3*i.val+j.val)) by omega]
    exact out.trans field

/-- The motif and site joins use the actual cached child records and geometry
map words. Both emit the ordered glue at the physical output bank. -/
theorem join_exec {F : Type*} {s p h : ℕ} {arity : Fin s→ℕ} (g : Bool) (T : HistoryBoundedJoin.Hub)
    (N : ∀ i,BitNetwork F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p)
    (id : ((Fin 3→Bool)→F)→ℕ) (head : Fin s→Header ℕ)
    (map : Fin s→Tape.MapRow) (start : ℕ) (m : Memory W)
    (room : A.party.seed+64+(rows A W g).length<2^W)
    (safe : Protected (joinHeader A W g) m (A.party.seed+64) (rows A W g).length)
    (src : HistoryBoundedBody.Build.Source (groupBuild A g T m) (Tape.tape (W:=W) N wire id head))
    (res : HistoryBoundedBody.Build.Resident (groupBuild A g T m) N wire id head map start) :
    let B := groupBuild A g T m
    let jobs := Tape.tape (W:=W) N wire id head
    (join A W g).Exec m (B.output jobs) (4+(rows A W g).length*(2*(joinHeader A W g).binds+4)+B.ticks jobs) ∧
      HistoryCompiledRows.Records id (glue N wire) start (B.output jobs) := by
  let B := groupBuild A g T m
  have run := HistoryBoundedBody.Build.complete B N wire id head map start src res
  refine ⟨?_,run.2⟩
  exact Procedure.Exec.then (write_header (joinHeader A W g) _ _ m room safe) run.1

theorem private_exec (m : Memory W) (room : A.privateStarts+9<2^W)
    (safe : Protected (privateHeader A W) m A.privateStarts 9) :
    (privateRows A W).Exec m (headerImage (privateHeader A W) A.privateStarts 9 m)
      (4+9*(2*(privateHeader A W).binds+4)) :=
  write_header _ _ _ _ room safe

/-- Fold the selected slot's genuine native party and geometry procedures in row
order; each body's input is the previous body's concrete output. -/
private theorem fold_rows (l : List ℕ) (step : ℕ→Procedure W) (run : Procedure W)
    (transform : ℕ→Memory W→Memory W) (tax : ℕ→ℕ) (inp state : Memory W) (spent : ℕ)
    (start : run.Exec inp state spent)
    (entries : ∀ before j tail,l=before++j::tail →
      let m := before.foldl (fun a k=>transform k a) state
      (step j).Exec m (transform j m) (tax j)) :
    (l.foldl (fun code i=>code.seq (step i)) run).Exec inp
      (l.foldl (fun a j=>transform j a) state) (spent+(l.map tax).sum) := by
  induction l generalizing run state spent with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
    exact start
  | cons i is ih =>
    have body : (step i).Exec state (transform i state) (tax i) := entries [] i is rfl
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ← Nat.add_assoc]
    intro labels registers slots machine
    refine ih (run.seq (step i)) (transform i state) (spent+tax i) (Procedure.Exec.then start body) ?_ machine
    intro before j tail eqn
    dsimp only
    intro labels' registers' slots' machine'
    exact entries (i::before) j tail (congrArg (List.cons i) eqn) machine'

theorem motif_exec (m : Memory W) (room : A.privateStarts+9<2^W)
    (safe : Protected (privateHeader A W) m A.privateStarts 9)
    (pairs gather : ℕ→Memory W→Memory W) (pairTax gatherTax : ℕ→ℕ)
    (parties : ∀ before j tail,List.range A.party.parties=before++j::tail →
      let mid := before.foldl (fun x t=>gather t (pairs t x)) (headerImage (privateHeader A W) A.privateStarts 9 m)
      (HistoryPartyPair.procedure W (withParty A j).party).Exec mid (pairs j mid) (pairTax j) ∧
      (HistoryGatherBody.procedure W (withParty A j)).Exec (pairs j mid) (gather j (pairs j mid)) (gatherTax j))
    (out : Memory W) (lastCost : ℕ)
    (last : (join A W true).Exec
      ((List.range A.party.parties).foldl (fun x j=>gather j (pairs j x)) (headerImage (privateHeader A W) A.privateStarts 9 m))
      out lastCost) :
    (motif A W).Exec m out (4+9*(2*(privateHeader A W).binds+4)+
      ((List.range A.party.parties).map (fun j=>pairTax j+gatherTax j)).sum+lastCost) := by
  let each := fun (prev : Procedure W) (j : ℕ)=>
    (prev.seq (HistoryPartyPair.procedure W (withParty A j).party)).seq (HistoryGatherBody.procedure W (withParty A j))
  let pass := fun x j=>gather j (pairs j x)
  let tax := fun j=>pairTax j+gatherTax j
  have fold (l : List ℕ) (code : Procedure W) (state : Memory W) (spent : ℕ) (start : code.Exec m state spent)
      (steps : ∀ before j tail,l=before++j::tail→
        let mid := before.foldl pass state
        (HistoryPartyPair.procedure W (withParty A j).party).Exec mid (pairs j mid) (pairTax j) ∧
        (HistoryGatherBody.procedure W (withParty A j)).Exec (pairs j mid) (pass mid j) (gatherTax j)) :
      (l.foldl each code).Exec m (l.foldl pass state) (spent+(l.map tax).sum) := by
    induction l generalizing code state spent with
    | nil =>
      simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]
      exact start
    | cons i is ih =>
      obtain ⟨pair,part⟩ := steps [] i is rfl
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, tax, ← Nat.add_assoc]
      refine ih (each code i) (pass state i) (spent+pairTax i+gatherTax i)
        (Procedure.Exec.then (Procedure.Exec.then start pair) part) ?_
      intro before j tail eqn
      exact steps (i::before) j tail (congrArg (List.cons i) eqn)
  intro labels registers slots machine
  exact Procedure.Exec.then (fold _ _ _ _ (private_exec A m room safe) parties) last machine

theorem kernel_shrink (S : Diagonal.CompressorPacking.Native.Graph.Stage) (mode : A.mode=.shrink S)
    (oldCap : ℕ) (input stage : Memory W) (prefixCost : ℕ)
    (start : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input stage prefixCost)
    (transform : ℕ→Memory W→Memory W) (tax : ℕ→ℕ)
    (motifs : ∀ before j tail,List.range A.party.motifs=before++j::tail →
      let m := before.foldl (fun a k=>transform k a) stage
      (motif (withMotif A j) W).Exec m (transform j m) (tax j))
    (out : Memory W) (lastCost : ℕ)
    (last : (join A W false).Exec ((List.range A.party.motifs).foldl (fun a j=>transform j a) stage) out lastCost) :
    (kernelProcedure A W oldCap).Exec input out (prefixCost+((List.range A.party.motifs).map tax).sum+lastCost) := by
  rw [kernelProcedure,mode]
  exact Procedure.Exec.then (fold_rows _ _ _ _ _ _ _ _ start motifs) last

theorem kernel_refresh (m h pad : ℕ) (mode : A.mode=.refresh m h pad) (oldCap : ℕ)
    {input stage out : Memory W} {c₀ c₁ : ℕ}
    (first : (HistoryNodePorts.phase W A.nodePorts oldCap).Exec input stage c₀)
    (part : (motif (withMotif A 0) W).Exec stage out c₁) :
    (kernelProcedure A W oldCap).Exec input out (c₀+c₁) := by
  rw [kernelProcedure,mode]
  exact Procedure.Exec.then first part

end Execution

section EagerReads
open Computability.VPVNP.BurstRAM.PrivateRAM PhysicalPinsExpr HistoryPartyBatchExec

private def Tracked (m : Memory W) (p : Word W) (safe : ℕ→Prop) (e : T W) : Prop :=
  ∀ x∈e.reads Fin.elim0 m (fun _=>p),safe x

variable {m : Memory W} {p : Word W} {safe : ℕ→Prop}
@[simp] private theorem tracked_lit (v : Word W) : Tracked m p safe (.literal v) := by simp [Tracked]
@[simp] private theorem tracked_reg (i : Fin 1) : Tracked m p safe (.result i) := by simp [Tracked,Term.reads]
@[simp] private theorem tracked_op (op : BinaryOp) (x y : T W) :
    Tracked m p safe (.binary op x y) ↔ Tracked m p safe x ∧ Tracked m p safe y := by
  simp only [Tracked,Term.reads_binary,List.forall_mem_append]
@[simp] private theorem tracked_sel (op : Comparison) (x y a b : T W) :
    Tracked m p safe (.select op x y a b) ↔
    Tracked m p safe x ∧ Tracked m p safe y ∧ Tracked m p safe a ∧ Tracked m p safe b := by
  simp only [Tracked,Term.reads_select,List.forall_mem_append]
@[simp] private theorem tracked_load (x : T W) :
    Tracked m p safe x.load ↔ Tracked m p safe x ∧ safe (x.eval Fin.elim0 m (fun _=>p)).val := by
  simp only [Tracked,Term.reads_load,List.forall_mem_append,List.forall_mem_singleton]

private theorem tracked_select (key : T W) (h : Tracked m p safe key) (i : ℕ) (xs : List (T W))
    (each : ∀ x∈xs,Tracked m p safe x) : Tracked m p safe (select key i xs) := by
  induction xs generalizing i with
  | nil=>simp [select,l]
  | cons x xs ih=>
    simp only [List.forall_mem_cons] at each
    simp [select,l,h,each.1,ih (i+1) each.2]

private theorem tracked_total (f : ℕ→T W) (n : ℕ) (h : ∀ j,j<n→Tracked m p safe (f j)) :
    Tracked m p safe (total f n) := by
  induction n with
  | zero=>simp [total,l]
  | succ n ih=>exact (tracked_op ..).2 ⟨ih (fun j hj=>h _ (by omega)),h n (by omega)⟩

/-- Physical addresses used by the current predecessor directory and the pointer to
the published successor half table. The last row is queried by the native program
even when a branch selects zero. -/
def nodeAddress (A : HistoryNodePorts.Layout) (m : Memory W) : Word W :=
  (HistoryNodePorts.node A).value (fun _=>0) m (fun _=>0)

def lastHalfAddress (A : HistoryNodePorts.Layout) (m : Memory W) : Word W :=
  let h:=wordAt m (nodeAddress A m) 6
  wordAt m h 1+4*cutWord (m h.val) 1

structure NodeReadCells (A : HistoryNodePorts.Layout) (m : Memory W) (safe : ℕ→Prop) : Prop where
  cursor : safe (A.cursor:Word W).val
  node : ∀ j : Fin 8,safe (nodeAddress A m+(j.val:Word W)).val
  header : ∀ j : Fin 2,safe (wordAt m (nodeAddress A m) 6+(j.val:Word W)).val
  tail : ∀ j : Fin 2,safe (lastHalfAddress A m+((j.val+2:ℕ):Word W)).val

private theorem track_id (A : HistoryNodePorts.Layout) (h : safe (A.cursor:Word W).val) :
    Tracked m p safe (HeaderScan.closed (HistoryNodePorts.id A)) := by
  change Tracked m p safe (cut (Term.literal (A.cursor:Word W)).load (l 1))
  simp only [cut,l,tracked_sel,tracked_lit,tracked_load,tracked_op,Term.eval_literal,h,and_self]

private theorem track_node (A : HistoryNodePorts.Layout) (h : safe (A.cursor:Word W).val) :
    Tracked m p safe (HeaderScan.closed (HistoryNodePorts.node A)) := by
  change Tracked m p safe (a (l A.nodes) (times (l 8) (HeaderScan.closed (HistoryNodePorts.id A))))
  simp [a,times,l,track_id A h]

private theorem node_eval_at (A : HistoryNodePorts.Layout) (m : Memory W) (p : Word W) :
    (HeaderScan.closed (HistoryNodePorts.node A) : T W).eval Fin.elim0 m (fun _=>p) =
      nodeAddress A m := by
  rw [HeaderScan.eval_closed]
  rfl

private theorem track_rd (x : T W) (j : ℕ) (h : Tracked m p safe x)
    (cell : safe (x.eval Fin.elim0 m (fun _=>p)+(j:Word W)).val) :
    Tracked m p safe (rd x j) := by
  simp only [rd,a,l,tracked_load,tracked_op,tracked_lit,Term.eval_binary,Term.eval_literal,
    BinaryOp.eval,and_true,h,cell]

private theorem track_node_field (A : HistoryNodePorts.Layout) (j : Fin 8) (h : safe (A.cursor:Word W).val)
    (cell : safe (nodeAddress A m+(j.val:Word W)).val) :
    Tracked m p safe (rd (HeaderScan.closed (HistoryNodePorts.node A)) j.val) := by
  apply track_rd _ _ (track_node A h)
  simpa only [node_eval_at] using cell

private theorem track_fresh (A : HistoryNodePorts.Layout) (H : NodeReadCells A m safe) :
    Tracked m p safe (HeaderScan.closed (HistoryNodePorts.fresh A)) := by
  let head : T W := rd (HeaderScan.closed (HistoryNodePorts.node A)) 6
  let last : T W := a (rd head 1) (times (l 4) (cut head.load (l 1)))
  have headValue : head.eval Fin.elim0 m (fun _=>p) = wordAt m (nodeAddress A m) 6 := by
    simp only [head,rd,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,node_eval_at,
      BinaryOp.eval,wordAt]
  have hb : Tracked m p safe head := track_node_field A 6 H.cursor (H.node 6)
  have h0 : safe (head.eval Fin.elim0 m (fun _=>p)).val := by
    rw [headValue]
    simpa using H.header 0
  have hc : Tracked m p safe head.load := (tracked_load (m:=m) (p:=p) (safe:=safe) head).2 ⟨hb,h0⟩
  have hp : Tracked m p safe (rd head 1) := by
    apply track_rd _ _ hb
    rw [headValue]
    exact H.header 1
  have hl : Tracked m p safe last := by simp only [last,a,times,cut,l,tracked_op,tracked_sel,
    tracked_lit,hc,hp,and_self]
  have lastValue : last.eval Fin.elim0 m (fun _=>p) = lastHalfAddress A m := by
    simp only [last,a,times,rd,cut,l,Term.eval_select,Term.eval_binary,Term.eval_literal,
      Term.eval_load,headValue,BinaryOp.eval,Comparison.test,decide_eq_true_eq,
      lastHalfAddress,wordAt,cutWord,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
    first
    | rfl
  have word (j : Fin 2) : Tracked m p safe (rd last (j.val+2)) := by
    apply track_rd _ _ hl
    rw [lastValue]
    exact H.tail j
  change Tracked m p safe (.select .eq head.load (l 0) (l 0) (a (rd last 3) (rd last 2)))
  exact (tracked_sel (m:=m) (p:=p) (safe:=safe) .eq head.load (l 0) (l 0)
    (a (rd last 3) (rd last 2))).2
    ⟨hc, tracked_lit _, tracked_lit _,
      (tracked_op (m:=m) (p:=p) (safe:=safe) .add (rd last 3) (rd last 2)).2 ⟨word 1, word 0⟩⟩

/-- Numerical predecessor addresses for every issued child slot. The cap is the
number of children physically assigned to this node by its stage family. -/
structure ChildReadCells (A : HistoryNodePorts.Layout) (m : Memory W) (cap : ℕ) (safe : ℕ→Prop) : Prop where
  cursor : safe (A.cursor:Word W).val
  directory : ∀ j : Fin 2,safe (nodeAddress A m+((3+j.val:ℕ):Word W)).val
  list : ∀ j : Fin cap,safe (wordAt m (nodeAddress A m) 3+(j.val:Word W)).val
  cache : ∀ j : Fin cap,let id:=wordAt m (wordAt m (nodeAddress A m) 3) j.val
    ∀ k : Fin 2,safe ((A.cache:Word W)+8*id+((1+4*k.val:ℕ):Word W)).val

theorem childPrefix_protected (A : HistoryNodePorts.Layout) (cap : ℕ) (m : Memory W)
    (H : ChildReadCells A m cap (fun i=>i<A.starts ∨ A.starts+(cap+1)≤ i)) :
    Protected (HeaderScan.closed (childPrefix A cap)) m A.starts (cap+1) := by
  let safe:=fun i=>i<A.starts ∨ A.starts+(cap+1)≤ i
  intro p _ _
  change Tracked m p safe _
  have cn : Tracked m p safe (HeaderScan.closed (HistoryNodePorts.childCount A)) :=
    track_node_field A 4 H.cursor (H.directory 1)
  have cl : Tracked m p safe (HeaderScan.closed (HistoryNodePorts.childList A)) :=
    track_node_field A 3 H.cursor (H.directory 0)
  let children : T W := HeaderScan.closed (HistoryNodePorts.childList A)
  have childrenEval : children.eval Fin.elim0 m (fun _=>p) = wordAt m (nodeAddress A m) 3 := by
    change (rd (HeaderScan.closed (HistoryNodePorts.node A)) 3).eval Fin.elim0 m (fun _=>p) = _
    simp only [rd,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,BinaryOp.eval,
      node_eval_at,wordAt]
  have prev (j : Fin cap) : Tracked m p safe (HeaderScan.closed (HistoryNodePorts.oldAt A (.lit j.val))) := by
    let key : T W := rd children j.val
    have k : Tracked m p safe key := track_rd children j.val cl (by
      rw [childrenEval]
      exact H.list j)
    have keyEval : key.eval Fin.elim0 m (fun _=>p) = wordAt m (wordAt m (nodeAddress A m) 3) j.val := by
      simp only [key,rd,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,BinaryOp.eval,
        childrenEval,wordAt]
    let base : T W := a (l A.cache) (times (l 8) key)
    have b : Tracked m p safe base :=
      (tracked_op (m:=m) (p:=p) (safe:=safe) .add (l A.cache) (times (l 8) key)).2
        ⟨tracked_lit _,(tracked_op (m:=m) (p:=p) (safe:=safe) .mul (l 8) key).2 ⟨tracked_lit _,k⟩⟩
    have baseEval : base.eval Fin.elim0 m (fun _=>p) =
        (A.cache:Word W) + 8 * wordAt m (wordAt m (nodeAddress A m) 3) j.val := by
      simp only [base,a,times,l,Term.eval_binary,Term.eval_literal,BinaryOp.eval,keyEval,Nat.cast_ofNat]
    have col (q : Fin 2) : Tracked m p safe (rd base (1+4*q.val)) :=
      track_rd base (1+4*q.val) b (by
        rw [baseEval]
        exact H.cache j q)
    have lo : Tracked m p safe (rd base 1) := col 0
    have hi : Tracked m p safe (rd base 5) := col 1
    change Tracked m p safe (cut (rd base 1) (rd base 5))
    exact (tracked_sel (m:=m) (p:=p) (safe:=safe) .lt (rd base 1) (rd base 5) (l 0)
      (.binary .sub (rd base 1) (rd base 5))).2
        ⟨lo,hi,tracked_lit _,(tracked_op (m:=m) (p:=p) (safe:=safe) .sub (rd base 1) (rd base 5)).2 ⟨lo,hi⟩⟩
  let idx : PhysicalPinsExpr.Formula 1:=.cut (.reg 0) (.lit A.starts)
  let key:=PhysicalPinsExpr.lt idx (HistoryNodePorts.childCount A) idx (HistoryNodePorts.childCount A)
  have ik : Tracked m p safe (HeaderScan.closed idx) := by
    change Tracked m p safe (cut (.result 0) (l A.starts))
    simp only [cut,l,tracked_sel,tracked_reg,tracked_lit,tracked_op,and_self]
  have keyOk : Tracked m p safe (HeaderScan.closed key) :=
    (tracked_sel (m:=m) (p:=p) (safe:=safe) .lt (HeaderScan.closed idx)
      (HeaderScan.closed (HistoryNodePorts.childCount A)) (HeaderScan.closed idx)
      (HeaderScan.closed (HistoryNodePorts.childCount A))).2 ⟨ik,cn,ik,cn⟩
  have stages (n : ℕ) (le : n≤cap) : Tracked m p safe (HeaderScan.closed (HistoryNodePorts.prefix A key n)) := by
    induction n with
    | zero => exact tracked_lit _
    | succ n ih =>
      let old : T W := HeaderScan.closed (HistoryNodePorts.oldAt A (.lit n))
      let branch : T W := .select .lt (l n) (HeaderScan.closed key) old (l 0)
      exact (tracked_op (m:=m) (p:=p) (safe:=safe) .add
        (HeaderScan.closed (HistoryNodePorts.prefix A key n)) branch).2
        ⟨ih (by omega),(tracked_sel (m:=m) (p:=p) (safe:=safe) .lt (l n) (HeaderScan.closed key) old (l 0)).2
          ⟨tracked_lit _,keyOk,prev ⟨n,by omega⟩,tracked_lit _⟩⟩
  exact stages cap le_rfl


private theorem track_kr (A : Layout) (H : NodeReadCells A.nodePorts m safe) : Tracked m p safe (kr A) :=
  track_node_field A.nodePorts 5 H.cursor (H.node 5)

/-- Pointer arithmetic on the six-word S44 kernel's retained incident list. -/
structure MotifReadCells (A : Layout) (m : Memory W) (safe : ℕ→Prop) : Prop where
  kernel : ∀ j : Fin 5,safe ((selected A m).kernel+(j.val:Word W)).val
  incident : ∀ j : Fin 6,safe ((selected A m).incident+(j.val:Word W)).val

private theorem kernel_eval (A : Layout) (m : Memory W) (p : Word W) :
    (kr A : T W).eval Fin.elim0 m (fun _=>p)=(selected A m).kernel := by
  rw [kr,HeaderScan.eval_closed]
  rfl

private theorem incident_eval (A : Layout) (m : Memory W) (p : Word W) :
    (inc A : T W).eval Fin.elim0 m (fun _=>p)=(selected A m).incident := by
  change (inc A : T W).eval Fin.elim0 m (fun _=>p)=wordAt m (selected A m).kernel 4 + _
  simp only [inc,rd,a,l,Term.eval_binary,Term.eval_load,Term.eval_literal,kernel_eval,BinaryOp.eval,wordAt]

private theorem read_word_eval (x : T W) (j : ℕ) (m : Memory W) (p : Word W) :
    (rd x j).eval Fin.elim0 m (fun _=>p)=wordAt m (x.eval Fin.elim0 m (fun _=>p)) j := by
  simp only [rd,a,l,Term.eval_load,Term.eval_binary,Term.eval_literal,BinaryOp.eval,wordAt]

private theorem cut_eval_at (x y : T W) (m : Memory W) (p : Word W) :
    (cut x y).eval Fin.elim0 m (fun _=>p)=
      cutWord (x.eval Fin.elim0 m (fun _=>p)) (y.eval Fin.elim0 m (fun _=>p)) := by
  simp only [cut,l,Term.eval_select,Term.eval_literal,Term.eval_binary,Comparison.test,
    decide_eq_true_eq,Nat.cast_zero,cutWord,BinaryOp.eval]

private theorem track_kernel_word (A : Layout) (N : NodeReadCells A.nodePorts m safe)
    (M : MotifReadCells A m safe) (j : Fin 5) : Tracked m p safe (rd (kr A) j.val) :=
  track_rd (kr A) j.val (track_kr A N) (by rw [kernel_eval]; exact M.kernel j)

private theorem track_incident_word (A : Layout) (N : NodeReadCells A.nodePorts m safe)
    (M : MotifReadCells A m safe) (j : Fin 6) : Tracked m p safe (rd (inc A) j.val) := by
  have k : Tracked m p safe (rd (kr A) 4) := track_kernel_word A N M 4
  have incident : Tracked m p safe (inc A) := (tracked_op ..).2 ⟨k,tracked_lit _⟩
  exact track_rd (inc A) j.val incident (by rw [incident_eval]; exact M.incident j)

private theorem track_live (A : Layout) (N : NodeReadCells A.nodePorts m safe)
    (M : MotifReadCells A m safe) (x : T W) (h : Tracked m p safe x) : Tracked m p safe (live A x) := by
  have k : Tracked m p safe (rd (kr A) 3) := track_kernel_word A N M 3
  exact (tracked_sel ..).mpr ⟨tracked_lit _,k,h,tracked_lit _⟩

private theorem track_bit (A : Layout) (N : NodeReadCells A.nodePorts m safe)
    (M : MotifReadCells A m safe) (j : ℕ) : Tracked m p safe (bit A j) := by
  have h : Tracked m p safe (live A (rd (inc A) 5)) := track_live A N M _ (track_incident_word A N M 5)
  simp [bit,test,l,h]

/-- Width address issued in a private-edge query, including the address evaluated
inside the unselected branch of the RAM word selector. -/
def privateWidthAddress (m : Memory W) (j : ℕ) : Word W :=
  let row:=selected A m
  let dir:=m row.kernel.val
  let idx:=BinaryOp.eval .div (cutWord (wordAt m row.incident 1) (wordAt m dir 1)) (A.histogramStride:Word W)
  wordAt m dir 3+(8*idx+(j:Word W))

structure PrivateReadCells (A : Layout) (m : Memory W) (safe : ℕ→Prop) : Prop where
  stage : ∀ g,A.mode=.shrink g→∀ j : Fin 4,safe (m (selected A m).kernel.val+(j.val:Word W)).val
  width : ∀ g,A.mode=.shrink g→∀ j : Fin 8,safe (privateWidthAddress A m j.val).val

theorem privateHeader_protected (m : Memory W)
    (N : NodeReadCells A.nodePorts m (fun i=>i<A.privateStarts ∨ A.privateStarts+9≤ i))
    (M : MotifReadCells A m (fun i=>i<A.privateStarts ∨ A.privateStarts+9≤ i))
    (I : PrivateReadCells A m (fun i=>i<A.privateStarts ∨ A.privateStarts+9≤ i)) :
    Protected (privateHeader A W) m A.privateStarts 9 := by
  let safe:=fun i=>i<A.privateStarts ∨ A.privateStarts+9≤ i
  intro p _ _
  change Tracked m p safe _
  have src (j : Fin 8) : Tracked m p safe (srcWidth A j.val) := by
    cases mode:A.mode with
    | refresh =>simp [srcWidth,mode,l]
    | shrink g=>
      let stage : T W:=(kr A).load
      let hist:T W:=.binary .div (cut (rd (inc A) 1) (rd stage 1)) (l A.histogramStride)
      have stage_eval : stage.eval Fin.elim0 m (fun _=>p)=m (selected A m).kernel.val := by
        simp only [stage,Term.eval_load,kernel_eval]
      have dp : Tracked m p safe stage :=
        (tracked_load (m:=m) (p:=p) (safe:=safe) (kr A)).2 ⟨track_kr A N,by
          rw [kernel_eval]
          simpa only [Fin.val_zero,Nat.cast_zero,add_zero] using M.kernel 0⟩
      have col (t : Fin 4) : Tracked m p safe (rd stage t.val) :=
        track_rd stage t.val dp (by rw [stage_eval]; exact I.stage g mode t)
      have h1 : Tracked m p safe (rd stage 1):=col 1
      have h3 : Tracked m p safe (rd stage 3):=col 3
      have edge : Tracked m p safe (rd (inc A) 1) := track_incident_word A N M 1
      have hh : Tracked m p safe hist := by
        simp only [hist,cut,l,tracked_op,tracked_sel,tracked_lit,h1,edge,and_self]
      let addr : T W := a (rd stage 3) (a (times (l 8) hist) (l j.val))
      have addr_ok : Tracked m p safe addr := by
        simp only [addr,a,times,l,tracked_op,tracked_lit,h3,hh,and_self]
      have addr_eval : addr.eval Fin.elim0 m (fun _=>p)=privateWidthAddress A m j.val := by
        simp only [addr,hist,privateWidthAddress,a,times,l,Term.eval_binary,Term.eval_literal,
          cut_eval_at,read_word_eval,incident_eval,stage_eval,BinaryOp.eval,Nat.cast_ofNat]
      rw [srcWidth,mode]
      apply track_live A N M
      exact (tracked_load (m:=m) (p:=p) (safe:=safe) addr).2 ⟨addr_ok,by
        rw [addr_eval]
        exact I.width g mode j⟩
  have part (j : Fin 8) : Tracked m p safe (absorbed A j.val) := by
    have mask : Tracked m p safe (live A (rd (inc A) 4)) := track_live A N M _ (track_incident_word A N M 4)
    simp [absorbed,test,l,mask,src j]
  apply tracked_select (m:=m) (p:=p) (safe:=safe) (cut (.result 0) (l A.privateStarts)) (by simp [cut,l])
  intro t ht
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ht
  have hj':=List.mem_range.mp hj
  exact tracked_total _ j (fun k hk=>part ⟨k,by omega⟩)

/-- The eager scan can compute the address of any static candidate, also in a slot
after the last live party. Its raw ordinal is always one of the tested party labels
or the literal fallback zero. -/
private theorem eager_ordinal (slot : ℕ) (p : Word W) (m : Memory W) :
    ∃ j : ℕ,(j=0 ∨ j<A.party.parties) ∧
      (partyOrdinal A slot).eval Fin.elim0 m (fun _=>p)=(j:Word W) := by
  let step (e:T W) (j:ℕ) := Term.select .eq (bit A j) (l 1)
    (.select .eq (total (bit A) j) (l slot) (l j) e) e
  let good:=fun e:T W=>∃ j:ℕ,(j=0 ∨ j<A.party.parties) ∧ e.eval Fin.elim0 m (fun _=>p)=(j:Word W)
  have fold (xs:List ℕ) (bound:∀j∈xs,j<A.party.parties) (base:T W) (init:good base) : good (xs.foldl step base) := by
    induction xs generalizing base with
    | nil=>exact init
    | cons j xs ih=>
      apply ih (fun i h=>bound i (List.mem_cons_of_mem _ h))
      dsimp only [good,step]
      simp only [Term.eval_select]
      split
      · split
        · exact ⟨j,Or.inr (bound j List.mem_cons_self),rfl⟩
        · exact init
      · exact init
  exact fold _ (by simp) _ ⟨0,Or.inl rfl,rfl⟩

private theorem track_ordinal (A : Layout) (N : NodeReadCells A.nodePorts m safe)
    (M : MotifReadCells A m safe) (slot : ℕ) : Tracked m p safe (partyOrdinal A slot) := by
  let step (e:T W) (j:ℕ) := Term.select .eq (bit A j) (l 1)
    (.select .eq (total (bit A) j) (l slot) (l j) e) e
  have fold (xs:List ℕ) (base:T W) (h:Tracked m p safe base) : Tracked m p safe (xs.foldl step base) := by
    induction xs generalizing base with
    | nil=>exact h
    | cons j xs ih=>
      apply ih
      simp [step,l,h,track_bit (p:=p) A N M j,tracked_total (p:=p) (bit A) j (fun k _=>track_bit A N M k)]
  exact fold _ _ (tracked_lit _)

/-- All candidate info words are checked over their raw finite slot/party space.
An inactive slot still points into its statically assigned S12 arena. -/
structure JoinReadCells (A : Layout) (m : Memory W) (g : Bool) (node : ℕ) (safe : ℕ→Prop) : Prop where
  id : (HistoryNodePorts.id A.nodePorts).value (fun _=>0) m (fun _=>0)=(node:Word W)
  oldEnd : safe ((A.nodePorts.starts:Word W)+wordAt m (nodeAddress A.nodePorts m) 4).val
  shared : g=true→safe ((A.privateStarts+8:ℕ):Word W).val
  info : ∀ i,i<(if g then A.party.parties else A.party.motifs)→∀ j,
    (j=0 ∨ j<A.party.parties)→safe ((sourceBank A node g i j 1:Word W)+1).val

private theorem track_loaded_sum (x y : T W) (hx : Tracked m p safe x) (hy : Tracked m p safe y)
    (address : safe (x.eval Fin.elim0 m (fun _=>p) + y.eval Fin.elim0 m (fun _=>p)).val) :
    Tracked m p safe (a x y).load := by
  refine (tracked_load (m:=m) (p:=p) (safe:=safe) (a x y)).2 ⟨(tracked_op .add x y).2 ⟨hx,hy⟩,?_⟩
  simpa only [a,Term.eval_binary,BinaryOp.eval] using address

private theorem track_port_count (A : Layout) (N : NodeReadCells A.nodePorts m safe)
    (last : safe ((A.nodePorts.starts:Word W) + wordAt m (nodeAddress A.nodePorts m) 4).val) :
    Tracked m p safe (portCount A) := by
  let count : T W := HeaderScan.closed (HistoryNodePorts.childCount A.nodePorts)
  have readable : Tracked m p safe count := track_node_field A.nodePorts 4 N.cursor (N.node 4)
  have value : count.eval Fin.elim0 m (fun _=>p) = wordAt m (nodeAddress A.nodePorts m) 4 := by
    have code : count = rd (HeaderScan.closed (HistoryNodePorts.node A.nodePorts)) 4 := rfl
    rw [code,read_word_eval,node_eval_at]
  have cell : Tracked m p safe (a (l A.nodePorts.starts) count).load :=
    track_loaded_sum (l A.nodePorts.starts) count (tracked_lit _) readable (by
      simpa only [l,Term.eval_literal,value] using last)
  exact (tracked_op .add _ _).2 ⟨cell,track_fresh A.nodePorts N⟩

set_option maxHeartbeats 1200000 in
private theorem track_join_header (m : Memory W) (p : Word W) (safe : ℕ → Prop)
    (g : Bool) (node : ℕ) (N : NodeReadCells A.nodePorts m safe)
    (M : MotifReadCells A m safe) (H : JoinReadCells A m g node safe) :
    Tracked m p safe (joinHeader A W g) := by
  have idOK : Tracked m p safe (id_ A):=track_id A.nodePorts N.cursor
  have idV : (id_ A:T W).eval Fin.elim0 m (fun _=>p)=(node:Word W) := by rw [id_,HeaderScan.eval_closed];exact H.id
  have bn (x y z v : T W) (u:Tracked m p safe x) (t:Tracked m p safe y)
      (w:Tracked m p safe z) (q:Tracked m p safe v) : Tracked m p safe (bank A x y z v) := by
    simp [bank,a,times,l,u,t,w,q,idOK]
  have root (i j:ℕ) : Tracked m p safe (rootData A g i j) := by
    cases g with
    | false =>
      exact bn _ _ _ _ ((tracked_op .add _ _).2 ⟨tracked_lit _,tracked_lit _⟩)
        (tracked_lit _) (tracked_lit _) (tracked_lit _)
    | true =>
      exact bn _ _ _ _ (tracked_lit _)
        ((tracked_op .add _ _).2 ⟨track_ordinal (p:=p) A N M i,tracked_lit _⟩)
        (tracked_lit _) (tracked_lit _)
  have info (i:ℕ) (hi:i<subCap A g) : Tracked m p safe (rd (rootData A g i 1) 1) := by
    apply track_rd _ 1 (root i 1)
    rw [Nat.cast_one]
    cases g with
    | false=>
      have zero : (rootData A false i 1).eval Fin.elim0 m (fun _=>p)=(sourceBank A node false i 0 1:Word W) := by
        dsimp only [rootData,motifBank,sourceBank,Bool.false_eq_true,ite_false]
        apply bank_value A m p node idV
        · simp only [a,l,Term.eval_binary,Term.eval_literal,BinaryOp.eval,Nat.cast_add]
        · rfl
        · rfl
        · rfl
      rw [zero]
      exact H.info i hi 0 (.inl rfl)
    | true=>
      obtain ⟨j,bound,eq⟩:=eager_ordinal A i p m
      have rootV : (rootData A true i 1).eval Fin.elim0 m (fun _=>p)=(sourceBank A node true i j 1:Word W) := by
        dsimp only [rootData,sourceBank,ite_true]
        apply bank_value A m p node idV
        · rfl
        · simp only [a,l,Term.eval_binary,Term.eval_literal,BinaryOp.eval,eq,Nat.cast_add]
        · rfl
        · rfl
      rw [rootV]
      exact H.info i hi j bound
  have pc : Tracked m p safe (portCount A) := track_port_count A N H.oldEnd
  have share : Tracked m p safe (if g then (l (A.privateStarts+8)).load else l 0) := by
    cases g with
    | false => exact tracked_lit _
    | true => exact (tracked_load (m:=m) (p:=p) (safe:=safe) _).2 ⟨tracked_lit _,H.shared rfl⟩
  have counts : Tracked m p safe (if g then total (bit A) A.party.parties else rd (kr A) 3) := by
    cases g
    · exact track_kernel_word A N M 3
    · exact tracked_total _ _ (fun j _=>track_bit A N M j)
  have dst (j:ℕ) : Tracked m p safe (if g then motifBank A (l A.party.motif) j else rootBank A j) := by
    cases g <;> apply bn <;> simp [a,l]
  refine tracked_select (m:=m) (p:=p) (safe:=safe) (cut (.result 0) (l (A.party.seed+64)))
    (by simp [cut,l]) 0 (rows A W g) ?_
  intro term ht
  unfold rows at ht
  simp only [List.mem_append,List.mem_flatMap,List.mem_range,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with (h|h)|h
  · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    exacts [dst 0,pc,share,counts,tracked_lit _,tracked_lit _,dst 1]
  · obtain ⟨i,hi,h⟩:=h
    rcases h with rfl|rfl|rfl|rfl
    exacts [root _ _,root _ _,tracked_lit _,tracked_lit _]
  · obtain ⟨i,hi,h⟩:=h
    rcases h with rfl|rfl|rfl
    · exact root _ _
    · exact info i hi
    · by_cases group : g = true
      · rw [ite_eq_left group]
        exact root i 2
      · rw [ite_eq_right group]
        exact tracked_lit ((2 : ℕ) : Word W)


theorem joinHeader_protected (m : Memory W) (g : Bool) (node : ℕ)
    (N : NodeReadCells A.nodePorts m (fun i=>i<A.party.seed+64 ∨ A.party.seed+64+(rows A W g).length≤ i))
    (M : MotifReadCells A m (fun i=>i<A.party.seed+64 ∨ A.party.seed+64+(rows A W g).length≤ i))
    (H : JoinReadCells A m g node (fun i=>i<A.party.seed+64 ∨ A.party.seed+64+(rows A W g).length≤ i)) :
    Protected (joinHeader A W g) m (A.party.seed+64) (rows A W g).length := by
  intro p _ _
  exact track_join_header A m p _ g node N M H

theorem MotifReadCells.of_addresses {m : Memory W} {safe : ℕ→Prop} (kernel incident : ℕ)
    (kernelAt : (selected A m).kernel=(kernel:Word W))
    (incidentAt : (selected A m).incident=(incident:Word W))
    (kernelSpan : ∀ j:Fin 5,safe (kernel+j.val) ∧ kernel+j.val<2^W)
    (incidentSpan : ∀ j:Fin 6,safe (incident+j.val) ∧ incident+j.val<2^W) :
    MotifReadCells A m safe := by
  constructor
  · intro j;rw [kernelAt,←Nat.cast_add,Fin.val_cast_of_lt (kernelSpan j).2];exact (kernelSpan j).1
  · intro j;rw [incidentAt,←Nat.cast_add,Fin.val_cast_of_lt (incidentSpan j).2];exact (incidentSpan j).1

theorem PrivateReadCells.refresh {m : Memory W} {safe : ℕ→Prop} {n h pad : ℕ}
    (mode : A.mode=.refresh n h pad) : PrivateReadCells A m safe := by
  constructor <;> intro g wrong <;> rw [mode] at wrong <;> cases wrong

theorem PrivateReadCells.of_shrink {m : Memory W} {owns : Fin 8→Prop} {issued : Fin 8→ℕ}
    {geo : Diagonal.CompressorPacking.Native.Graph.Stage} (r : PrivateSite A (geo:=geo) m owns issued)
    {safe : ℕ→Prop} (stage : ℕ) (stageAt : m (selected A m).kernel.val=(stage:Word W))
    (stageSpan : ∀ j:Fin 4,safe (stage+j.val) ∧ stage+j.val<2^W)
    (supplySpan : ∀ j:Fin 8,safe (r.supply+(8*r.row+j.val))) : PrivateReadCells A m safe := by
  constructor
  · intro g mode j;rw [stageAt,←Nat.cast_add,Fin.val_cast_of_lt (stageSpan j).2];exact (stageSpan j).1
  · intro g mode j
    have cap:=r.countsRoom
    have base : r.counts<2^W:=by omega
    have val : cutWord (((r.counts+r.row*A.histogramStride:ℕ):Word W)) (r.counts:Word W)=((r.row*A.histogramStride:ℕ):Word W) := by
      have big : ¬(((r.counts+r.row*A.histogramStride:ℕ):Word W)<(r.counts:Word W)):=by
        change ¬(_ : Word W).val<(_ : Word W).val
        rw [Fin.val_cast_of_lt cap,Fin.val_cast_of_lt base];omega
      rw [cutWord, ite_eq_right big]
      simp [Nat.cast_add]
    have part :=WordQuotients.div_at (r.row*A.histogramStride) A.histogramStride (by omega) r.strideRoom
    rw [Nat.mul_div_cancel _ r.stridePos] at part
    have room:=r.supplyRoom
    have fin : r.supply+(8*r.row+j.val)<2^W:=by have:=j.isLt;omega
    have countBase : wordAt m (m (selected A m).kernel.val) 1 = (r.counts : Word W) :=
      r.countBase
    have widthBase : wordAt m (m (selected A m).kernel.val) 3 = (r.supply : Word W) :=
      r.widthBase
    change safe (wordAt m (m (selected A m).kernel.val) 3 +
      (8 * BinaryOp.eval .div (cutWord (wordAt m (selected A m).incident 1)
        (wordAt m (m (selected A m).kernel.val) 1)) (A.histogramStride : Word W) +
        (j.val : Word W))).val
    rw [r.rowCount, countBase, widthBase, val, part]
    simpa only [←Nat.cast_ofNat (R:=Word W) (n:=8),←Nat.cast_mul,←Nat.cast_add,Fin.val_cast_of_lt fin]
      using supplySpan j


/-- For an unused motif the pointer in its zero-filled six-word record is zero.
The eager evaluator therefore probes the first eight supply words. -/
theorem PrivateReadCells.of_padded {m : Memory W} {safe : ℕ→Prop} (stage supply : ℕ)
    (stageAt : m (selected A m).kernel.val=(stage:Word W))
    (sizeAt : wordAt m (m (selected A m).kernel.val) 3=(supply:Word W))
    (empty : wordAt m (selected A m).incident 1=0)
    (stageSpan : ∀ j:Fin 4,safe (stage+j.val) ∧ stage+j.val<2^W)
    (supplySpan : ∀ j:Fin 8,safe (supply+j.val) ∧ supply+j.val<2^W) : PrivateReadCells A m safe := by
  constructor
  · intro _ _ k;rw [stageAt,←Nat.cast_add,Fin.val_cast_of_lt (stageSpan k).2];exact (stageSpan k).1
  · intro _ _ j
    let counts:=wordAt m (m (selected A m).kernel.val) 1
    have cut0 : cutWord 0 counts=0 := by
      by_cases zero : counts=0
      · simp [cutWord,zero]
      · have pos : (0:Word W)<counts:=lt_of_le_of_ne (show (0:Word W)≤counts by exact Nat.zero_le _) (Ne.symm zero)
        simp [cutWord,pos]
    have div0 : BinaryOp.eval .div (0:Word W) (A.histogramStride:Word W)=0 := by
      apply Fin.ext
      simp [BinaryOp.eval]
    change safe (wordAt m (m (selected A m).kernel.val) 3+
      (8*BinaryOp.eval .div (cutWord (wordAt m (selected A m).incident 1) counts)
        (A.histogramStride:Word W)+(j.val:Word W))).val
    rw [empty,cut0,div0,sizeAt];simpa [←Nat.cast_add,Fin.val_cast_of_lt (supplySpan j).2] using (supplySpan j).1

end EagerReads


end
end ThreeFlat.RAM.HistoryMotifJoin

end OAI
