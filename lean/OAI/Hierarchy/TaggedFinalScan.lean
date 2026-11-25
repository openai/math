import OAI.Hierarchy.TaggedFinalRows
import OAI.Hierarchy.TaggedScan
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn

namespace OAI
/-! # The final flagged-pair scan through padded rows

Each column remembers the value of the preceding real source. Dummies do not
advance the parser. The scan accepts exactly alternating source and target
records with equal words, and costs linearly in rows times word width.
-/

namespace Hierarchy.Tagged.FinalScan
open ThreeFlat Routing
open scoped BigOperators Classical
noncomputable section

inductive State (α : Type*) where
  | failed
  | ready
  | pending (a : α)
  deriving DecidableEq

def take {α : Type*} [DecidableEq α] : State α → Bool × α → State α
  | .failed, _ => .failed
  | .ready, (target,v) => if target then .failed else .pending v
  | .pending v, (target,u) => if target && decide (u = v) then .ready else .failed

private theorem failed {α : Type*} [DecidableEq α] (xs : List (Bool × α)) :
    xs.foldl take .failed = State.failed := by induction xs <;> simp [*, take]

theorem accepts_iff {α : Type*} [DecidableEq α] (xs : List (Bool × α)) :
    xs.foldl take .ready = State.ready ↔ paired xs := by
  match xs with
  | [] => simp [paired]
  | [(f,x)] => cases f <;> simp [paired,take]
  | (f,x)::(g,y)::rest =>
    have ih := accepts_iff rest
    cases f <;> cases g <;> by_cases eq : x = y <;> simp [paired, take, eq, eq_comm, failed]
    exact eq_comm.trans ih

private def encode : State Bool → Fin 3 → Bool
  | .failed => ![false,false,false]
  | .ready => ![true,false,false]
  | .pending b => ![true,true,b]
private def decode (s : Fin 3 → Bool) : State Bool :=
  if s 0 then if s 1 then .pending (s 2) else .ready else .failed
private theorem decode_encode (s : State Bool) : decode (encode s) = s := by cases s <;> rfl

private def trans (s x : Fin 3 → Bool) : Fin 3 → Bool :=
  encode (if x 0 then take (decode s) (x 1,x 2) else decode s)

abbrev Fields (w : ℕ) := Option (Option (Fin w))
abbrev Ports (n w : ℕ) := Fin n × Fields w

def rows {n w : ℕ} (x : Ports n w → Bool) : List (Bool × (Fin w → Bool)) :=
  (List.ofFn (fun i : Fin n => i)).filterMap fun i =>
    if x (i,none) then some (x (i,some none),fun j => x (i,some (some j))) else none

private def field {w : ℕ} (j : Fin w) : Fin 3 → Fields w := ![none,some none,some (some j)]
private def one (F : Type*) [Zero F] [One F] (n : ℕ) : BitNetwork F (Fintype.card (Scan.Ports n 3)) :=
  Scan.network F (encode .ready) (fun _ => trans) (fun s => decode s = .ready)

def network (F : Type*) [Zero F] [One F] (n w : ℕ) : BitNetwork F (Fintype.card (Ports n w)) :=
  TypedWiring.glue (fun _ : Fin w => one F n) (fun j (k : Scan.Ports n 3) =>
    (Sum.inl (k.1,field j k.2) : Ports n w ⊕ Empty))

private def bitRows {n : ℕ} (x : Scan.Ports n 3 → Bool) : List (Bool × Bool) :=
  (List.ofFn (id : Fin n → Fin n)).filterMap fun i => if x (i,0) then some (x (i,1),x (i,2)) else none

private theorem trace_cons {n : ℕ} (x : Scan.Ports n 3 → Bool) (i : Fin (n+1)) :
    Scan.run (encode .ready) (fun _ => trans) x i = encode
      (((List.ofFn (fun j : Fin i.val => (⟨j.val,lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)⟩ : Fin n))).filterMap
        (fun j => if x (j,0) then some (x (j,1),x (j,2)) else none)).foldl take .ready) := by
  induction i using Fin.induction with
  | zero => simp [Scan.run]
  | succ i ih =>
    rw [show Scan.run (encode .ready) (fun _ => trans) x i.succ =
      trans (Scan.run (encode .ready) (fun _ => trans) x i.castSucc) (fun j => x (i,j)) by simp [Scan.run], ih]
    simp only [Fin.val_succ, List.ofFn_succ', List.concat_eq_append, List.filterMap_append,
      List.foldl_append]
    cases real : x (i,0) <;> simp [trans, decode_encode, real, List.filterMap]

private theorem one_value (F : Type*) [CommSemiring F] {n : ℕ} (x : Scan.Ports n 3 → Bool) :
    TypedWiring.value (one F n) x = if paired (bitRows x) then 1 else 0 := by
  rw [one, Scan.eval, trace_cons, decode_encode, accepts_iff]
  rfl

private theorem project {n w : ℕ} (x : Ports n w → Bool) (j : Fin w) :
    bitRows (fun k : Scan.Ports n 3 => x (k.1, field j k.2)) =
      (rows x).map (fun p => (p.1,p.2 j)) := by
  unfold bitRows rows
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro i _
  cases h : x (i,none) <;> simp [field,h]

private theorem columns {w : ℕ} (hw : 0 < w) (xs : List (Bool × (Fin w → Bool))) :
    (∀ j, paired (xs.map fun p => (p.1,p.2 j))) ↔ paired xs := by
  match xs with
  | [] => simp [paired]
  | [a] => simp [paired, Fin.pos_iff_nonempty.mp hw]
  | a::b::xs =>
    have ih := columns hw xs
    simp only [List.map_cons, paired]
    constructor
    · intro h
      let j : Fin w := ⟨0,hw⟩
      exact ⟨(h j).1,(h j).2.1,funext (fun i => (h i).2.2.1),ih.mp (fun i => (h i).2.2.2)⟩
    · rintro ⟨fa,fb,eq,rest⟩ j
      exact ⟨fa,fb,congrFun eq j,(ih.mpr rest) j⟩

theorem eval (F : Type*) [CommSemiring F] {n w : ℕ} (hw : 0 < w) (x : Ports n w → Bool) :
    TypedWiring.value (network F n w) x = if paired (rows x) then 1 else 0 := by
  simp only [network, TypedWiring.glue_value, Fintype.sum_unique, Sum.elim_inl,
    one_value, project, Fintype.prod_boole, columns hw]

theorem size (F : Type*) [Zero F] [One F] (n w : ℕ) :
    (network F n w).cells+(network F n w).internal ≤ 11000*w*(n+2) := by
  have cost := Scan.size F (n := n) (encode .ready) (fun _ => trans) (fun s => decode s = .ready)
  change (one F n).cells+(one F n).internal = _ at cost
  simp only [network, TypedWiring.glue_cells, TypedWiring.glue_internal, Fintype.card_empty,
    Nat.zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Nat.mul_add]
  rw [cost]
  norm_num
  ring_nf
  omega

end
end Hierarchy.Tagged.FinalScan

end OAI
