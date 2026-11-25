import OAI.Hierarchy.ProbePathScan
import Mathlib.Data.List.ReduceOption
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Padded depth-first enumeration of sampler chains on row ports -/

namespace Hierarchy.ProtocolRAM.PurchaseDFS

open AdaptiveProbe

variable {n D : ℕ}

/-- Fixed-length digit words, with the first digit as the outermost loop. -/
def words (D : ℕ) : (h : ℕ) → List (Fin h → Fin D)
  | 0 => [Fin.elim0]
  | h+1 => (List.finRange D).flatMap fun d => (words D h).map (Fin.cons d)

theorem mem_words (D : ℕ) {h : ℕ} (z : Fin h → Fin D) : z ∈ words D h := by
  induction h with
  | zero => exact List.mem_singleton.mpr (funext fun i => i.elim0)
  | succ h ih =>
    exact List.mem_flatMap.mpr ⟨z 0, List.mem_finRange _,
      List.mem_map.mpr ⟨Fin.tail z, ih _, Fin.cons_self_tail z⟩⟩

/-- One port lookup per digit. A missing port kills its full continuation. -/
def walk (choice : Fin n → Fin D → Option (Fin n)) (start : Fin n) :
    {h : ℕ} → (Fin h → Fin D) → Option (List (Fin n))
  | 0, _ => some [start]
  | h+1, z => (choice start (z 0)).bind fun y =>
      (walk choice y (h := h) (fun i => z i.succ)).map (start :: ·)

@[simp] theorem walk_cons (choice : Fin n → Fin D → Option (Fin n)) (x : Fin n)
    {h : ℕ} (d : Fin D) (z : Fin h → Fin D) :
    walk choice x (Fin.cons d z) = (choice x d).bind fun y => (walk choice y z).map (x :: ·) := by
  simp [walk, Fin.cons_zero, Fin.cons_succ]

/-- All visited port states, including a sentinel at every depth after a missing port. -/
def optionStates (choice : Fin n → Fin D → Option (Fin n)) (x : Option (Fin n)) :
    List (Fin D) → List (Option (Fin n))
  | [] => [x]
  | d :: ds => x :: optionStates choice (x.bind (fun v => choice v d)) ds

@[simp] theorem length_optionStates (choice : Fin n → Fin D → Option (Fin n))
    (x : Option (Fin n)) (ds : List (Fin D)) : (optionStates choice x ds).length = ds.length+1 := by
  induction ds generalizing x <;> simp [optionStates, *]

private theorem mapM_optionStates_none (choice : Fin n → Fin D → Option (Fin n)) (ds : List (Fin D)) :
    (optionStates choice none ds).mapM id = none := by
  cases ds <;> simp [optionStates, List.mapM_cons]

/-- A word decodes to a live path exactly by sequencing its visited physical optional states. -/
theorem optionStates_walk (choice : Fin n → Fin D → Option (Fin n)) (x : Fin n)
    {h : ℕ} (z : Fin h → Fin D) :
    (optionStates choice (some x) (List.ofFn z)).mapM id = walk choice x z := by
  induction h generalizing x with
  | zero => simp [optionStates,walk]
  | succ h ih =>
    rw [List.ofFn_succ,optionStates,List.mapM_cons,walk]
    cases e : choice x (z 0) with
    | none => simp [e,mapM_optionStates_none]
    | some y =>
      cases ew : walk choice y (fun i => z i.succ) <;> simp [e,ih,ew]

/-- The outer scan visits every physical starting row in numerical order. -/
def layout (n D h : ℕ) : List (Fin n × (Fin h → Fin D)) :=
  (List.finRange n).flatMap fun v => (words D h).map (Prod.mk v)

theorem mem_layout (x : Fin n) {h : ℕ} (z : Fin h → Fin D) : (x,z) ∈ layout n D h :=
  List.mem_flatMap.mpr ⟨x, List.mem_finRange _, List.mem_map.mpr ⟨z,mem_words D z,rfl⟩⟩

def padded (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) : List (Option (List (Fin n))) :=
  (layout n D h).map fun z => walk choice z.1 z.2

/-- The adjacency list suppresses empty ports but preserves the order of all live digits. -/
def next (choice : Fin n → Fin D → Option (Fin n)) (v : Fin n) : List (Fin n) :=
  (List.ofFn (choice v)).reduceOption

private theorem length_flatMap_const {α β : Type*} (xs : List α) (f : α → List β) (k : ℕ)
    (len : ∀ x, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [len, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem length_words (D h : ℕ) : (words D h).length = D ^ h := by
  induction h with
  | zero => simp [words]
  | succ h ih =>
    rw [words, length_flatMap_const _ _ (D ^ h) (fun d => by simp [ih])]
    simp [pow_succ, Nat.mul_comm]

@[simp] theorem length_layout (n D h : ℕ) : (layout n D h).length = n * D^h := by
  rw [layout, length_flatMap_const _ _ (D ^ h) (fun v => by simp)]
  simp

@[simp] theorem length_padded (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) :
    (padded choice h).length = n * D^h := by simp [padded]

private theorem reduce_map {α β γ : Type*} (xs : List α) (f : α → Option β) (g : β → γ) :
    (xs.map (fun x => (f x).map g)).reduceOption = (xs.map f).reduceOption.map g := by
  exact (congrArg List.reduceOption (List.map_map (g := Option.map g) (f := f) (l := xs))).symm.trans
    List.reduceOption_map

private theorem reducedLevel (choice : Fin n → Fin D → Option (Fin n)) (x : Fin n) (h : ℕ)
    (ds : List (Fin D)) :
    (ds.flatMap fun d => (words D h).map (fun z => walk choice x (Fin.cons d z))).reduceOption =
    (ds.filterMap (choice x)).flatMap (fun y => ((words D h).map (walk choice y)).reduceOption.map (x :: ·)) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [List.flatMap_cons, List.reduceOption_append, ih]
    cases hd : choice x d with
    | none => simp [hd, walk_cons]
    | some y => simp [hd, walk_cons, reduce_map]

/-- Erasing only dead leaves recovers the ordinary DFS at each starting row, as an ordered list. -/
theorem reduce_walks (choice : Fin n → Fin D → Option (Fin n)) (x : Fin n) (h : ℕ) :
    ((words D h).map (walk choice x)).reduceOption = paths (next choice) x h := by
  induction h generalizing x with
  | zero => simp [words,walk,paths]
  | succ h ih =>
    simp only [words, List.map_flatMap, List.map_map, Function.comp_def, reducedLevel, ih, paths]
    simp [next, List.ofFn_eq_map, List.reduceOption, List.filterMap_map]

/-- The complete live DFS is the numerical-row concatenation of ordinary paths. -/
theorem reduce_padded (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) :
    (padded choice h).reduceOption = (List.finRange n).flatMap fun x => paths (next choice) x h := by
  simp only [padded, layout, List.map_flatMap, List.map_map, Function.comp_def]
  change List.filterMap id _ = _
  rw [List.filterMap_flatMap]
  apply List.flatMap_congr
  intro x _
  exact reduce_walks choice x h

/-- The valid distinct candidates are independent of the marked subset being scanned. -/
def candidates (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) : List (List (Fin n)) :=
  (padded choice h).reduceOption.filter (fun p => decide p.Nodup)

/-- The per-word decision used by a padded row machine recovers the exact scan list. -/
theorem candidates_eq_filterMap (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) :
    candidates choice h = (layout n D h).filterMap (fun z =>
      (walk choice z.1 z.2).filter fun p => decide p.Nodup) := by
  simp only [candidates, padded, List.reduceOption, List.filterMap_map, Function.comp_def,
    id_eq, List.filter_filterMap]

theorem mem_candidates (choice : Fin n → Fin D → Option (Fin n)) {h : ℕ} {p : List (Fin n)} :
    p ∈ candidates choice h ↔ p.length = h+1 ∧ p.Nodup ∧ p.IsChain (fun a b => b ∈ next choice a) := by
  rw [candidates, reduce_padded, List.mem_filter]
  constructor
  · rintro ⟨hm, dist⟩
    obtain ⟨x,_,member⟩ := List.mem_flatMap.mp hm
    obtain ⟨t,rfl,len,c⟩ := (paths_spec _ _ _ _).mp member
    exact ⟨by simp [len], of_decide_eq_true dist, c⟩
  · rintro ⟨lh,nd,chain⟩
    cases p with
    | nil => simp at lh
    | cons v tail =>
      exact ⟨List.mem_flatMap.mpr ⟨v,List.mem_finRange v,(paths_spec _ _ _ _).mpr
        ⟨tail,rfl,by simpa using lh,chain⟩⟩,decide_eq_true nd⟩

/-- Purchasing from any signed stratum gives pairwise-disjoint paths, a maximal residue,
and an exact account of every originally marked row. -/
theorem purchase_spec (choice : Fin n → Fin D → Option (Fin n)) (h : ℕ) (left : Finset (Fin n)) :
    let ps := candidates choice h
    let result := scanPaths ps left
    (∀ p∈ps, ¬p.toFinset ⊆ result.2) ∧
      result.1.Pairwise (fun p q => Disjoint p.toFinset q.toFinset) ∧
      result.1.length * (h+1) + result.2.card = left.card := by
  dsimp only
  have good := fun p (hp : p ∈ candidates choice h) => (mem_candidates choice).mp hp
  exact ⟨scan_maximal _ left (fun p hp hn => by have len := (good p hp).1; simp [hn] at len),
    (scan_disjoint _ left).2, scan_account _ _ left (fun p hp => ⟨(good p hp).1,(good p hp).2.1⟩)⟩

/-- The physical scan finds every sampler witness, including when live output digits have gaps. -/
theorem purchase_residue (choice : Fin n → Fin D → Option (Fin n)) (h a : ℕ) (ha : 0 < a)
    (mix : SamplerMixes (fun i j => j ∈ next choice i) a) (left : Finset (Fin n)) :
    (scanPaths (candidates choice h) left).2.card < (h+1)*(2*a) := by
  apply remaining_tiles_lt a (h+1) ha (Nat.succ_pos _) mix
  intro f inside path
  let p := List.ofFn f
  have chain : p.IsChain (fun x y => y ∈ next choice x) := by
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have bound : i+1<h+1 := by simpa [p] using hi
    simpa only [p, List.getElem_ofFn] using path i bound
  have member : p ∈ candidates choice h := (mem_candidates choice).mpr
    ⟨by simp [p], List.nodup_ofFn.mpr f.injective, chain⟩
  apply (purchase_spec choice h left).1 p member
  intro i hi
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp hi)
  exact inside j


end Hierarchy.ProtocolRAM.PurchaseDFS

end OAI
