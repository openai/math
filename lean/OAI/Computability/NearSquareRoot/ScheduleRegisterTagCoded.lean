import OAI.Computability.NearSquareRoot.ScheduleRegisterTagCodedArithmetic
import OAI.Computability.NearSquareRoot.ScheduleRegisterTableEffective
import Batteries.Tactic.OpenPrivate

/-! # The numeric finite transition table for the scale selector -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleStream
open private tick from OAI.Computability.NearSquareRoot.KernelScaleStream
abbrev tagStep := @tick
end KernelScaleStream

namespace RegisterTagCoded
open IntegerMultiplication Code KernelComputableAddress
open KernelSelectorAlign (Column)

abbrev P := ℕ × ℕ × List ℕ
abbrev state (p : P) := Option (Column p.1) × (Fin p.2.1 → ZMod 2)

def step (p : P) (s : state p) (x : Column p.1) : state p :=
  KernelScaleStream.tagStep (KernelComputableSelector.test (p.1+1) p.2.1 p.2.2) s x

def seed (p : P) : state p := (none,0)
def result (p : P) (s : state p) := (packSig p.2.1 s.2).val

theorem fold_result (p : P) (xs : List (Column p.1)) :
    result p (xs.foldl (step p) (seed p)) =
      (KernelScaleStream.tag (KernelComputableSelector.test (p.1+1) p.2.1 p.2.2) xs).val := rfl

def phase (p : P) (s : state p) := s.1.elim 0 (fun u => columnRank p.1 u + 1)
def modulus (p : P) := 2^p.2.1
def stateCount (p : P) := (2^(p.1+1)+1)*modulus p
def stateRank (p : P) (s : state p) := result p s + phase p s * modulus p
def stateTree (p : P) (s : state p) := send (tally (stateRank p s))

theorem stateRank_lt (p : P) (s : state p) : stateRank p s < stateCount p := by
  have acc : result p s < modulus p := (packSig p.2.1 s.2).isLt
  have ph : phase p s < 2^(p.1+1)+1 := by
    rcases s with ⟨_ | u,v⟩
    · simp [phase]
    · simpa [phase] using columnRank_lt p.1 u
  calc
    stateRank p s < modulus p + phase p s * modulus p := Nat.add_lt_add_right acc _
    _ = (phase p s+1)*modulus p := by ring
    _ ≤ stateCount p := Nat.mul_le_mul_right _ ph

theorem stateRank_mod (p : P) (s : state p) : stateRank p s % modulus p = result p s := by
  simp [stateRank,Nat.mod_eq_of_lt (show result p s < modulus p from (packSig _ s.2).isLt)]

theorem stateRank_div (p : P) (s : state p) : stateRank p s / modulus p = phase p s := by
  have positive : 0 < modulus p := by unfold modulus; positivity
  simp [stateRank,Nat.add_mul_div_right _ _ positive,Nat.div_eq_of_lt
    (show result p s < modulus p from (packSig _ s.2).isLt)]

def tickRank (p : P) (v n : ℕ) : ℕ :=
  let acc := n % modulus p
  let ph := n / modulus p
  if ph = 0 then acc+(v+1)*modulus p
  else updateParity p.2.1 (p.2.2.getD (pairedRank p.1 (ph-1) v) 0) acc

theorem tickRank_step (p : P) (s : state p) (x : Column p.1) :
    tickRank p (columnRank p.1 x) (stateRank p s) = stateRank p (step p s x) := by
  rw [tickRank,stateRank_mod,stateRank_div]
  rcases s with ⟨_ | u,v⟩
  · rfl
  · simp only [phase,Option.elim_some,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]
    unfold result
    rw [updateParity_pack p.2.2 u x v]
    change _ = _ + 0*modulus p
    simp
    rfl

theorem seed_rank (p : P) : stateRank p (seed p) = 0 := by
  change (finFunctionFinEquiv (fun _ : Fin p.2.1 => (0 : Fin 2))).val + 0*modulus p = 0
  simp

theorem seed_tree (p : P) : stateTree p (seed p) = send (tally 0) := by simp [stateTree,seed_rank]

/-- Rows enumerate the little-endian column ordinal and the numeric automaton state. -/
def keys (p : P) : List (Column p.1 × ℕ) :=
  (List.finRange (2^(p.1+1))).flatMap fun k =>
    (List.range (stateCount p)).map (fun n => (columnUnrank p.1 k,n))

def keyTree (p : P) (v : Column p.1 × ℕ) := (send v.1).fork (send (tally v.2))
def nextTree (p : P) (v : Column p.1 × ℕ) := send (tally (tickRank p (columnRank p.1 v.1) v.2))

def table (p : P) := (keys p).map fun v => (keyTree p v,nextTree p v)

def finishTable (p : P) := (List.range (stateCount p)).map fun n =>
  (send (tally n),send (tally (n % modulus p)))

private theorem tally_injective : Function.Injective (fun n => send (tally n)) := by
  intro x y hi
  have eq := congrArg Tree.count hi
  change size (tally x) = size (tally y) at eq
  simpa [size_tally] using eq

private theorem key_injective (p : P) : Function.Injective (keyTree p) := by
  rintro ⟨v,n⟩ ⟨w,m⟩ h
  obtain ⟨one,two⟩ := Tree.fork.inj h
  exact Prod.ext (FiniteState.identify one) (tally_injective two)

private theorem lookup_key {X : Type} (key : X → Tree) (hkey : Function.Injective key)
    (out : X → Tree) (l : List X) (u : X) (hu : u ∈ l) :
    RegisterLookup.read (l.map fun v => (key v,out v)) (key u) = out u := by
  induction l with
  | nil => cases hu
  | cons v l ih =>
    by_cases e : v=u
    · simp [RegisterLookup.read,e]
    · simp [RegisterLookup.read,hkey.ne e,ih ((List.mem_cons.mp hu).resolve_left (Ne.symm e))]

theorem run_step (p : P) (s : state p) (x : Column p.1) (env : Env) (r : Deck) :
    Fits env (RegisterTable.command (table p)) (pile 0 ((send x).fork (stateTree p s)) r)
      (pile 0 (stateTree p (step p s x)) r) (RegisterTable.cost (table p)) := by
  let u := (x,stateRank p s)
  have hu : u ∈ keys p := List.mem_flatMap.mpr ⟨⟨_,columnRank_lt p.1 x⟩,List.mem_finRange _,
    List.mem_map.mpr ⟨_,List.mem_range.mpr (stateRank_lt p s),by simp [u]⟩⟩
  have tr := RegisterTable.run_lookup (table p) (keyTree p u) (nextTree p u)
    (List.mem_map.mpr ⟨u,hu,rfl⟩) (lookup_key (keyTree p) (key_injective p) (nextTree p) (keys p) u hu)
    env r
  simpa only [keyTree,nextTree,u,stateTree,tickRank_step] using tr

theorem run_finish (p : P) (s : state p) (env : Env) (r : Deck) :
    Fits env (RegisterTable.command (finishTable p)) (pile 0 (stateTree p s) r)
      (pile 0 (send (tally (result p s))) r) (RegisterTable.cost (finishTable p)) := by
  let n := stateRank p s
  have hn : n ∈ List.range (stateCount p) := List.mem_range.mpr (stateRank_lt p s)
  have h := RegisterTable.run_lookup (finishTable p) (send (tally n)) (send (tally (n%modulus p)))
    (List.mem_map.mpr ⟨n,hn,rfl⟩)
    (lookup_key _ tally_injective (fun k => send (tally (k%modulus p))) _ n hn) env r
  simpa only [n,stateTree,stateRank_mod] using h

theorem within_step {R : ℕ} (hR : 2 ≤ R) (p : P) :
    CommonRegisters.Within R (RegisterTable.command (table p)) := RegisterTable.within hR _
theorem within_finish {R : ℕ} (hR : 2 ≤ R) (p : P) :
    CommonRegisters.Within R (RegisterTable.command (finishTable p)) := RegisterTable.within hR _

end RegisterTagCoded

end NearSquareRoot
end Computability
end OAI
