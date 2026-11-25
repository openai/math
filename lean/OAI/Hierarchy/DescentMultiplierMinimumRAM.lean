import OAI.Hierarchy.DescentFirstMinimumRAM
import OAI.Hierarchy.DescentMultiplierSeeds

namespace OAI
/-! # The actual first minimizing field multiplier, in public coefficient order -/

namespace Hierarchy.DescentColonies.MultiplierMinimumRAM
open DescentGL DescentBinaryField DescentFirstMinimumRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

theorem mapWinner {A B : Type*} (key : A→B) (score : B→ℕ) (xs : List A) :
    (scanMinimum score (xs.map key)).1 =
      (scanMinimum (fun a=>score (key a)) xs).1.map (fun p=>(key p.1,p.2)) := by
  induction xs with
  | nil=>rfl
  | cons a xs ih=>
    simp only [List.map_cons,scanMinimum,ih]
    cases h : (scanMinimum (fun a=>score (key a)) xs).1 with
    | none=>rfl
    | some b=> by_cases better : score (key a)≤b.2 <;> simp [better]

def key {k : ℕ} (μ : Nonzero k) := (seedCode μ.val).val
def keys (k : ℕ) := (nonzeroWords k).map key

/-- Read a row by its positive coefficient index. The default is only
used for malformed words outside the enumeration. -/
def scoreAt {k : ℕ} (score : Nonzero k→ℕ) (i : ℕ) :=
  if h : 0< i ∧ i<2^k then score (seedAt k ⟨i-1,by omega⟩) else 0

theorem scoreAt_key {k : ℕ} (score : Nonzero k→ℕ) (μ : Nonzero k) :
    scoreAt score (key μ)=score μ := by
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (show μ∈List.ofFn (seedAt k) from mem_nonzeroWords μ)
  subst μ
  have range := i.isLt
  simp only [key,seedAt_code,scoreAt]
  simp [show i.val+1<2^k by omega]

theorem chosen {w out k : ℕ} (m : Memory w) (base : ℕ) (score : Nonzero k→ℕ)
    (fit : (Bank.mk base k).Fits w out) (room : out+(2^k-1)<2^w) (cap : ∀μ,score μ<2^w)
    (stored : ∀μ : Nonzero k,m (base+key μ)=(score μ:Word w))
    {μ : Nonzero k} {s : ℕ} (found : (scanMinimum score (nonzeroWords k)).1=some (μ,s)) :
    let b := Bank.mk base k
    (code w out b (keys k)).Exec m (after out b m (keys k)) (ticks out b (keys k)) ∧
      after out b m (keys k) (out+((2^k-1)-1))=(key μ:Word w) ∧
      ticks out b (keys k)≤4+70*(2^k-1) := by
  let b := Bank.mk base k
  have len : (keys k).length=2^k-1 := by simp [keys,length_nonzeroWords]
  have bound : 1<2^w := (show 1≤2^k from Nat.two_pow_pos k).trans_lt fit.2.1
  have mapped := mapWinner (@key k) (scoreAt score) (nonzeroWords k)
  simp only [scoreAt_key,found,Option.map_some] at mapped
  refine ⟨exec b m (keys k) fit (by simpa only [len] using room) bound,?_,by simpa [len] using length_budget out b (keys k)⟩
  rw [←len]
  apply winner b m (scoreAt score) (keys k) fit _ _ _ mapped
  · intro i hi
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    exact (seedCode a.val).isLt
  · intro i hi
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    simpa only [scoreAt_key] using stored a
  · intro i hi
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    simpa only [scoreAt_key] using cap a

end Hierarchy.DescentColonies.MultiplierMinimumRAM

end OAI
