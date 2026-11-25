import OAI.Hierarchy.DescentTerminalShapeData
import OAI.Hierarchy.DescentTerminalAddressInput
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Sizes of the ten physical emitter slabs and their compact literal shelves -/
namespace Hierarchy.DescentTerminalEmitter.Allocation

def reserve (s:Shape) (i f:ℕ) := 3*(s.rows+s.pool+s.leaves+i+f+1)
def power (s:Shape) (i f:ℕ) := Nat.clog 2 (reserve s i f)
def slab (s:Shape) (i f:ℕ) := 2^(power s i f)
def endAt (s:Shape) (i f base:ℕ) := base+10*slab s i f

variable (s : Shape) (i f base : ℕ)

theorem reserve_fit : reserve s i f≤ slab s i f := Nat.le_pow_clog (by decide) _

theorem slab_price : slab s i f≤2*reserve s i f := by
  cases eq:power s i f with
  | zero=>simp only [slab,eq,pow_zero];unfold reserve;omega
  | succ k=>
    have hk:k<Nat.clog 2 (reserve s i f):=by change k<power s i f;omega
    have less:=Nat.pow_lt_of_lt_clog hk
    simp only [slab,eq,pow_succ];omega

theorem price : endAt s i f base≤base+60*(s.rows+s.pool+s.leaves+i+f+1) := by
  have inv:=slab_price s i f
  unfold endAt reserve at *
  omega

end Hierarchy.DescentTerminalEmitter.Allocation

namespace Hierarchy.DescentTerminalEmitter.Compact
open scoped Classical BigOperators
noncomputable section

def need : Column → ℕ
  | .attained _=>0
  | .literal n=>n

def size : Column → ℕ
  | .attained _=>0
  | .literal n=>2^(Nat.clog 2 n)

def wordsBought (c : Columns) := ∑j,size (c j)
def shelfEnd (base : ℕ) (c : Columns) := base+wordsBought c
def flightEnd (base : ℕ) (c : Columns) (flightWords : ℕ) := shelfEnd base c+flightWords

theorem invoice (c : Columns) : wordsBought c≤2*(∑j,need (c j))+43 := by
  have each (j : Fin 43) : size (c j)≤2*need (c j)+1 := by
    cases h:c j with
    | attained b=>simp [size,need]
    | literal n=>
      change 2^(Nat.clog 2 n)≤2*n+1
      cases eq:Nat.clog 2 n with
      | zero=>simp
      | succ k=>
        have lt:k<Nat.clog 2 n:=by omega
        have :=Nat.pow_lt_of_lt_clog lt
        rw [pow_succ]
        omega
  calc
    wordsBought c ≤ ∑j:Fin 43, (2*need (c j)+1) := Finset.sum_le_sum (fun j _=>each j)
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]

variable (base : ℕ) (c : Columns) (s : Shape) (i f flightWords : ℕ)
local notation "start" => flightEnd base c flightWords
local notation "slabs" => Allocation.endAt s i f start

theorem price :
    slabs≤base+2*(∑j,need (c j))+43+flightWords+60*(s.rows+s.pool+s.leaves+i+f+1) := by
  apply (Allocation.price s i f start).trans
  change base+wordsBought c+flightWords+60*(s.rows+s.pool+s.leaves+i+f+1) ≤ _
  have table := invoice c
  omega

end
end Hierarchy.DescentTerminalEmitter.Compact

end OAI
