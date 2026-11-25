import OAI.Hierarchy.DescentPackedProfileTape
import OAI.Hierarchy.DescentTerminalEpochChart
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Addresses and extents of the original compact verification tapes -/
namespace Hierarchy.DescentPackedProfileInstall
open DescentPackedProfileTape ProtocolRAM
noncomputable section

def sourceBank (lo seats grain : ℕ) : Bank:=⟨lo,Nat.clog 2 (slots seats grain)⟩
def startsBank (lo seats grain : ℕ) : Bank:=
  ⟨lo+(sourceBank lo seats grain).size,Nat.clog 2 (slots seats grain)⟩
def tablesBase (lo seats grain : ℕ) := (startsBank lo seats grain).base+(startsBank lo seats grain).size

end
end Hierarchy.DescentPackedProfileInstall

namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileInstall
open scoped BigOperators
noncomputable section
variable {A : Type}

def space (r : ℕ) (s : Source A) := 2*DescentDyadicSpan.span (slots s.seats r)
def extent (r : ℕ) (ss : List (Source A)) := (ss.map (space r)).sum

theorem next (lo r : ℕ) (s : Source A) : tablesBase lo s.seats r=lo+space r s := by
  simp only [tablesBase,startsBank,sourceBank,ProtocolRAM.Bank.size,space,DescentDyadicSpan.span]
  omega

theorem extent_le (r : ℕ) (ss : List (Source A)) :
    extent r ss ≤ 4*(ss.map (fun s=>slots s.seats r)).sum+2*ss.length := by
  induction ss with
  | nil=>rfl
  | cons s ss ih=>
    have h:=DescentDyadicSpan.span_le (slots s.seats r)
    change 2*DescentDyadicSpan.span (slots s.seats r)+extent r ss ≤ _
    simp only [List.map_cons,List.length_cons,List.sum_cons]
    omega

structure Shelf (A : Type) where
  src : Source A
  base : ℕ
  ordinal : ℕ

def shelves (r : ℕ) : ℕ→ℕ→List (Source A)→List (Shelf A)
  | _,_,[]=>[]
  | lo,j,s::ss=>⟨s,lo,j⟩::shelves r (lo+space r s) (j+1) ss

theorem sources (r lo j : ℕ) (ss : List (Source A)) : (shelves r lo j ss).map Shelf.src=ss := by
  induction ss generalizing lo j with
  | nil=>rfl
  | cons s ss ih=>simp [shelves,ih]

theorem placed (r lo j : ℕ) (ss : List (Source A)) (s : Shelf A) (mem : s∈shelves r lo j ss) :
    lo ≤ s.base ∧ s.base+space r s.src ≤ lo+extent r ss := by
  induction ss generalizing lo j with
  | nil=>simp [shelves] at mem
  | cons a ss ih=>
    change s∈_::_ at mem
    rcases List.mem_cons.mp mem with eqn|later
    · subst s;change lo ≤ lo ∧ lo+space r a ≤ lo+(space r a+extent r ss);omega
    · have h:=ih _ _ later
      change lo ≤ s.base ∧ s.base+space r s.src ≤ lo+(space r a+extent r ss)
      omega

end
end Hierarchy.DescentPackedEpochShelves

end OAI
