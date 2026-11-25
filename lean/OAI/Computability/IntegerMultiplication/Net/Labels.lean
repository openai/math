import OAI.Computability.IntegerMultiplication.Net.Bank
import OAI.Computability.IntegerMultiplication.Net.Wiring

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Motif
open Finset
/-- Frame names. In the bit shear construction the opening label additionally
 carries a negative sign (edge change counted with surcharge). -/
inductive Place (T : Type)
| opening (a : Keys T)
| box (past : ℕ) (a : Keys T)
| ybox (past : ℕ) (a : Keys T)
| low (j : S) (p : Sub T)
| leanOn (j : S) (p : Sub T) (t : T)
| high (j : S) (p : Sub T)
| full
| clear
deriving DecidableEq

namespace Place
variable {T : Type}
def charge (h : ℤ) : Place T → ℤ
| .opening _ => 1
| .box b _ => h^b
| .ybox b _ => h^b-1
| .low j _ => h^(j.val+1)-h
| .leanOn j _ _ => h^(j.val+1)-h+1
| .high j _ => h^(j.val+1)
| .full => h^3
| .clear => 0
def isOp : Place T → Bool
| .opening _ => true
| _ => false
/-- count bound. Charge an extra one leaving a negative source. -/
def allowance (h : ℤ) (u v : Place T) : ℤ :=
  |charge h v - charge h u| +
  if isOp u && !(isOp v) then 1 else 0
@[simp] theorem stay_allowance (h : ℤ) (u : Place T) : allowance h u u = 0 := by simp [allowance]

def xEntry (n : ℕ) (a : Keys T) : Place T := if n = 0 then opening a else box n a

/-- permitted changes, for extracting the edge interface later. -/
inductive road (adj : T → T → Prop) : Place T → Place T → Prop where
| still l : road adj l l
| entry j p t :
    road adj (xEntry j.val (fill j p t)) (.leanOn j p t)
| fromY j p t : road adj (.ybox j.val (fill j p t)) (.low j p)
| sideStart j p t : road adj .clear (.ybox j.val (fill j p t))
| side0 j p s t (e : adj t s) : road adj (.ybox j.val (fill j p s)) (.leanOn j p t)
| centerStart j p : road adj .clear (.low j p)
| centerGo j p : road adj (.low j p) (.high j p)
| centerDrop j p : road adj (.high j p) (.low j p)
| growX j p t : road adj (.leanOn j p t) (.high j p)
| growY j p t : road adj (.low j p) (.ybox (j.val+1) (fill j p t))
| core j p t u (e : adj t u) :
    road adj (.leanOn j p t) (.ybox (j.val+1) (fill j p u))
| sideDone j p t : road adj (.ybox (j.val+1) (fill j p t)) (.high j p)
| finishX j p t : road adj (.high j p) (.box (j.val+1) (fill j p t))
| finishQ j p : road adj (.high j p) .full
| skip : road adj .clear .full

-- side0 ybox(s)->lean(t) needs simultaneous basis of TWO pinned lines s,t!!!
-- only neighbor, add e argument.
end Place
end Net.Motif

end IntegerMultiplication
end Computability
end OAI
