import Mathlib.Data.List.OfFn
import Mathlib.Tactic

namespace OAI
/-! # The shared interpretation of an affine operand in whole-payload units -/

namespace Hierarchy.DescentBundleHistory
structure SliceCode where
  start : ℕ
  stride : ℕ
  count : ℕ
deriving DecidableEq

/-- One local table word may depend on several consecutive physical words.
The code contains just the offset, stride and number of named words. -/
def SliceCode.eval (p : ℕ) (s : SliceCode) (ws : List (List Bool)) := List.ofFn fun d : Fin p=>
  let t := s.start+s.stride*d.val
  (ws.getD (t/p) []).getD (t%p) false

def rowCount (s : List SliceCode) := (s.map SliceCode.count).sum

def evalRow (p : ℕ) : List SliceCode→List (List Bool)→List Bool
  | [],_=>[]
  | s::ss,ws=>(s.eval p (ws.take s.count))++evalRow p ss (ws.drop s.count)

def evalRows (p : ℕ) : List (List SliceCode)→List (List Bool)→List (List Bool)
  | [],_=>[]
  | s::ss,ws=>evalRow p s (ws.take (rowCount s)) :: evalRows p ss (ws.drop (rowCount s))

def bundleScalar {U K : Type} (p : ℕ) (dict : U→List (List Bool)→K)
    (code : U×List (List SliceCode)) (ws : List (List Bool)) : K := dict code.1 (evalRows p code.2 ws)

variable {α β : Type} (read : α→List Bool) (name : β→SliceCode) (args : β→List α)
variable (honest : ∀s,(args s).length=(name s).count)
include honest

theorem rowCount_true (xs : List β) : rowCount (xs.map name)=(xs.flatMap args).length := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    change (name x).count+rowCount (xs.map name)=(args x++xs.flatMap args).length
    rw [List.length_append,ih,honest x]

theorem evalRow_true (p : ℕ) (xs : List β) :
    evalRow p (xs.map name) ((xs.flatMap args).map read)=
      xs.flatMap (fun x=>(name x).eval p ((args x).map read)) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.map_cons,List.flatMap_cons,List.map_append,evalRow]
    rw [←honest x,←List.length_map (as:=args x) read]
    simp [ih]

theorem evalRows_true (p : ℕ) (xs : List (List β)) :
    evalRows p (xs.map (List.map name)) ((xs.flatMap (List.flatMap args)).map read)=
      xs.map (fun row=>row.flatMap (fun x=>(name x).eval p ((args x).map read))) := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.map_cons,List.flatMap_cons,List.map_append,evalRows]
    rw [rowCount_true name args honest x,←List.length_map (as:=x.flatMap args) read]
    simp [evalRow_true read name args honest,ih]
end Hierarchy.DescentBundleHistory

end OAI
