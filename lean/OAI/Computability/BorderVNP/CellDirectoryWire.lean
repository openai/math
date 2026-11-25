import OAI.Computability.BorderVNP.CellSparse
import OAI.Computability.BorderVNP.CellRecordScan
import Mathlib.Data.Nat.Bits

/-! # Typed sparse packets at the team-to-private boundary

Lists are prefixed by their numbers of entries. All natural fields are binary
records. Box contents occur once in the directory, independent of the number
of times or copies in which a box is visited. External wire values occupy a
separate private input stack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

/-- Length followed by the concatenation of the elements' word sequences. -/
def fieldList {α : Type} (enc : α → List ℕ) (xs : List α) : List ℕ :=
  xs.length :: xs.flatMap enc

/-- Three word fields for a possibly strided assignment-bank port. -/
def port (p : Port) : List ℕ := [p.base,p.copyStride,p.laneStride]

/-- One profile route uses two scalar fields and two ports. -/
def route (r : Route) : List ℕ := [r.term,r.lanes] ++ port r.original ++ port r.compact

/-- One length-prefixed vector of scalar words. -/
def vector (xs : List ℕ) : List ℕ := xs.length :: xs

/-- Tagged representation of one private factor, including its one-copy table. -/
def factor : Factor → List ℕ
  | .truth ws rs => [0] ++ vector ws ++ vector (rs.map Bool.toNat)
  | .sign ws rs => [1] ++ vector ws ++ vector (rs.map Bool.toNat)
  | .gadget ws rs => [2] ++ vector ws ++ vector rs
  | .unary i p => [3,i] ++ port p

/-- Tagged representation of a public sparse record. -/
def record : Record → List ℕ
  | .zero c l p => [0,c,l] ++ port p
  | .equal c l p q => [1,c,l] ++ port p ++ port q
  | .box id base c stride => [2,id,base,c,stride]
  | .profile c p w hist rs => [3,c] ++ port p ++ [w] ++ vector hist ++ fieldList route rs

/-- Complete compact word input to the private evaluator. -/
def words (D : Directory) (privateWires : ℕ) : List ℕ :=
  [privateWires] ++ fieldList (fieldList factor) D.boxes ++ fieldList record D.records ++
    fieldList vector D.reportedCounts

/-- Actual bit framing consumed by the private stack machine. -/
def bits (D : Directory) (privateWires : ℕ) : List Bool :=
  CellMacro.Generator.records ((words D privateWires).map Nat.bits)

/-- The single packed burst delimits the typed packet and leaves external
assignment bits in their physical stack order. -/
def input (D : Directory) (privateWires : ℕ) (external : List Bool) : List Bool :=
  RationalHitting.StackLanguage.codeWord (bits D privateWires) ++ external

/-- A word parser may consume a prefix and return the untouched suffix. -/
abbrev Parser (α : Type) := List ℕ → Option (α × List ℕ)

/-- Read a scalar from the stream. -/
def scalar : Parser ℕ
  | [] => none
  | x::xs => some (x,xs)

/-- Run an element parser exactly the indicated number of times. -/
def many {α : Type} (p : Parser α) : ℕ → Parser (List α)
  | 0, xs => some ([],xs)
  | n+1, xs => do
    let (a,xs) ← p xs
    let (as,xs) ← many p n xs
    return (a::as,xs)

/-- Parse a length-prefixed list without consuming following fields. -/
def list {α : Type} (p : Parser α) : Parser (List α) := fun xs => do
  let (n,xs) ← scalar xs
  many p n xs

private theorem many_append {α : Type} (enc : α → List ℕ) (p : Parser α)
    (h : ∀ a rest, p (enc a ++ rest) = some (a,rest)) (as : List α) (rest : List ℕ) :
    many p as.length (as.flatMap enc ++ rest) = some (as,rest) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [many, List.append_assoc, h, ih]

/-- Exact prefix/suffix behavior of a framed list parser. -/
theorem list_append {α : Type} (enc : α → List ℕ) (p : Parser α)
    (h : ∀ a rest, p (enc a ++ rest) = some (a,rest)) (as : List α) (rest : List ℕ) :
    list p (fieldList enc as ++ rest) = some (as,rest) := by
  simpa [list,fieldList,scalar] using many_append enc p h as rest

private theorem vector_append (xs rest : List ℕ) :
    list scalar (vector xs ++ rest) = some (xs,rest) := by
  simpa [fieldList,vector] using list_append (fun a : ℕ => [a]) scalar (fun _ _ => rfl) xs rest

/-- Decode a three-word port. -/
def readPort : Parser Port
  | a::b::c::xs => some (⟨a,b,c⟩,xs)
  | _ => none

private theorem port_append (p : Port) (rest : List ℕ) : readPort (port p ++ rest) = some (p,rest) := rfl

/-- Decode both ports and scalar fields of a route. -/
def readRoute : Parser Route
  | t::l::xs => do
    let (p,xs) ← readPort xs
    let (q,xs) ← readPort xs
    return (⟨t,l,p,q⟩,xs)
  | _ => none

private theorem route_append (r : Route) (rest : List ℕ) : readRoute (route r ++ rest) = some (r,rest) := by
  simp [readRoute, route, List.append_assoc, port_append]

private def booleans (xs : List ℕ) : Option (List Bool) :=
  xs.mapM fun x => if x = 0 then some false else if x = 1 then some true else none

private theorem booleans_map (xs : List Bool) : booleans (xs.map Bool.toNat) = some xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [booleans] at ih ⊢ <;> rw [ih] <;> rfl

/-- Reject unknown factor tags and Boolean rows with non-Boolean scalar words. -/
def readFactor : Parser Factor
  | 0::xs => do
    let (ws,xs) ← list scalar xs
    let (rs,xs) ← list scalar xs
    return (.truth ws (← booleans rs),xs)
  | 1::xs => do
    let (ws,xs) ← list scalar xs
    let (rs,xs) ← list scalar xs
    return (.sign ws (← booleans rs),xs)
  | 2::xs => do
    let (ws,xs) ← list scalar xs
    let (rs,xs) ← list scalar xs
    return (.gadget ws rs,xs)
  | 3::i::xs => do
    let (p,xs) ← readPort xs
    return (.unary i p,xs)
  | _ => none

private theorem factor_append (f : Factor) (rest : List ℕ) : readFactor (factor f ++ rest) = some (f,rest) := by
  cases f <;> simp [readFactor,factor,List.append_assoc,vector_append,booleans_map,port_append]

/-- Decode a sparse record and retain all following words. -/
def readRecord : Parser Record
  | 0::c::l::xs => do
    let (p,xs) ← readPort xs
    return (.zero c l p,xs)
  | 1::c::l::xs => do
    let (p,xs) ← readPort xs
    let (q,xs) ← readPort xs
    return (.equal c l p q,xs)
  | 2::id::base::c::stride::xs => some (.box id base c stride,xs)
  | 3::c::xs => do
    let (p,xs) ← readPort xs
    let (w,xs) ← scalar xs
    let (hist,xs) ← list scalar xs
    let (rs,xs) ← list readRoute xs
    return (.profile c p w hist rs,xs)
  | _ => none

private theorem record_append (r : Record) (rest : List ℕ) : readRecord (record r ++ rest) = some (r,rest) := by
  cases r <;> simp [readRecord,record,List.append_assoc,port_append,scalar,vector_append,list_append route _ route_append]

/-- Decode the public row stream, private one-copy descriptions, and reported
subtotal addresses. A well-formed packet has no trailing words. -/
def parse : List ℕ → Option (ℕ × Directory) := fun xs => do
  let (priv,xs) ← scalar xs
  let (boxes,xs) ← list (list readFactor) xs
  let (rs,xs) ← list readRecord xs
  let (reports,xs) ← list (list scalar) xs
  if xs.isEmpty then return (priv,⟨boxes,rs,reports⟩) else none

/-- The parser recovers the complete original directory, with all offsets and multiplicities. -/
theorem parse_words (D : Directory) (priv : ℕ) : parse (words D priv) = some (priv,D) := by
  have hbox := list_append factor readFactor factor_append
  have h1 := list_append (fieldList factor) (list readFactor) hbox D.boxes
  have h2 := list_append record readRecord record_append D.records
  have h3 := list_append vector (list scalar) vector_append D.reportedCounts []
  simp [parse,words,List.append_assoc,scalar,h1,h2] at *
  exact h3 ▸ rfl

end CellSparse.Packet

end BorderVNP
end Computability
end OAI
