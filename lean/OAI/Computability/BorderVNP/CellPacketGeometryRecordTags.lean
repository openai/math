import OAI.Computability.BorderVNP.PackedFrozenTapeRows
import OAI.Computability.BorderVNP.CellPacketGeometryBankPlaced

/-! # Recovering the immutable public row format from its relocation tags -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankPacket.Stored

open Inherited CellSparse Word
open private plain port route from OAI.Computability.BorderVNP.PackedInheritedFields

/-- Public constructor and fixed arities of the canonical compact record. -/
inductive Shape where
  | zero | equal | box
  | profile (hist routes : ℕ)
  deriving DecidableEq

/-- Shape of the actual mathematical row, with histogram and route arities. -/
def shape : Record → Shape
  | .zero .. => .zero
  | .equal .. => .equal
  | .box .. => .box
  | .profile _ _ _ h rs => .profile h.length rs.length

private def routeTags : List Kind := [.plain,.plain,.bitAddress,.plain,.plain,.bitAddress,.plain,.plain]

/-- There is one address at the selector and two per route in a profile.
All other public scalar roles, including histogram entries, are immutable. -/
def Shape.tags : Shape → List Kind
  | .zero => [.plain,.plain,.plain,.bitAddress,.plain,.plain]
  | .equal => [.plain,.plain,.plain,.bitAddress,.plain,.plain,.bitAddress,.plain,.plain]
  | .box => [.plain,.boxID,.bitAddress,.plain,.plain]
  | .profile h r => [.plain,.plain,.bitAddress,.plain,.plain,.plain,.plain] ++
      List.replicate h .plain ++ [.plain] ++ (List.replicate r routeTags).flatten

private theorem route_tags (r : Route) : (route r).map Prod.fst = routeTags := rfl

/-- The previously verified frozen-site scalar annotation is exactly this fixed format. -/
theorem marked_tags (r : Record) : (marked r).map Prod.fst = (shape r).tags := by
  cases r with
  | zero | equal | box => rfl
  | profile n p w h rs =>
    have routes : (rs.flatMap route).map Prod.fst = (List.replicate rs.length routeTags).flatten := by
      simp only [List.map_flatMap,route_tags]
      rw [List.flatMap_def]
      simp
    simp [marked,shape,Shape.tags,List.map_append,plain,port,List.map_map,Function.comp_def,routes]

private theorem route_count (n : ℕ) :
    (List.replicate n routeTags).flatten.count Kind.bitAddress = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,List.count_append,ih]
    change 2+2*n = 2*(n+1)
    omega

private theorem plain_count (n : ℕ) : (List.replicate n Kind.plain).count Kind.bitAddress = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,List.count_cons]
    exact ih

/-- One public format decoder, evaluated only on the immutable relocation
tags. It does not inspect any numerical operands, including private strings. -/
def decodeShape (tags : List Kind) : Shape :=
  if tags[1]? = some .boxID then .box
  else if tags[2]? = some .bitAddress then
    let r := (tags.count .bitAddress-1)/2
    .profile (tags.length-8-8*r) r
  else if tags.length=6 then .zero else .equal

/-- Every legal canonical sparse format is decoded correctly, including empty
histograms and empty route lists. -/
theorem decode_tags (s : Shape) : decodeShape s.tags = s := by
  cases s with
  | zero | equal | box => rfl
  | profile h r =>
    let ts := (Shape.profile h r).tags
    have len : ts.length = 8+h+8*r := by simp [ts,Shape.tags,routeTags,Nat.mul_comm]; omega
    have count : ts.count .bitAddress = 1+2*r := by
      simp only [ts,Shape.tags,List.count_append,plain_count,route_count]
      rfl
    have first : ts[1]? = some .plain := rfl
    have third : ts[2]? = some .bitAddress := rfl
    change decodeShape ts = _
    rw [decodeShape]
    simp only [first,third,reduceCtorEq,Option.some.injEq,ite_false,ite_true,count,len]
    congr 1 <;> omega

end Packing.BankPacket.Stored

end BorderVNP
end Computability
end OAI
