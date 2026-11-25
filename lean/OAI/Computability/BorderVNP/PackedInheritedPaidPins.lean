import OAI.Computability.BorderVNP.PackedInheritedPaidModel
import OAI.Computability.BorderVNP.PackedBankPaidInstall
import OAI.Computability.BorderVNP.PackedInheritedFields

/-! # Intrinsic seed-packet pins of each paid site

Each bundle's static reference selects its own endpoint in the sewn layout.
The virtual endpoint prefix is measured with zero auxiliary storage, so adding
the site's work places the complete incoming cable in intrinsic coordinates.
The frozen packet expressions then give precisely the site's birth rows and
their relocation marks, for internal edges, self-loops and terminal feeders.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.PaidSite

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep
open BankJoint BankPacket
open scoped Classical
open private paidReference from OAI.Computability.BorderVNP.PackedBankReferences

private theorem atOwner {D ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (v : N.Site) (z : Incident N v) (edge : N.Edge) (hz : z.val = edge) (side : Bool)
    (hs : (if side then N.src edge else N.dst edge) = v) :
    (if side then wireStart N edgeID portID (N.src edge) ⟨edge,.inl rfl⟩
     else wireStart N edgeID portID (N.dst edge) ⟨edge,.inr rfl⟩) = wireStart N edgeID portID v z := by
  subst edge
  rcases z with ⟨z,hz⟩
  cases side <;> dsimp only [Bool.false_eq_true,ite_false,ite_true] at hs ⊢ <;> subst v <;> rfl

variable {D m ne np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {S : Type} [Fintype S] (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (s : S) (a : Fin e.count) (v : (e.net a).Site)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)

local notation3 "G₀" => (output e p bin perm positive first q).layout
local notation3 "tag₀" => (Sum.inr (Sum.inr ⟨a,v⟩) : TemplateSite e)
local notation3 "ws" => PaidBox.widths (e.net a) v
local notation3 "cp₀" => Subtype.val (q s) a
local notation3 "start₀" => starts e p bin perm positive first q s a v edgeID portID

/-- The selected end of every paid template bundle is the actual incident cable
used by the local sparse program. The source is selected at a paid self-loop. -/
theorem referenced_start (r : Fin (Fintype.card (PaidBox.Bundle (e.net a) v))) :
    ∃ u side, reference e tag₀ r = some (u,side) ∧
      let edge : (G₀).Edge := .inr (.inr ⟨s,u⟩)
      (if side then wireStart G₀ edgeID portID ((G₀).src edge) ⟨edge,.inl rfl⟩
       else wireStart G₀ edgeID portID ((G₀).dst edge) ⟨edge,.inr rfl⟩) = start₀ r := by
  let B := PaidBox.Bundle (e.net a) v
  let code (z : B) : TemplateEdge e × Bool := match z with
    | .inl z => (.inr (.inr ⟨a,z.val⟩),decide ((e.net a).src z.val = v))
    | .inr z => (.inr (.inl (a,z.val)),false)
  let z := (Fintype.equivFin B).symm r
  let cable := PaidPhysical.cable e p bin perm positive first q s a v z
  have href : reference e tag₀ r = some (code z) := by
    change paidReference e a v z = some (code z)
    cases z <;> rfl
  have hz : cable.val = .inr (.inr ⟨s,(code z).1⟩) := by
    change (PaidPhysical.cable e p bin perm positive first q s a v z).val = _
    cases z <;> rfl
  have hs := reference_site e p bin perm positive first q s tag₀ r (code z).1 (code z).2 href
  exact ⟨(code z).1,(code z).2,href,atOwner G₀ edgeID portID _ cable _ hz _ hs⟩

variable (position : e.Entry → ℕ)
local notation3 "state₀" => physical e p bin perm positive first q s a v edgeID portID position

/-- The common seed-packet emitter returns exactly the private persistent rows
when fed the site's zero offsets, physical histogram and intrinsic cable bases. -/
theorem emitted_rows (raw : Raw e → ℕ) (hc : raw (.inl (some a)) = cp₀)
    (ho : raw (.inr ⟨tag₀,none⟩) = 0) (hi : raw (.inr ⟨tag₀,some none⟩) = 0)
    (hb : ∀ r : Fin (Fintype.card (PaidBox.Bundle (e.net a) v)),
      raw (.inr ⟨tag₀,some (some r)⟩) = work ws cp₀ + start₀ r) :
    emitted e first raw tag₀ = (state₀).rows := by
  let f := PaidBox.tableFactor e position a v
  have fields : (fun i : Operands e tag₀ => word e raw (pin e tag₀ i)) =
      PaidBinding.fields ws cp₀ 0 0 (source ws cp₀ start₀) := by
    funext i
    rcases i with _ | _ | h | r
    · exact ho
    · exact hi
    · exact congrArg (fun c => PaidBox.header ws c h) hc
    · exact hb r
  have hrows : (state₀).rows = (PaidBinding.fragment ws cp₀ 0 0 (source ws cp₀ start₀) [[f]]).records := by
    exact congrArg CellSparse.Directory.records (directory ws cp₀ (incoming G₀ (PaidPhysical.site e p bin perm positive first q s a v)) start₀ f)
  rw [hrows]
  change (BankPacket.Paid.rows ws).map (RecordCode.read (fun i : Operands e tag₀ => word e raw (pin e tag₀ i))) = _
  rw [fields]
  rfl

/-- The relocation marks belong to precisely the words of those same stored rows. -/
theorem emitted_marks (raw : Raw e → ℕ) (h : emitted e first raw tag₀ = (state₀).rows) :
    ((rows e first tag₀).flatMap markedCode).map
      (fun z => (z.1,z.2.eval (fun i => word e raw (pin e tag₀ i)))) = (state₀).markedWords := by
  rw [Site.markedWords,← h]
  simp only [emitted,List.flatMap_map,List.map_flatMap]
  apply List.flatMap_congr
  intro r _
  exact markedCode_eval r _

end Packing.Inherited.PaidSite

end BorderVNP
end Computability
end OAI
