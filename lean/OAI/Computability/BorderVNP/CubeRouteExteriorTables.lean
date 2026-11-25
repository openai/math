import OAI.Computability.BorderVNP.CubeRouteCalibratedPreparation
import OAI.Computability.BorderVNP.CubeRouteExteriorOwners
import OAI.Computability.BorderVNP.CubeRoutePackedDemands

/-! # Equality of the actual ordered tables and physical wire layouts across exteriors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical Packing.Directory RoutingISA

/-- Equality of the native routing columns only requires equal receivers at cells present in the compact data list. -/
theorem combinedRow_congr {R a q : ℕ} {xs ys : List Row} {left right : ℕ → Fin (R+1)}
    (blocks K h : ℕ) (D : LengthDeclaration a q) {g g' : Fin q → Fin (R+1)}
    (data : xs=ys) (hosts : ∀ i : Fin xs.length, left xs[i.val].cell=right xs[i.val].cell) (groups : g=g') :
    combinedRow xs left blocks K h D g = combinedRow ys right blocks K h D g' := by
  subst ys
  subst g'
  funext k
  unfold combinedRow
  split
  · rename_i hk
    cases e : (ordinal xs.length q).symm ⟨k,hk⟩ with
    | inl i => simp only [Sum.elim_inl,dataRow,hosts i]
    | inr p => rfl
  · rfl

end Cube.RouteRecords

namespace Routing.WireLayout

/-- Header and width uniquely determine the full typed four-region wire layout. -/
theorem eq_of_fields {N r link : ℕ} (L M : WireLayout N r link) (head : L.header=M.header) (wid : L.width=M.width) :
    L=M := by
  cases L
  cases M
  cases head
  cases wid
  rfl

end Routing.WireLayout

namespace TeamContraction

open VPVNP BurstRAM Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube BorderVNP.Cube.Physical Packing.Directory

/-- The computed table on each exterior, at exactly the frame and count read by the native route. -/
def exteriorTable (a : CubeArena.Layout) (frame : ℕ) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) :=
  a.table frame ((D.directory pp lp).length+a.header.d.choose 2)

/-- The common four columns, indexed by their genuine populated ordinal. -/
noncomputable def exteriorRows {R : ℕ} (a : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (owner : ℕ → Fin (R+1)) (decl : LengthDeclaration a.n a.header.d) (group : Fin a.header.d → Fin (R+1)) :=
  RouteRecords.combinedRow (D.directory pp lp) owner a.header.blocks a.K a.h decl group

/-- If the same network and source placements produced the native owners, the entire routing table and
typed wire allocation agree across the two exterior inputs. Slots outside the populated data list may
have arbitrary values in either placement memory. -/
theorem exterior_tables_of_placement {R r link : ℕ} {T : Type*} (ref : T)
    (a : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : T → ℕ → ℕ × ℕ) (frame : ℕ)
    {I : Type*} [Fintype I] (cell : I → Fin a.cells) (id : I ↪ ℕ) (width : I → ℕ)
    (place : ∀ t, BankPlacement D (pp t) (lp t) I cell id width) (keys : ∀ t k, (place t).key k=(place ref).key k)
    (bound : D.DestinationBounds) (owner : T → ℕ → Fin (R+1)) (decl : LengthDeclaration a.n a.header.d)
    (group : T → Fin a.header.d → Fin (R+1))
    (owners : ∀ t, group t=group ref ∧ ∀ c < a.cells, owner t c=owner ref c)
    (L : T → WireLayout (R+1) r link) (header : ℕ) (teams : R+1=a.teams)
    (calibrated : ∀ t, (L t).header=header ∧ (L t).width=tableWidth (exteriorTable a frame D (pp t) (lp t))
      (exteriorRows a D (pp t) (lp t) (owner t) decl (group t)) teams) :
    ∀ t, D.directory (pp t) (lp t)=D.directory (pp ref) (lp ref) ∧
      exteriorTable a frame D (pp t) (lp t)=exteriorTable a frame D (pp ref) (lp ref) ∧
      exteriorRows a D (pp t) (lp t) (owner t) decl (group t) =
        exteriorRows a D (pp ref) (lp ref) (owner ref) decl (group ref) ∧ (L t).width=(L ref).width ∧ L t=L ref := by
  intro t
  have data := (place t).directory_eq (place ref) (keys t) bound
  have tab : exteriorTable a frame D (pp t) (lp t) = exteriorTable a frame D (pp ref) (lp ref) := by
    simp only [exteriorTable,data]
  have row : exteriorRows a D (pp t) (lp t) (owner t) decl (group t) =
      exteriorRows a D (pp ref) (lp ref) (owner ref) decl (group ref) :=
    RouteRecords.combinedRow_congr _ _ _ _ data (fun i => (owners t).2 _ (BankPlacement.populated_cell_lt (place t) bound i)) (owners t).1
  have sameWidth : (L t).width=(L ref).width := by
    rw [(calibrated t).2,(calibrated ref).2,row]
    exact congrArg (fun count : ℕ => tableWidth (a.table frame (count+a.header.d.choose 2))
      (exteriorRows a D (pp ref) (lp ref) (owner ref) decl (group ref)) teams) (congrArg List.length data)
  exact ⟨data,tab,row,sameWidth,WireLayout.eq_of_fields _ _ ((calibrated t).1.trans (calibrated ref).1.symm) sameWidth⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
