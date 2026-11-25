import OAI.Computability.BorderVNP.CubeRouteCommonOwners

/-! # Common source and receiving teams in the native schedules of all processors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube LocalRow CubeArena Transmission

variable {R w : ℕ} {T : Type*} (team : T → Fin (R+1)) (ref : T) (a : CubeArena.Layout) (frame controls : ℕ) (axis : Fin (a.n+1))
    (saved : T → ℕ) (selected orig final : T → ℕ → ℕ)

local notation "input" => fun u => powerHeaderImage a (saved u) (selected u)
local notation "group" => fun (u : T) (g : Fin a.header.d) => TeamNative.owner R (GroupWeights.Layout.weight (weightLayout a frame axis.val) ((input) u)) (Fin.val g)
local notation "owner" => fun (u : T) => a.receivingOwner frame axis R ((input) u)

/-- Physical owner comparison for two exterior inputs or two different teams.
Only the stored true declaration and the actual chosen label and incoming demand at
each cell must agree with the designated reference execution. -/
theorem native_exterior_owners (pub : T → Arg → ℕ)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ) (axes : a.header.a = a.n+1) (positive : 0 < a.header.d)
    (native : ∀ u, NativeEntry a frame controls axis R ((input) u) (orig u) (final u))
    (sources : ∀ u, DirectorySources a frame controls axis
      (fun mem => a.ScannerWords frame (team u).val axis.val (fun g => ((group) u g).val) (pub u) mem rows) w (final u))
    (labels : ∀ u c, c < a.cells → selected u (a.publicBase+c)=selected ref (a.publicBase+c) ∧
      selected u (a.demands+c)=selected ref (a.demands+c)) :
    ∀ u, (group) u = (group) ref ∧ ∀ c < a.cells, (owner) u c = (owner) ref c := by
  have stored (u : T) := (native u).stored_rows a frame axis R (sources u) rows axes (fun _ words => words.table)
  intro u
  have same (c : ℕ) (hc : c < a.cells) := labels u c hc
  have inputSame (c : ℕ) (hc : c < a.cells) :
      (input) u (a.publicBase+c)=(input) ref (a.publicBase+c) ∧ (input) u (a.demands+c)=(input) ref (a.demands+c) := by
    obtain ⟨lu,du⟩ := cell_words_after_header a (selected u) (saved u) c hc
    obtain ⟨lz,dz⟩ := cell_words_after_header a (selected ref) (saved ref) c hc
    exact ⟨lu.trans ((same c hc).1.trans lz.symm),du.trans ((same c hc).2.trans dz.symm)⟩
  have owners := common_owners a frame axis R positive rows (stored u) (stored ref) inputSame
  exact ⟨funext owners.2.1,owners.2.2⟩


end RoutingISA.Evaluator

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube LocalRow CubeArena Transmission

variable {R w : ℕ} (a : CubeArena.Layout) (frame controls : ℕ) (axis : Fin (a.n+1))
    (saved : Fin (R+1) → ℕ) (selected orig final : Fin (R+1) → ℕ → ℕ)

local notation "input" => fun u => powerHeaderImage a (saved u) (selected u)
local notation "group" => fun (u : Fin (R+1)) (g : Fin a.header.d) => TeamNative.owner R (GroupWeights.Layout.weight (weightLayout a frame axis.val) ((input) u)) (Fin.val g)
local notation "owner" => fun (u : Fin (R+1)) => a.receivingOwner frame axis R ((input) u)

/-- Each genuine team computes the same symbol owners and the same receiver for every placed cell.
The canonical assignment may consequently be read from team zero. The two inputs that must agree
across the actual label runs are the chosen label and total incoming demand at each cell. -/
theorem native_common_owners (pub : Fin (R+1) → Arg → ℕ)
    (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ) (axes : a.header.a = a.n+1) (positive : 0 < a.header.d)
    (native : ∀ u, NativeEntry a frame controls axis R ((input) u) (orig u) (final u))
    (sources : ∀ u, DirectorySources a frame controls axis
      (fun mem => a.ScannerWords frame u.val axis.val (fun g => ((group) u g).val) (pub u) mem rows) w (final u))
    (labels : ∀ u c, c < a.cells → selected u (a.publicBase+c)=selected 0 (a.publicBase+c) ∧
      selected u (a.demands+c)=selected 0 (a.demands+c)) :
    ∀ u, (group) u = (group) 0 ∧ ∀ c < a.cells, (owner) u c = (owner) 0 c :=
  native_exterior_owners (fun u => u) 0 a frame controls axis saved selected orig final pub rows axes positive
    native sources labels

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
