import OAI.Computability.BorderVNP.CubePhysicalBottomExtraction
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites
import OAI.Computability.BorderVNP.PackedInheritedPlacementWork

/-! # Recovering bottom wire choices from the actual installed private banks

Each original site has a unique final host. Its intrinsic private bank is the
row-major array of completed original copies. All inherited cut and subdivision
records append forced work, and final cell placement appends the current incident
words. The decoder reads the original prefix in the true installed cell slab.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited
open scoped Classical

variable {D m np ns : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {Cell : Type}
    (N : Network D P bits) (cell : N.Site → Cell) (siteID : N.Site ↪ Fin ns)
    (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin np) (state : Site.Programs N)
    {J : Type*} (host : J ↪ N.Site) (slabs : J → Slab) (mult : J → ℕ)
    (birthWidth : ∀ j, (state (host j)).birth.work = mult j*(slabs j).stride)

/-- Work and incidence width physically allocated for a whole host program. -/
abbrev placedSize (state : Site.Programs N) (v : N.Site) := (state v).program.size

/-- Each original copy starts at its old offset in the actual final site, even
after its private program has retained several subdivisions and crossing epochs. -/
def retainedLocation (j : J) : BottomLocation N (placedSize N state) (slabs j) (mult j) where
  site := host j
  offset := 0
  fits := (Nat.zero_add _).le.trans ((birthWidth j).symm.le.trans
    ((state (host j)).retention.work_le.trans (Nat.le_add_right ..)))

/-- All non-private fields in a completed one-copy bottom slab. -/
abbrev BottomFields (s : Slab) := (Fin s.supplied → Bool) × (Fin s.incoming → Bool) × (Fin s.used → Bool)

/-- The complete work tape at a retained original site at its birth. -/
def originalWork (z : BottomChoices slabs mult) (data : ∀ j, Fin (mult j) → BottomFields (slabs j))
    (j : J) (k : Fin (state (host j)).birth.work) : Bool :=
  let coord := finProdFinEquiv.symm (Fin.cast (birthWidth j) k)
  let f := data j coord.1
  (slabs j).complete (z j coord.1) f.1 f.2.1 f.2.2 coord.2

/-- The intrinsic work of a site, using the actual bottom copy contents exactly
when this is the retained host of an original input. -/
noncomputable def sourceWork (z : BottomChoices slabs mult) (data : ∀ j, Fin (mult j) → BottomFields (slabs j))
    (other : ∀ v : N.Site, Fin (state v).birth.work → Bool) (v : N.Site) : Fin (state v).birth.work → Bool := by
  by_cases hv : ∃ j, host j = v
  · let j := hv.choose
    exact (hv.choose_spec ▸ originalWork N state host slabs mult birthWidth z data j)
  · exact other v

/-- Host injectivity retrieves the prescribed original copy at its own birth address. -/
theorem sourceWork_at (z : BottomChoices slabs mult) (data : ∀ j, Fin (mult j) → BottomFields (slabs j))
    (other : ∀ v : N.Site, Fin (state v).birth.work → Bool) (j : J) :
    sourceWork N state host slabs mult birthWidth z data other (host j) =
      originalWork N state host slabs mult birthWidth z data j := by
  have hx : ∃ k, host k = host j := ⟨j,rfl⟩
  have agree (k : J) (e : host k = host j) :
      (e ▸ originalWork N state host slabs mult birthWidth z data k) =
        originalWork N state host slabs mult birthWidth z data j := by
    obtain rfl := host.injective e
    rfl
  unfold sourceWork
  rw [dite_eq_left hx]
  exact agree _ hx.choose_spec

variable {n d blocks b h K s : ℕ} {Team : Type*} [DecidableEq Cell]
    (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)

variable (supply : Routed (b := b) (s := s) owners → ∀ c, Fin (suppliedSize N cell c) → Bool)
    (fields : BottomChoices slabs mult → Routed (b := b) (s := s) owners → ∀ c, (Fin (guessedSize N cell c) → Bool) → ∀ j, Fin (mult j) → BottomFields (slabs j))
    (other : BottomChoices slabs mult → Routed (b := b) (s := s) owners → ∀ c, (Fin (guessedSize N cell c) → Bool) → ∀ v : N.Site, Fin (state v).birth.work → Bool)

/-- The actual installed incidence data and the uniquely extended intrinsic work
at each site, as addressed by the physical cell's site-word map. -/
noncomputable def retainedExpected (z : BottomChoices slabs mult) (q : Routed (b := b) (s := s) owners) : Expected N cell (placedSize N state) := fun c g =>
  let input := fun v : {v : N.Site // cell v=c} =>
    Placement.canonical N cell c edgeID portID v g (supply q c) ∘ Fin.cast (state v.val).size
  let work := fun v : {v : N.Site // cell v=c} => (state v.val).retention.complete (input v)
    (sourceWork N state host slabs mult birthWidth z (fields z q c g) (other z q c g) v.val)
  siteWords N cell c siteID (placedSize N state)
    (Placement.install N cell c siteID edgeID portID (fun v => (state v).program) (fun v => (state v).size)
      g (supply q c) work)

omit [DecidableEq Cell] in
/-- The particular retained original lane contains the complete designated data of its
birth copy, including the actual fine guessed and supplied bits and the report lanes. -/
theorem retainedExpected_lane (z : BottomChoices slabs mult) (q : Routed (b := b) (s := s) owners)
    (j : J) (i : Fin (mult j)) (g : Fin (guessedSize N cell (cell (host j))) → Bool)
    (k : Fin (slabs j).stride) :
    let f := fields z q (cell (host j)) g j i
    retainedExpected N cell siteID edgeID portID state host slabs mult birthWidth owners supply fields other
      z q (cell (host j)) g ⟨host j,rfl⟩ (BottomLocation.lane N (placedSize N state)
        (retainedLocation N state host slabs mult birthWidth j) i k) =
      (slabs j).complete (z j i) f.1 f.2.1 f.2.2 k := by
  let c := cell (host j)
  let data := fields z q c g
  let v : {v : N.Site // cell v=c} := ⟨host j,rfl⟩
  let input := fun u : {v : N.Site // cell v=c} =>
    Placement.canonical N cell c edgeID portID u g (supply q c) ∘ Fin.cast (state u.val).size
  let work := fun u : {v : N.Site // cell v=c} => (state u.val).retention.complete (input u)
    (sourceWork N state host slabs mult birthWidth z data (other z q c g) u.val)
  let lane := Fin.cast (birthWidth j).symm (finProdFinEquiv (i,k))
  let here := state (host j)
  have native := Placement.read_install N cell c siteID edgeID portID (fun u => (state u).program)
    (fun u => (state u).size) g (supply q c) work v
  have atLane := congrFun native ((lane.castLE here.retention.work_le).castAdd here.program.incoming)
  have named : BottomLocation.lane N (placedSize N state) (retainedLocation N state host slabs mult birthWidth j) i k =
      (lane.castLE here.retention.work_le).castAdd here.program.incoming := by
    apply Fin.ext
    simp [BottomLocation.lane,retainedLocation,lane]
  change retainedExpected N cell siteID edgeID portID state host slabs mult birthWidth owners supply fields other
    z q c g v (BottomLocation.lane N (placedSize N state) (retainedLocation N state host slabs mult birthWidth j) i k) = _
  rw [named]
  refine atLane.trans ((Fin.append_left (work v) (input v) _).trans ?_)
  rw [show work v _ = _ from here.retention.complete_prefix (input v) _ lane]
  change sourceWork N state host slabs mult birthWidth z data (other z q c g) (host j) lane = _
  rw [sourceWork_at]
  simp only [originalWork,lane,Fin.cast_cast,Fin.cast_eq_self,Equiv.symm_apply_apply]
  rfl

omit [DecidableEq Cell] in
/-- The true installed expected banks have the precise bottom-copy images consumed by
the native wire decoder. -/
theorem retainedBottomImages :
    BottomImages N cell (placedSize N state) owners slabs mult
      (fun _ j => retainedLocation N state host slabs mult birthWidth j)
      (retainedExpected N cell siteID edgeID portID state host slabs mult birthWidth owners supply fields other) := by
  intro z q j i g
  let f := fields z q (cell (host j)) g j i
  exact ⟨f.1,f.2.1,f.2.2,retainedExpected_lane N cell siteID edgeID portID state host slabs mult birthWidth owners
    supply fields other z q j i g⟩

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
