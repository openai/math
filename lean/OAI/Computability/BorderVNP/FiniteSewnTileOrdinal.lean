import OAI.Computability.BorderVNP.DiagonalExternalTileLookup
import OAI.Computability.BorderVNP.DiagonalExternalGridHosts
import OAI.Computability.BorderVNP.FiniteSewnFieldLanes

/-! # The actual grouped field lane at a team, tile, and copy offset

An occupied field slot is read exactly at the grouped lane recorded by
the grid. The same statement detects every missing lane of the padded
last tile. All team and port coordinates use their genuine enumerations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open scoped Classical

variable {R r t pins link inner n V groups copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (hV : 0 < V) (count : groups*copies = R+1)

local notation "g" => blockWidth (r*n) V
local notation "groupLane" => groupedLane G V hV groups copies count
local notation "teams" => teamBlocks groups copies count

/-- The inverse grouped lane lookup uses the same team and team-local
ordinal as the native physical tile run. -/
theorem groupedLane_iff (hg : 0 < g) (a : Fin groups × Fin V) (i : Fin copies) (j : Fin g)
    (p : PublicPort R r (G.program.length+t) link) :
    groupLane p = ⟨a,finProdFinEquiv (i,j)⟩ ↔
      p.1 = (teams).symm (a.1,i) ∧ (teamOrdinal p).val = a.2.val*g+j.val := by
  let u := teams p.1
  let slot := wiredLane G V hV p.2
  have physical : groupLane p = ⟨(u.1,slot.1),finProdFinEquiv (u.2,slot.2)⟩ := rfl
  have c := wiredLane_coordinates G hV p.2
  change slot.1.val = (teamOrdinal p).val/g ∧ slot.2.val = (teamOrdinal p).val%g at c
  constructor
  · intro eqn
    rw [physical] at eqn
    have hgroup := congrArg Sigma.fst eqn
    have hbit := finProdFinEquiv.injective (congrArg (fun k : Σ _ : Fin groups × Fin V, Fin (copies*g) => k.2) eqn)
    have team : u = (a.1,i) := Prod.ext (congrArg (fun z : Fin groups × Fin V => z.1) hgroup)
      (congrArg (fun z : Fin copies × Fin g => z.1) hbit)
    have tile : slot.1 = a.2 := congrArg Prod.snd hgroup
    have lane : slot.2 = j := congrArg Prod.snd hbit
    refine ⟨(teams).eq_symm_apply.mpr team,?_⟩
    calc
      (teamOrdinal p).val = (teamOrdinal p).val/g*g+(teamOrdinal p).val%g := (Nat.div_add_mod' ..).symm
      _ = a.2.val*g+j.val := by rw [← c.1,← c.2,tile,lane]
  · rintro ⟨ht,ho⟩
    have team : u = (a.1,i) := (teams).eq_symm_apply.mp ht
    have tile : slot.1 = a.2 := Fin.ext (c.1.trans ((Nat.div_eq_iff hg).mpr (by rw [ho]; have := j.isLt; omega)))
    have lane : slot.2 = j := Fin.ext (c.2.trans (by rw [ho]; simp [Nat.mod_eq_of_lt j.isLt]))
    rw [physical,team,tile,lane]

/-- The actual finite lookup classifies exactly the unique linked/free
slot that occupies a named old grouped incidence lane. -/
theorem lookup_grouped_iff (hg : 0 < g) (a : Fin groups × Fin V) (i : Fin copies) (j : Fin g)
    (s : TileRuns.Slot R r (G.program.length+t) link g) :
    TileRuns.lookup ((teams).symm (a.1,i)) a.2.val j = some s ↔
      groupLane (TileRuns.port R r (G.program.length+t) link g s) = ⟨a,finProdFinEquiv (i,j)⟩ :=
  (TileRuns.lookup_some ..).trans (groupedLane_iff G hV count hg a i j _).symm

end Packing.SewnField

end BorderVNP
end Computability
end OAI
