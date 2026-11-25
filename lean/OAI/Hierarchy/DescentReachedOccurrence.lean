import OAI.Hierarchy.DescentReached

namespace OAI
/-! # Fixed common terminal positions and the actual occurrence calendar at a position -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentHostDegree DescentHostDirectory DescentColonies
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
    {G:PoweredGadget F} {price ε:ℝ} {S:AtomSchedule} {k age z degree wire hist : ℕ}
    (R:Reached W G price ε S k age z degree wire hist)

/-- Each group uses the same host coordinate and the same padded position file. -/
def home (v : W.graph.Site) : Fin (S.hostSize age) :=
  (R.vertex (R.placement.pos v).2).castLE R.valid.host

theorem home_eq {v u : W.graph.Site} :
    R.home v=R.home u ↔ (R.placement.pos v).2=(R.placement.pos u).2 := by
  constructor
  · intro h
    exact R.vertex.injective (Fin.ext (congrArg (fun p : Fin (S.hostSize age)=>p.val) h))
  · intro h
    simp only [home,h]

/-- The vertex injection in a reached phase gives a truthful local calendar of
(group,block). This same rank is used even when other groups have missing slots. -/
def slot (i:Fin (S.hostSize age)) : {v:W.graph.Site // R.home v=i} ↪ Fin (S.groupCount age)×Block k where
  toFun u:=((R.placement.pos u.val).1,R.placement.block u.val)
  inj' := by
    intro v u h
    have host: (R.placement.pos v.val).2=(R.placement.pos u.val).2:=R.home_eq.mp (v.property.trans u.property.symm)
    apply Subtype.ext
    apply R.valid.coordinates
    have first: (R.placement.pos v.val).1=(R.placement.pos u.val).1 :=
      congrArg (fun p : Fin (S.groupCount age)×Block k=>p.1) h
    have second: R.placement.block v.val=R.placement.block u.val :=
      congrArg (fun p : Fin (S.groupCount age)×Block k=>p.2) h
    exact Prod.ext (Prod.ext first host) second

theorem occurrence_bound (i:Fin (S.hostSize age)) :
    Fintype.card {v:W.graph.Site // R.home v=i}≤S.groupCount age*2^k := by
  simpa [Block] using Fintype.card_le_of_embedding (R.slot i)

end
end Hierarchy.DescentSixParty.Reached

end OAI
