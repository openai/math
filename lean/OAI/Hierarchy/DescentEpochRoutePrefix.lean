import OAI.Hierarchy.DescentTerminalEpochRoutes

namespace OAI
/-! # Every reached count is preceded by the original bits of its honest completion -/
namespace Hierarchy.DescentTerminalEpochChart
open DescentTerminalEpochBits DescentSixParty
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {source : U→Z}
variable {b : Chart bits ok source}

/-- At a reached address, the startup choices and every previously used profile pin
are literally equal to those of the total reference path. -/
def Route.Past (p : Route b) : Prop :=
  ∀z, (0 < (b.rows z).length → ∀a, z (b.seed a)=b.store (p.follow z) (b.seed a)) ∧
    ∀i, i+1 < (b.rows z).length → ∀a, b.layout[i]?=some a →
      ∀k,z (a.pin k)=b.store (p.follow z) (a.pin k)

private theorem enough_sources (z : b.Pin→Bool) : (b.rows z).length ≤ b.layout.length := by
  obtain ⟨tail,h⟩:=b.archived z
  have eqn:=congrArg List.length h
  simp only [List.length_map,List.length_append] at eqn
  omega

variable {C seats : ℕ} {I Fiber : U→Type} (n : U→ℕ)
    (number : ∀u,I u≃Fin (n u)) (bound : ∀u,n u ≤ seats)
    (profile : ∀u,Fiber u≃(I u→Profile C))

theorem Route.past_extend (p : Route b) (old : p.Past) : (Route.extend b n number bound profile p).Past := by
  intro z
  let y:=left b z
  let t:=p.follow y
  let nb:=DescentTerminalEpochChart.extend b n number bound profile
  have full {u} (hit : b.read y=some u) : y=b.store t := by
    have eqn:=(b.read_iff _ _).mp hit
    have selected : t=u:=by change p.follow y=u;rw [eqn,p.stored]
    simpa only [selected] using eqn
  have dead (none_ : b.read y=none) : (nb.rows z).length=(b.rows y).length := by
    change (extendedRows b n z).length=_
    simp only [extendedRows,show b.read (left b z)=none from none_,List.append_nil,y]
  have atMost : (nb.rows z).length ≤ (b.rows y).length+1 := by
    change (extendedRows b n z).length ≤ _
    cases h:b.read (left b z) <;> simp [extendedRows,h,y]
  constructor
  · intro positive a
    change y (b.seed a)=b.store t (b.seed a)
    cases hit:b.read y with
    | none=>exact (old y).1 (by rw [←dead hit];exact positive) a
    | some u=>exact congrFun (full hit) _
  · intro i earlier src entered k
    have rowBound : i < b.layout.length :=
      (show i < (b.rows y).length from by
        change i+1 < (nb.rows z).length at earlier
        omega).trans_le (enough_sources y)
    let a:=b.layout[i]
    have prior : b.layout[i]?=some a:=List.getElem?_eq_getElem rowBound
    have shifted : a.map Sum.inl=src := by
      apply Option.some.inj
      change (extendedLayout (C:=C) (seats:=seats) b)[i]?=some src at entered
      simp only [extendedLayout,List.getElem?_append_left (show i < (b.layout.map (Source.map (Sum.inl : b.Pin→b.Pin⊕Pins C seats))).length by simpa using rowBound),
        List.getElem?_map,prior,Option.map_some] at entered
      exact entered
    subst src
    change y (a.pin k)=b.store t (a.pin k)
    cases hit:b.read y with
    | none=>exact (old y).2 i (by rw [←dead hit];exact earlier) a prior k
    | some u=>exact congrFun (full hit) _

end
end Hierarchy.DescentTerminalEpochChart

namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentTerminalEpochChart DescentKernelHistory.BitDescription
open scoped Classical
noncomputable section
variable {F P S Z : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
variable (G : PoweredGadget F) (hu : 0 ≤ u) (he : 0 ≤ ε)
variable {bits : Z→S→Bool} {ok : (S→Bool)→Prop}

theorem schedule_past {t : ℕ} {H : Histories F d P portBits} (s : Schedule G (u:=u) he t H)
    (o : ScheduleOrders G he s) {root : H.Choice→Z} (b : Chart bits ok root) (p : Route b)
    (past : p.Past) : (scheduleRoute G he s o b p).Past := by
  induction t generalizing H with
  | zero=>exact past
  | succ t ih=>
    exact ih s.2 o.2 (extendWith G he s.1 o.1 b) _
      (Route.past_extend (count G he s.1) o.1 (count_le G he s.1) _ p past)

theorem epochs_past {J t h C Ht : ℕ} {H : Histories F d P portBits}
    (s : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H)
    (o : EpochOrders G hu he s) {root : H.Choice→Z} (b : Chart bits ok root) (p : Route b)
    (past : p.Past) : (epochRoute G hu he s o b p).Past := by
  induction J generalizing H with
  | zero=>exact past
  | succ J ih=>
    exact ih s.2 o.2 (scheduledWith G he s.1.subrounds o.1 b) _
      (schedule_past G he s.1.subrounds o.1 b p past)

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
