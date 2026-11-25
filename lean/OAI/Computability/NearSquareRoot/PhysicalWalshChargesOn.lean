import OAI.Computability.NearSquareRoot.PhysicalWalshCharges

/-! # Charging a Walsh machine on a closed set of recursive layouts

The same template command applies at every shape. Its numerical time and
space certificates need only cover admitted roots and their descendants.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Space

variable {X U K : Type*} {d : RecSpec X U} {W calls : ℕ}

/-- Restrict the proof indices of a recursive machine to permitted layouts. -/
def RecSpec.restrict (d : RecSpec X U) (P : U → Prop) :
    RecSpec {x : X // P (d.world x)} {u : U // P u} where
  world x := ⟨d.world x.val,x.property⟩
  level u := d.level u.val
  payload x := d.payload x.val
  reply x := d.reply x.val
  child u v := d.child u.val v.val
  decreases := d.decreases
  scan u := d.scan u.val
  arena u := d.arena u.val
  arena_le u := d.arena_le u.val

def ChargeLayout.restrict (l : ChargeLayout d W K) (P : U → Prop) : ChargeLayout (d.restrict P) W K where
  key u := l.key u.val
  volume u := l.volume u.val
  nonnegative u := l.nonnegative u.val
  childKey := l.childKey
  childLevel := l.childLevel
  childVolume := l.childVolume

/-- Bounds on a descendant-closed set of worlds suffice for the compiled
recursive program with the original serialized query and reply. -/
theorem ChargeLayout.boundedOn (l : ChargeLayout d W K) (P : U → Prop)
    (closed : ∀ {u v}, d.child u v → P u → P v)
    (one : BoundedTask (fun x : d.Base => d.scan (d.world x.val))
      (fun x => d.arena (d.world x.val)) (fun x => d.payload x.val) (fun x => d.reply x.val))
    (step : OpenRun d.meter calls (fun x : d.Step => d.world x.val)
      (fun x => d.payload x.val) (fun x => d.reply x.val))
    (t s : K → ℕ → ℝ → ℝ) (tmono : ∀ k j, Monotone (t k j)) (smono : ∀ k j, Monotone (s k j))
    (ht : ∀ u, P u → (d.scan u : ℝ)+1 ≤ t (l.key u) (d.level u) (l.volume u))
    (hs : ∀ u, P u → (d.arena u : ℝ)+1 ≤ s (l.key u) (d.level u) (l.volume u)) :
    BoundedTask (fun x : {x : X // P (d.world x)} => l.budget calls t (d.world x.val))
      (fun x => l.budget 1 s (d.world x.val)) (fun x => d.query x.val) (fun x => d.reply x.val) := by
  apply (l.restrict P).bounded _ _ t s tmono smono
    (fun u => ht u.val u.property) (fun u => hs u.val u.property)
  · exact one.on (fun x : (d.restrict P).Base => ⟨x.val.val,x.property⟩)
  · obtain ⟨cmd,C,run⟩ := step
    refine ⟨cmd,C,fun x env time space permit p b hp => ?_⟩
    apply run (⟨x.val.val,x.property⟩ : d.Step) env time space _ p b hp
    intro y child
    exact permit ⟨y,closed child x.val.property⟩ child

end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
