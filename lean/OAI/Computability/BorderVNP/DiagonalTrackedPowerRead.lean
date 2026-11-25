import OAI.Computability.BorderVNP.DiagonalTrackedPowerHosts
import OAI.Computability.BorderVNP.PackedInheritedRoundValue

/-! # Reading an original unary bit through one actual sorted crossing step

The tagged output reads its old bands at their selected cut or hook, inverts the
source's dense cable order and selects the correct child. The input may come from
one particular endpoint of a routed packet. Only incidence words of the chosen
owner site enter the result.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Shortening.Adaptive Packing Packing.Inherited
open PackedHistoryCircuit.Normalized Diagonal.ExternalSew
open private extendWires extendPorts from OAI.Computability.BorderVNP.PackedInheritedRoundValue
open scoped Classical
set_option maxHeartbeats 1800000

variable {D : ℕ} {P : Type} {bits : P → ℕ}

/-- Complete edge and port words used to read one specified physical owner. -/
structure PowerInput (N : Network D P bits) where
  /-- The assigned cable lanes, used at the selected endpoint. -/
  edges : N.Assignment
  /-- The grouped exterior word at each attached port. -/
  ports : Ports bits

/-- Extend the supplied local words at a single host, including one word for each incident
loop. The extension is used solely to evaluate tables at this same host. -/
noncomputable def PowerInput.atHost (N : Network D P bits) (v : N.Site)
    (z : ∀ u : Incident N v, Fin (N.width u.val) → Bool)
    (x : ∀ u : Attached N v, Fin (bits u.val) → Bool) : PowerInput N :=
  ⟨extendWires N v z,extendPorts N v x⟩

variable {Team Param Gadget : Type} [Fintype Team] [Fintype Param] {exp : ℕ}

/-- Evaluate one original binary power slot at its current physical owner. -/
noncomputable def Tracked.powerRead {N : Network D P bits} (t : Tracked Team Param Gadget exp N)
    (w : PowerSlot Team Param exp) (x : PowerInput N) : Bool :=
  N.read t.words.selected x.edges x.ports (t.words.site w) w

/-- The genuine path tally's endpoint-specific selected bit is exactly this local table read. -/
theorem Tracked.localUse_atHost {N : Network D P bits} (t : Tracked Team Param Gadget exp N)
    (w : PowerSlot Team Param exp) (z : PowerSites.LocalEdges N) (x : PowerSites.LocalPorts N) :
    t.words.localUse z x w.1 w.2.1 w.2.2 =
      t.powerRead w (PowerInput.atHost N (t.words.site w) (z _) (x _)) := by
  rcases w with ⟨team,p,j⟩
  let v := t.words.site (team,p,j)
  have hz : (fun u : Incident N v => (PowerInput.atHost N v (z v) (x v)).edges u.val) = z v := by
    funext u k
    simp only [PowerInput.atHost,extendWires,dite_eq_left u.property]
  have hx : (fun u : Attached N v => (PowerInput.atHost N v (z v) (x v)).ports u.val) = x v := by
    funext u k
    simp only [PowerInput.atHost,extendPorts,dite_eq_left u.property]
  exact (congrFun (congrArg₂ (t.words.selected v) hz hx) (team,p,j)).symm

/-- Pull complete words back along the actual storage cable and port maps. -/
def Storage.powerInput {N M : Network D P bits} (store : Storage N M) (x : PowerInput M) : PowerInput N :=
  ⟨store.assignment x.edges,x.ports⟩

theorem Storage.powerRead {N M : Network D P bits} (store : Storage N M) (t : Tracked Team Param Gadget exp N)
    (w : PowerSlot Team Param exp) (x : PowerInput M) :
    (store.tracked t).powerRead w x = t.powerRead w (store.powerInput x) := by
  have h := store.read t.words.selected x.edges x.ports (store.site (t.words.site w))
  rw [store.site.symm_apply_apply] at h
  exact congrFun h w

namespace DenseReplay

variable {m k d d' : ℕ} [NeZero D] {I B K E : Type} [Fintype I] [Fintype B] [Field K] [Field E]
    {child : Fin k → PlacedPack D P bits K I d} (s : Stage m B d' child)
    (input : ∀ j, Tracked Team Param Gadget exp (child j).pack.layout)
    (e : PaidIdentity K D m) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0) (pos : e.Entry → Gadget)
    (q : s.Index e)

/-- Original sorted input cable words at this chosen inherited site, reconstructed
from the actual cut, hook and residual positions of the selected histogram. -/
noncomputable def cutPowerInput (v : s.input.layout.Site) (x : PowerInput (s.result e q).pack.layout) :
    PowerInput s.input.layout :=
  ⟨extendWires s.input.layout v (oldWireWords e s.input s.label s.perm s.orient (0,false) q x.edges v),x.ports⟩

/-- Undo the first dense save and take exactly the old cables and exterior ports of
the indicated child. -/
noncomputable def childPowerInput (v : (raw child).layout.Site) (x : PowerInput (s.result e q).pack.layout) :
    PowerInput (child v.1).pack.layout :=
  let old := (Storage.dense (raw child).layout s.slot).powerInput (cutPowerInput s e q v x)
  ⟨fun z => old.edges ⟨v.1,z⟩,fun p => old.ports (v.1,p)⟩

/-- The bit read from the selected tagged stage equals the original child's bit on
its physically reassembled old endpoint, for either truth value. -/
theorem stage_power_read (w : PowerSlot (Fin k × Team) Param exp)
    (x : PowerInput (s.result e q).pack.layout) :
    (stageOutput s input e y hy pos q).powerRead w x =
      (input w.1.1).powerRead (w.1.2,w.2) (childPowerInput s e q ⟨w.1.1,(input w.1.1).words.site (w.1.2,w.2)⟩ x) := by
  let v := (ordered s input).words.site w
  let t := (ordered s input).words.selected
  let z := oldWireWords e s.input s.label s.perm s.orient (0,false) q x.edges v
  have hz : (fun u : Incident s.input.layout v => (cutPowerInput s e q v x).edges u.val) = z := by
    funext u j
    simp only [cutPowerInput,extendWires,dite_eq_left u.property,z]
  have h := sewn_table_read e s.input s.label s.perm s.orient (0,false) q t (fun _ _ _ _ => false) x.edges x.ports v
  refine (congrFun h w).trans ?_
  have orderedRead : (ordered s input).powerRead w (cutPowerInput s e q v x) =
      t v z (oldPortWords s.input x.ports v) w := congrArg (fun z' => t v z' (oldPortWords s.input x.ports v) w) hz
  refine orderedRead.symm.trans (((Storage.dense (raw child).layout s.slot).powerRead
    (merged input) w (cutPowerInput s e q v x)).trans ?_)
  simp only [merged,Tracked.powerRead,PowerWords.parallel,Network.read]
  rfl

end DenseReplay
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
