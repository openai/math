import OAI.Computability.BorderVNP.PackedInheritedLayerRead
import OAI.Computability.BorderVNP.PackedInheritedCovers

/-! # Persistent inherited tables at an actual combining round

For the concrete list of clipped bands, hook rows and external-port rows,
the retained private program contracts to the old site's entry of the sewn
pack on every possible local input. Its local extent and representation
invariant can therefore be reused at the next round.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep
open scoped Classical

variable {D m old next np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (name : A → ℕ) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (v : p.layout.Site)

local notation3 "G₀" => (output e p bin perm positive first q).layout
variable (oldID : p.layout.Edge ↪ Fin old) (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin next)
    (portID : P ↪ Fin np)
local notation3 "cuts₀" => layerCuts e p bin perm name positive first q v oldID nextID portID
local notation3 "read₀" => layerRead e p bin perm positive first q v oldID nextID portID

/-- The old-site state installed in this concrete successor branch. -/
noncomputable def retained (s : Site) : Site := s.retain (incoming G₀ (.inl v)) cuts₀

variable (s : Site) (hs : s.incoming = incoming p.layout v) (loc : s.Local)
    (weight : List (Bool × Option ℕ) → K) (models : s.Models p.layout oldID portID v hs weight p.table)

include hs loc in
/-- Every observable choice in the retained state depends only on the enlarged site bank. -/
theorem retained_local : (retained e p bin perm name positive first q v oldID nextID portID s).Local :=
  s.local_retain loc cuts₀ (read₀ ∘ Fin.cast hs)
    ((layer_covers e p bin perm name positive first q v oldID nextID portID).castOld hs)

include loc models in
/-- The value of the retained program, with its physical successor inputs, is the
exact local factor of the field-valued sewn pack. All old private work is summed. -/
theorem retained_read (y : (G₀).Assignment) (x : Ports bits) :
    let state := retained e p bin perm name positive first q v oldID nextID portID s
    state.value weight (successorInput e p bin perm positive first q v nextID portID y x) =
      (G₀).read (output e p bin perm positive first q).table y x (.inl v) := by
  exact value_retain_read e p bin perm positive first q v oldID portID s hs loc weight models
    cuts₀ (read₀ ∘ Fin.cast hs) ((layer_covers e p bin perm name positive first q v oldID nextID portID).castOld hs)
    _ y x (fun k => congrFun (layerRead_inputs e p bin perm positive first q v oldID nextID portID y x) (Fin.cast hs k))

private noncomputable def extendWires {D : ℕ} {P : Type*} {bits : P → ℕ}
    (N : Network D P bits) (v : N.Site) (words : ∀ z : Incident N v, Fin (N.width z.val) → Bool) :
    N.Assignment := fun z k => if h : N.src z = v ∨ N.dst z = v then words ⟨z,h⟩ k else false

private noncomputable def extendPorts {D : ℕ} {P : Type*} {bits : P → ℕ}
    (N : Network D P bits) (v : N.Site) (words : ∀ u : Attached N v, Fin (bits u.val) → Bool) :
    Ports bits := fun u k => if h : N.attach u = v then words ⟨u,h⟩ k else false

include loc models in
/-- The physically constructed successor program realizes the new table on every
local input, including all choices of loop words and zero-width rows. -/
theorem retained_models :
    let state := retained e p bin perm name positive first q v oldID nextID portID s
    state.Models G₀ nextID portID (.inl v) rfl weight (output e p bin perm positive first q).table := by
  intro state z x
  let v' : (G₀).Site := .inl v
  let y := extendWires G₀ v' z
  let ports := extendPorts G₀ v' x
  have hz : (fun u : Incident G₀ v' => y u.val) = z := by
    funext u k
    simp only [y,extendWires,dite_eq_left u.property]
  have hx : (fun u : Attached G₀ v' => ports u.val) = x := by
    funext u k
    simp only [ports,extendPorts,dite_eq_left u.property]
  have hr := retained_read e p bin perm name positive first q v oldID nextID portID s hs loc weight models y ports
  change state.value weight (inputWords G₀ nextID portID v' (fun u => y u.val) (fun u => ports u.val)) =
    (output e p bin perm positive first q).table v' (fun u => y u.val) (fun u => ports u.val) at hr
  rw [hz,hx] at hr
  exact hr

end Packing.Inherited

end BorderVNP
end Computability
end OAI
