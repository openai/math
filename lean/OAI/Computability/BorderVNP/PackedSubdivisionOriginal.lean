import OAI.Computability.BorderVNP.PackedSubdivisionSlices
import OAI.Computability.BorderVNP.PackedRetainedWork

/-! # Observation fibers of a retained subdivided site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing
open scoped Classical

variable {D m n np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (route : N.WireRoutes) (v : N.Site)
local notation "G" => N.subdivide route
variable (oldID : N.Edge ↪ Fin m) (newID : (N.subdivide route).Edge ↪ Fin n) (portID : P ↪ Fin np)

variable (wire : ∀ e : Incident (N.subdivide route) (.inl v), Fin ((N.subdivide route).width e.val) → Bool)
    (port : ∀ p : Attached (N.subdivide route) (.inl v), Fin (bits p.val) → Bool)

/-- Restrict arbitrary successor cable words to the endpoints selected by the original site. -/
noncomputable def oldWires (e : Incident N v) (j : Fin (N.width e.val)) : Bool :=
  if h : N.src e.val = v then wire ⟨⟨e.val,0⟩,Or.inl (congrArg Sum.inl h)⟩ j
  else wire ⟨⟨e.val,Fin.last _⟩,Or.inr (by simp [Network.subdivide,e.property.resolve_left h])⟩ j

/-- Restrict attached exterior ports to the same original words. -/
def oldPorts (p : Attached N v) := port (attached N route v p)

omit [Fintype P] in
private theorem wire_congr {a b : Incident G (.inl v)} {width : ℕ} (eqn : a=b)
    (ha : width=(G).width a.val) (hb : width=(G).width b.val) (j : Fin width) :
    wire a (Fin.cast ha j) = wire b (Fin.cast hb j) := by subst b; rfl

omit [Fintype P] in
private theorem endpoint_read (e : Incident N v) (j : Fin (N.width e.val)) :
    wire (endpoint N route v e) (Fin.cast (endpoint_width N route v e).symm j) = oldWires N route v wire e j := by
  by_cases h : N.src e.val = v
  · rw [oldWires,dite_eq_left h]
    let a : Incident G (.inl v) := ⟨⟨e.val,0⟩,.inl (congrArg Sum.inl h)⟩
    have eqn : endpoint N route v e = a := dite_eq_left h
    exact wire_congr N route v wire eqn (endpoint_width N route v e).symm rfl j
  · rw [oldWires,dite_eq_right h]
    let a : Incident G (.inl v) := ⟨⟨e.val,Fin.last _⟩,.inr (by simp [Network.subdivide,e.property.resolve_left h])⟩
    have eqn : endpoint N route v e = a := dite_eq_right h
    exact wire_congr N route v wire eqn (endpoint_width N route v e).symm rfl j

/-- The incidence-vector projection reads exactly the chosen first/last hop
and the original exterior ports at their canonical physical addresses. -/
theorem read_inputs :
    inputWords G newID portID (.inl v) wire port ∘ read N route v oldID newID portID =
      inputWords N oldID portID v (oldWires N route v wire) (oldPorts N route v port) := by
  funext k
  obtain ⟨a,rfl⟩ := (sourceOrder N oldID portID v).surjective k
  rcases a with ⟨e,j⟩ | ⟨p,j⟩ <;> simp only [Function.comp_apply,read,Equiv.symm_apply_apply,nextLane]
  · exact (inputWords_wire G newID portID (.inl v) wire port (endpoint N route v e) _).trans
      ((endpoint_read N route v wire e j).trans (inputWords_wire N oldID portID v _ _ e j).symm)
  · exact (inputWords_port G newID portID (.inl v) wire port (attached N route v p) j).trans
      (inputWords_port N oldID portID v (oldWires N route v wire) (oldPorts N route v port) p j).symm

omit [Fintype P] in
/-- Direct evaluation of the subdivision definition, including a loop returning
to a different final hop. Only the source copy of that loop feeds the original table. -/
theorem original_table {R : Type*} [Zero R] [One R] (t : N.Tables R) :
    N.subdivideTables route t (.inl v) wire port =
      t v (oldWires N route v wire) (oldPorts N route v port) := by
  apply congrArg₂ (t v) _ rfl
  funext e j
  by_cases h : N.src e.val = v <;> simp [oldWires,h]

/-- The actual sparse original-site program after endpoint subdivision. -/
noncomputable def originalProgram (s : Site) : Site :=
  s.retain (incoming G (.inl v)) (cuts N route v oldID newID portID)

/-- Extending a real previously installed history through the new endpoint layer. -/
noncomputable def originalRetention {birth s : Site} (past : birth.Retention s)
    (size : s.incoming = incoming N v) :
    birth.Retention (originalProgram N route v oldID newID portID s) :=
  .layer past _ (read N route v oldID newID portID ∘ Fin.cast size)
    ((covers N route v oldID newID portID).castOld size)

/-- Any fixed complete sequence of signed observations has precisely the same
private multiplicity when its chosen endpoint words are staged by the new rows. -/
noncomputable def originalFiber (s : Site) (size : s.incoming = incoming N v) (loc : s.Local)
    (obs : List (Bool × Option ℕ)) :
    s.Fiber (inputWords N oldID portID v (oldWires N route v wire) (oldPorts N route v port) ∘ Fin.cast size) obs ≃
      (originalProgram N route v oldID newID portID s).Fiber (inputWords G newID portID (.inl v) wire port) obs := by
  rw [←read_inputs N route v oldID newID portID wire port]
  exact retainFiberEquiv s loc _ (read N route v oldID newID portID ∘ Fin.cast size)
    ((covers N route v oldID newID portID).castOld size) _ obs

/-- The sparse private program realizes the paper's actual subdivided local table for
arbitrary entries in the original program and all supplied physical input assignments. -/
theorem original_models {R : Type*} [AddCommMonoid R] [One R] (t : N.Tables R)
    (s : Site) (size : s.incoming = incoming N v) (loc : s.Local) (weight : List (Bool × Option ℕ) → R)
    (model : s.Models N oldID portID v size weight t) :
    (originalProgram N route v oldID newID portID s).Models G newID portID (.inl v) rfl weight
      (N.subdivideTables route t) := by
  intro wire port
  change (s.retain _ _).value weight (inputWords G newID portID (.inl v) wire port) = _
  refine (value_retain s loc _ (read N route v oldID newID portID ∘ Fin.cast size)
    ((covers N route v oldID newID portID).castOld size) weight (inputWords G newID portID (.inl v) wire port)).trans ?_
  rw [original_table N route v wire port t,←model (oldWires N route v wire) (oldPorts N route v port)]
  apply congrArg (s.value weight)
  funext j
  exact congrFun (read_inputs N route v oldID newID portID wire port) (Fin.cast size j)

/-- The old private choices and every prior record occur once, followed by
at most one sparse endpoint tie per old cable or exterior port. -/
theorem original_resources (s : Site) :
    let t := originalProgram N route v oldID newID portID s
    t.work = s.size ∧ t.incoming = incoming G (.inl v) ∧ t.boxes = s.boxes ∧
      t.rows.length ≤ s.rows.length + (Fintype.card (Incident N v) + Fintype.card (Attached N v)) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  exact (s.retain_count ..).le.trans (Nat.add_le_add_left (cuts_count N route v oldID newID portID) _)

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
