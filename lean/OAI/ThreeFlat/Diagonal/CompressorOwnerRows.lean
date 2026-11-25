import OAI.Computability.VPVNP.SlotPacking
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Indexed child lists for the two compressor layouts

Each new site enumerates its old children by two blocks of slot/word pairs.
The thick block uses the site itself. For a thin child the incoming slot
uniquely recovers the assigned bundle and the old site. Admissibility is one
test of the old position's color bit.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.Owner
open Computability.VPVNP.Compression

variable {V H Tag L : Type*} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

abbrev Index (d c : ℕ) := Bool × (Fin d × BitWord c)

def port (layout : Bool) : Equiv.Perm (Site V Tag L × Fin d) :=
  if layout then P.siteGraph.target else Equiv.refl _

def child (layout : Bool) (site : Site V Tag L) (i : Index d c) : Position V H Tag L c :=
  if i.1 then
    let e := (port P layout).symm (site,i.2.1)
    (P.offsetSite.symm e.1,i.2.2,P.slotLabel.symm e.2)
  else (site,i.2.2,P.slotLabel.symm i.2.1)

def valid (layout : Bool) (site : Site V Tag L) (i : Index d c) : Prop :=
  if i.1 then ¬P.thick (child P layout site i) else P.thick (child P layout site i)

instance (layout : Bool) (site : Site V Tag L) (i : Index d c) :
    Decidable (valid P layout site i) := by unfold valid; split <;> infer_instance

def index (layout : Bool) (x : Position V H Tag L c) : Index d c :=
  if P.thick x then (false,P.slotLabel x.2.2,x.2.1)
  else (true,(port P layout (P.assignedBundle x)).2,x.2.1)

omit [AddCommGroup H] in
theorem placement_eq (layout : Bool) (x : Position V H Tag L c) :
    P.placement layout x = if P.thick x then x.1 else (port P layout (P.assignedBundle x)).1 := by
  cases layout <;> simp [PackingData.placement,port]

omit [AddCommGroup H] in
theorem child_index (layout : Bool) (x : Position V H Tag L c) :
    child P layout (P.placement layout x) (index P layout x) = x := by
  by_cases h : P.thick x <;>
    simp [index,child,placement_eq,h,PackingData.assignedBundle]

omit [AddCommGroup H] in
theorem valid_index (layout : Bool) (x : Position V H Tag L c) :
    valid P layout (P.placement layout x) (index P layout x) := by
  rw [valid,child_index]
  by_cases h : P.thick x <;> simp [index,h]

omit [AddCommGroup H] in
theorem placement_child (layout : Bool) (site : Site V Tag L) (i : Index d c)
    (h : valid P layout site i) : P.placement layout (child P layout site i) = site := by
  obtain ⟨b,i,u⟩ := i
  cases b with
  | false =>
    have thick : P.thick (child P layout site (false,i,u)) := h
    rw [placement_eq,ite_eq_left thick]
    rfl
  | true =>
    have thin : ¬P.thick (child P layout site (true,i,u)) := h
    rw [placement_eq,ite_eq_right thin]
    simp [child,PackingData.assignedBundle]

omit [AddCommGroup H] in
theorem index_child (layout : Bool) (site : Site V Tag L) (i : Index d c)
    (h : valid P layout site i) : index P layout (child P layout site i) = i := by
  obtain ⟨b,i,u⟩ := i
  cases b with
  | false =>
    have thick : P.thick (child P layout site (false,i,u)) := h
    rw [index,ite_eq_left thick]
    simp [child]
  | true =>
    have thin : ¬P.thick (child P layout site (true,i,u)) := h
    rw [index,ite_eq_right thin]
    simp [child,PackingData.assignedBundle]

def children (layout : Bool) (site : Site V Tag L) :
    {i : Index d c // valid P layout site i} ≃ {x // P.placement layout x = site} where
  toFun i := ⟨child P layout site i.val,placement_child P layout site i.val i.property⟩
  invFun x := ⟨index P layout x.val,by simpa only [x.property] using valid_index P layout x.val⟩
  left_inv i := Subtype.ext (index_child P layout site i.val i.property)
  right_inv x := Subtype.ext (by simpa only [x.property] using child_index P layout x.val)

theorem index_count : Fintype.card (Index d c) = 2*d*2^c := by
  simp [Index,BitWord,Nat.mul_assoc]

end ThreeFlat.Diagonal.CompressorPacking.Owner

end OAI
