import OAI.Computability.VPVNP.SlotDemandKernel

/-!
# Reading the four demand words locally

The bit slices of an AB demand can contain pieces from several old wires.
Every outgoing old factor in those pieces lands at the single packed A site,
and every incoming factor lands at B. The unsplit CD words are read at the
new site of their respective old endpoint. This supplies the demand arguments
of the local map rows in equation (7.1).
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

/-- All thick source positions of a bundle are packed together at A. -/
theorem place_thick_source (layout : Bool) (a : P.ThickWire) :
    P.placement layout (sourcePosition a.1) = a.1.1.1 := by
  rw [placement, ite_eq_left a.2.1]
  rfl

/-- All thick destination positions of the same bundle are packed at B. -/
theorem place_thick_target (layout : Bool) (a : P.ThickWire) :
    P.placement layout (sourcePosition (P.actual a.1)) = (P.siteGraph.target a.1.1).1 := by
  rw [placement, ite_eq_left a.2.2]
  rfl

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]

variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag L d c → ℕ) (layout : Bool)

/-- Half-wire fields of all whole old vertices placed at a single new site. -/
abbrev PlacedHalf (s : Site V Tag L) :=
  NetworkKernel.Placed (P.placement layout) (P.oldWireNetwork w).Half s

/-- Extract the source half of the AB slice from the local inputs at A. -/
def localAWord (m : P.Motif) (x : P.PlacedHalf w layout (P.roleA m)) :
    Fin (P.abWidth number w m) → Bool := fun i ↦
  let z := P.demandBitEquiv hc hd number order w (P.bundle m) ⟨⟨m,rfl⟩,i⟩
  let h : P.roleA m = P.placement layout (sourcePosition z.1.1.1) :=
    (congrArg Prod.fst z.1.2.symm).trans (P.place_thick_source layout z.1.1).symm
  (x (sourcePosition z.1.1.1) h).1 z.1.1.1 rfl z.2

/-- Extract the destination half of the same slice from the inputs at B. -/
def localBWord (m : P.Motif) (x : P.PlacedHalf w layout (P.roleB m)) :
    Fin (P.abWidth number w m) → Bool := fun i ↦
  let z := P.demandBitEquiv hc hd number order w (P.bundle m) ⟨⟨m,rfl⟩,i⟩
  let h : P.roleB m = P.placement layout (sourcePosition (P.actual z.1.1.1)) :=
    (congrArg (fun b ↦ (P.siteGraph.target b).1) z.1.2.symm).trans
      (P.place_thick_target layout z.1.1).symm
  (x (sourcePosition (P.actual z.1.1.1)) h).2 z.1.1.1 rfl z.2

/-- Extract the CD half-wire at C, whichever original slot supplied it. -/
def localCWord (m : P.Motif) (x : P.PlacedHalf w layout (P.placement layout (P.C m))) :
    Fin (w m.1) → Bool :=
  if h : P.thick (sourcePosition m.1) then
    (x (sourcePosition (P.actual m.1)) (by simp [C,h])).2 m.1 rfl
  else (x (sourcePosition m.1) (by simp [C,h])).1 m.1 rfl

/-- Read the opposite CD half-wire at D's new position. -/
def localDWord (m : P.Motif) (x : P.PlacedHalf w layout (P.roleD layout m)) :
    Fin (w m.1) → Bool :=
  if h : P.thick (sourcePosition m.1) then
    (x (sourcePosition m.1) (by simp [roleD,D,h])).1 m.1 rfl
  else (x (sourcePosition (P.actual m.1)) (by simp [roleD,D,h])).2 m.1 rfl

@[simp] theorem localAWord_eval (m : P.Motif) (x : ∀ s, (P.oldWireNetwork w).Half s) :
    P.localAWord hc hd number order w layout m (fun u _ ↦ x u) =
      P.abWord hc hd number order w (P.outgoingWord w x) m := rfl

@[simp] theorem localBWord_eval (m : P.Motif) (x : ∀ s, (P.oldWireNetwork w).Half s) :
    P.localBWord hc hd number order w layout m (fun u _ ↦ x u) =
      P.abWord hc hd number order w (P.incomingWord w x) m := rfl

omit [DecidableEq V] [DecidableEq Tag] [DecidableEq L] in
@[simp] theorem localCWord_eval (m : P.Motif) (x : ∀ s, (P.oldWireNetwork w).Half s) :
    P.localCWord w layout m (fun u _ ↦ x u) = P.cWord w x m := by
  by_cases h : P.thick (sourcePosition m.1) <;> simp [localCWord,cWord,h] <;> rfl

omit [DecidableEq V] [DecidableEq Tag] [DecidableEq L] in
@[simp] theorem localDWord_eval (m : P.Motif) (x : ∀ s, (P.oldWireNetwork w).Half s) :
    P.localDWord w layout m (fun u _ ↦ x u) = P.dWord w x m := by
  by_cases h : P.thick (sourcePosition m.1) <;> simp [localDWord,dWord,h] <;> rfl

end Compression.PackingData

end VPVNP
end Computability
end OAI
