import OAI.ThreeFlat.Diagonal.CompressorLaneSplit
import OAI.ThreeFlat.Diagonal.RefreshArrival
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Transporting sites and actual edges between successive compressor shapes -/

namespace ThreeFlat.Diagonal.CompressorPacking.StageAddress
open Computability.VPVNP.Compression
variable {V X H Tag L : Type} {c d : ℕ}
variable [AddCommGroup X] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]

def site (z : (V × Fin d) × X) : V × X := (z.1.1,z.2)

def reshuffle : V × (BitWord c × H × Tag × L) ≃ Position V H Tag L c where
  toFun z := ((z.1,z.2.2.2),z.2.1,z.2.2.1)
  invFun z := (z.1.1,z.2.1,z.2.2,z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def splitSite (u : X ≃+ BitWord c × H × Tag × L) : V × X ≃ Position V H Tag L c :=
  ((Equiv.refl V).prodCongr u.toEquiv).trans reshuffle

def splitEdge (u : X ≃+ BitWord c × H × Tag × L) :
    (V × Fin d) × X ≃ Arc V H Tag L d c :=
  ((Equiv.refl (V × Fin d)).prodCongr u.toEquiv).trans packedAddress

def packedGraph (P : PackingData V H Tag L d c) : LiftedSlots V d (BitWord c × H × Tag × L) :=
  ⟨P.slots,fun e => (P.bitShift e,P.slotShift e,P.siteShift e)⟩

theorem split_source (u : X ≃+ BitWord c × H × Tag × L) (z : (V × Fin d) × X) :
    sourcePosition (splitEdge u z) = splitSite u (site z) := rfl

theorem actual_conjugacy (G : LiftedSlots V d X) (u : X ≃+ BitWord c × H × Tag × L)
    (P : PackingData V H Tag L d c) (agree : packedGraph P = changeLanes G u)
    (z : (V × Fin d) × X) : P.actual (splitEdge u z) = splitEdge u (G.actualTarget z) := by
  rcases z with ⟨e,g⟩
  change packedAddress ((packedGraph P).actualTarget (e,u g)) = packedAddress (_,u _)
  rw [agree,changeLanes_target]
  rfl

theorem actual_symm_conjugacy (G : LiftedSlots V d X) (u : X ≃+ BitWord c × H × Tag × L)
    (P : PackingData V H Tag L d c) (agree : packedGraph P = changeLanes G u)
    (z : (V × Fin d) × X) : P.actual.symm (splitEdge u z) = splitEdge u (G.actualTarget.symm z) := by
  apply P.actual.injective
  rw [Equiv.apply_symm_apply,actual_conjugacy G u P agree,Equiv.apply_symm_apply]

theorem split_target (G : LiftedSlots V d X) (u : X ≃+ BitWord c × H × Tag × L)
    (P : PackingData V H Tag L d c) (agree : packedGraph P = changeLanes G u) (z : (V × Fin d) × X) :
    sourcePosition (P.actual (splitEdge u z)) = splitSite u (site (G.actualTarget z)) := by
  rw [actual_conjugacy G u P agree,split_source]

def refreshSite (u : X ≃+ H × L) (port : Fin d ≃ H) : V × X ≃ (V × L) × Fin d where
  toFun z := ((z.1,(u z.2).2),port.symm (u z.2).1)
  invFun z := (z.1.1,u.symm (port z.2,z.1.2))
  left_inv z := by simp
  right_inv z := by simp

def refreshEdge (u : X ≃+ H × L) (port : Fin d ≃ H) :
    (V × Fin d) × X ≃ RefreshTies.Address (V × L) d :=
  ((Equiv.refl (V × Fin d)).prodCongr u.toEquiv).trans (RefreshTies.slotAddress port).symm

def refreshVertex (a : RefreshTies.Address (V × L) d) : (V × L) × Fin d := (a.1,a.2.1)

theorem refresh_source (u : X ≃+ H × L) (port : Fin d ≃ H) (z : (V × Fin d) × X) :
    refreshVertex (refreshEdge u port z) = refreshSite u port (site z) := rfl

theorem refresh_conjugacy (G : LiftedSlots V d X) (u : X ≃+ H × L) (port : Fin d ≃ H)
    (z : (V × Fin d) × X) :
    RefreshTies.arrival (changeLanes G u) port (refreshEdge u port z) =
      refreshEdge u port (G.actualTarget z) := by
  rcases z with ⟨e,g⟩
  simp only [RefreshTies.arrival,refreshEdge,Equiv.trans_apply,Equiv.apply_symm_apply]
  exact congrArg (RefreshTies.slotAddress port).symm (changeLanes_target G u e g)

theorem refresh_target (G : LiftedSlots V d X) (u : X ≃+ H × L) (port : Fin d ≃ H)
    (z : (V × Fin d) × X) :
    refreshVertex (RefreshTies.arrival (changeLanes G u) port (refreshEdge u port z)) =
      refreshSite u port (site (G.actualTarget z)) := by
  rw [refresh_conjugacy,refresh_source]

/-- The consumed coordinate in a refresh of power-of-two temporary degree. -/
def dyadicPort (s : ℕ) : Fin (2^s) ≃ BitWord s := finFunctionFinEquiv.symm

end ThreeFlat.Diagonal.CompressorPacking.StageAddress

end OAI
