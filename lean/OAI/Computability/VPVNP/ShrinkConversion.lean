import OAI.Computability.VPVNP.ShrinkMotif
import OAI.Computability.VPVNP.SlotDemandKernel
import OAI.Computability.VPVNP.RAMSerialization

/-!
# Six-party identities on the packed demand words

Section 7.2 applies one fixed instance of Theorem 6.1 to every AB/CD pair.
The independently supplied old half-wire words give the four terminal inputs
of the identity. Its outer index determines the supply widths, while one
shared value per supply edge is summed over inside the selected term.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open WireTensor MotifGrid MotifBlocks MotifConversion MotifSelector MotifDemandPadding ShrinkMotif

variable {V H Tag L : Type} {d c : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c)
variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag L d c → ℕ)

/-- The widths of the AB and CD wires in the local identity. -/
abbrev shrinkDemandWidths (m : P.Motif) := demandWidths (P.abWidth number w m) (w m.val)

/-- Read the AB and CD words independently at both old endpoints. -/
def shrinkDemandArg (m : P.Motif) (x : ∀ u, (P.oldWireNetwork w).Half u) (j : Fin 6) :
    HalfBits demandSource demandTarget (P.shrinkDemandWidths number w m) j :=
  (fun e _ ↦ match e with
    | false => (RAMSerialization.wordBits _).symm
        (P.abWord hc hd number order w (P.outgoingWord w x) m)
    | true => (RAMSerialization.wordBits _).symm (P.cWord w x m),
   fun e _ ↦ match e with
    | false => (RAMSerialization.wordBits _).symm
        (P.abWord hc hd number order w (P.incomingWord w x) m)
    | true => (RAMSerialization.wordBits _).symm (P.dWord w x m))

variable {k : Type*} [Field k] {H' : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R)

/-- The admissible outer indices in the local conversion of one demand. -/
noncomputable abbrev ShrinkChoice (m : P.Motif) :=
  ↥(outerIndices B (P.shrinkDemandWidths number w m))

/-- Supply width of an admitted local term. -/
noncomputable abbrev shrinkSupplyWidths (m : P.Motif) (i : P.ShrinkChoice number w B m) :=
  supplyWidths B (P.shrinkDemandWidths number w m) i.val

/-- A matrix entry at each party, over the ring carrying a solution of the
block's fixed equations. -/
noncomputable def shrinkMap (m : P.Motif) (i : P.ShrinkChoice number w B m) (j : Fin 6) :
    HalfBits demandSource demandTarget (P.shrinkDemandWidths number w m) j →
      HalfBits supply.src supply.dst (P.shrinkSupplyWidths number w B m i) j → R :=
  fun x y ↦ evalEntry κ (entry B demandMass_pos (P.shrinkDemandWidths number w m) i.val j x y)

/-- Exact six-party expansion on the old independent half-wire inputs, in
every ring satisfying the same parameter equations. -/
theorem shrinkDemand_identity (hκ : (parameterData B).IsSolution κ) (m : P.Motif)
    (x : ∀ u, (P.oldWireNetwork w).Half u) :
    P.demandCoeff hc hd number order w m x =
      ∑ i : P.ShrinkChoice number w B m,
        ∑ z : (e : Bool × Fin 4) → Word (P.shrinkSupplyWidths number w B m i e),
          ∏ j, P.shrinkMap number w B κ m i j (P.shrinkDemandArg hc hd number order w m x j)
            (edgeAssignment supply.src supply.dst z j) := by
  classical
  let X := P.shrinkDemandArg hc hd number order w m x
  have hw : (wireNetwork (k := R) demandSource demandTarget
      (fun e ↦ Word (P.shrinkDemandWidths number w m e))).coeff X =
      P.demandCoeff hc hd number order w m x := by
    have hab : (X (demandSource false)).1 false rfl = (X (demandTarget false)).2 false rfl ↔
        P.abWord hc hd number order w (P.outgoingWord w x) m =
          P.abWord hc hd number order w (P.incomingWord w x) m :=
      (RAMSerialization.wordBits _).symm.injective.eq_iff
    have hcd : (X (demandSource true)).1 true rfl = (X (demandTarget true)).2 true rfl ↔
        P.cWord w x m = P.dWord w x m := (RAMSerialization.wordBits _).symm.injective.eq_iff
    simp only [wireNetwork, Fintype.prod_bool, hab, hcd, demandCoeff]
    by_cases h : P.cWord w x m = P.dWord w x m <;> simp [h]
  rw [← hw]
  have h := congrFun (identity B κ hκ demandMass_pos supplyMass_pos
    (P.shrinkDemandWidths number w m)) X
  erw [Finset.sum_apply] at h
  refine h.trans ?_
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i _
  refine (applyLocal_wireNetwork (k := R) supply.src supply.dst
    (fun e ↦ Word (P.shrinkSupplyWidths number w B m i e))
    (P.shrinkMap number w B κ m i) X).trans ?_
  apply Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext z
  simp

end Compression.PackingData

end VPVNP
end Computability
end OAI
