import OAI.Hierarchy.DescentDonorNativeParts
import OAI.Hierarchy.DescentPackedMatchPrepareIssued
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Retain genuine signed predecessor words from matching into donor replay -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSixParty DescentSIMDLookup DescentPackedZip DescentStageEdgeReceipt
open ProtocolRAM Computability.VPVNP.BurstRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable {d k i M H G w : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
  (valid : A.StateBounds S i) (groups : J≃Fin G) (hosts : V↪Fin H)
local notation "g" => groups.toEmbedding
local notation "rank" => groupRank ((g).trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)

theorem signed_project (x : Fin (2^k)) (j : Fin (2*A.cap)) (v : Fin H) (z : Fin G) :
    DescentSignedCableCodec.encode (Prepare.signed A native S valid g hosts x j v z) =
    physicalSigned A native S valid rank groups hosts v z x j := by
  classical
  unfold physicalSigned Prepare.signed Prepare.spreadField
  by_cases hv : ∃u,hosts u=v
  · let p : J×V:=(groups.symm z,hv.choose)
    have ok : ∃u : J×V,g u.1=z ∧ hosts u.2=v:=⟨p,groups.apply_symm_apply _,hv.choose_spec⟩
    have e : ok.choose=p := Prod.ext ((g).injective (ok.choose_spec.1.trans (groups.apply_symm_apply _).symm))
      (hosts.injective (ok.choose_spec.2.trans hv.choose_spec.symm))
    simp only [dite_eq_left ok,dite_eq_left hv,e,p]
  · have none : ¬∃u : J×V,g u.1=z ∧ hosts u.2=v := fun h=>hv ⟨h.choose.2,h.choose_spec.2⟩
    rw [dite_eq_right none, dite_eq_right hv]
    exact DescentSignedCableCodec.empty ..

theorem signed_retained (wire : Fin (2^k)→Fin (2*A.cap)→Bank) (cut : ℕ) (old new : Memory w)
    (source : ∀x j,Reads (wire x j) (fun h z=>DescentSignedCableCodec.encode (Prepare.signed A native S valid g hosts x j h z)) M old)
    (fit : ∀x j,(wire x j).Fits w cut) (size : ∀x j,H*chunks G M≤(wire x j).size)
    (preserved : ∀x,x<cut→new x=old x) :
    ∀i : Fin ((2^k)*(2*A.cap)),let p:=finProdFinEquiv.symm i
      Source (.lookup (wire p.1 p.2) .row) (fun h z=>physicalSigned A native S valid rank groups hosts h z p.1 p.2) M new := by
  intro i p
  apply source_column _ cut (fit _ _) new _ (size _ _)
  intro a
  rw [preserved _ ((Nat.add_lt_add_left ((row H G M a).isLt.trans_le (size _ _)) _).trans_le (fit p.1 p.2).2.2)]
  simpa only [signed_project] using (source p.1 p.2 a)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
