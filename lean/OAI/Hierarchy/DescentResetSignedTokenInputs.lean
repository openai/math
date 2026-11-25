import OAI.Hierarchy.DescentPaddedSignedInputs
import OAI.Hierarchy.DescentResetSignedTokens
import OAI.Hierarchy.DescentDatedVenueSources

namespace OAI
/-! # The dated signed-cable input to the next reset's token raster -/
namespace Hierarchy.DescentResetSignedTokens
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentStageEdgeReceipt ProtocolRAM
open DescentPacking.PackedMatch.Local.Stage DescentCompiler
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i N H R w : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {T : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W T price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : AtomSchedule) (ready : A.StateBounds S i) (groups : J≃Fin R) (hosts : V≃Fin H) (ph : H≤N)
local notation "padded" => hosts.toEmbedding.trans (Fin.castLEEmb ph)

/-- Projecting a recorded signed cable onto its marked token gives the exact
old socket consumed by the reset, also at every unoccupied host. -/
theorem dated_token (short : ℕ) (h : Fin N) (g : Fin R) (t : Fin (2^k) × Fin (2*A.cap)) :
    marked short (Prepare.signed A native S ready groups.toEmbedding padded t.1 t.2 h g) =
      PackedFlow.Padded.tokens A native S ready groups hosts short h g t := by
  classical
  unfold Prepare.signed Prepare.spreadField PackedFlow.Padded.tokens DescentPackedFlowPair.Padded.project
  by_cases active : h.val<H
  · let old : Fin H := ⟨h.val,active⟩
    let u := (groups.symm g,hosts.symm old)
    have mapped : padded u.2=h := by
      apply Fin.ext
      change (hosts (hosts.symm old)).val=h.val
      rw [hosts.apply_symm_apply]
    have seen : ∃z : J×V,groups.toEmbedding z.1=g ∧ padded z.2=h :=
      ⟨u,groups.apply_symm_apply g,mapped⟩
    have chosen : seen.choose=u :=
      Prod.ext (groups.injective (seen.choose_spec.1.trans (groups.apply_symm_apply g).symm))
        ((padded).injective (seen.choose_spec.2.trans mapped.symm))
    simp only [dite_eq_left active,dite_eq_left seen,chosen,Option.elim_some]; rfl
  · have absent : ¬∃z : J×V,groups.toEmbedding z.1=g ∧ padded z.2=h := by
      rintro ⟨z,_,hz⟩
      have same : (hosts z.2).val=h.val := congrArg Fin.val hz
      exact active (same ▸ (hosts z.2).isLt)
    simp only [dite_eq_right active,dite_eq_right absent,Option.elim_none]; rfl

def datedLayout (N R sourceLanes targetLanes short : ℕ) : Layout :=
  ⟨N,R,sourceLanes,targetLanes,k,A.degree,A.cap,short⟩

local notation "sheet" => datedLayout A N R
local notation "pin" => Prepare.signed A native S ready groups.toEmbedding padded

/-- Both complete cable words and the token banks required by prepare_initial
are issued by the same program on the previous date's signed venue. -/
theorem venue_issued (sourceLanes targetLanes short base : ℕ)
    (pages : (Fin (2^k) × Fin (2*A.cap)) → Bank) (m : Memory w)
    (before : ∀t,(pages t).Fits w base)
    (extent : ∀t,N*chunks R sourceLanes≤(pages t).size)
    (read : ∀t,Reads (pages t) (fun h g=>DescentSignedCableCodec.encode (pin t.1 t.2 h g)) sourceLanes m)
    (live : 0<sourceLanes) (cap : (sheet sourceLanes targetLanes short).endAddress base<2^w) :
    let s := sheet sourceLanes targetLanes short
    (s.phase base w pages).Runs m ∧
      ∀t, Reads (s.raw base t) (fun h g=>DescentSignedCableCodec.encode (pin t.1 t.2 h g)) targetLanes
          ((s.phase base w pages).image m) ∧
        Reads (s.bank base t) (fun (h : Fin N) g=>PackedFlow.Padded.tokens A native S ready groups hosts short h g t)
          targetLanes ((s.phase base w pages).image m) := by
  let s := sheet sourceLanes targetLanes short
  obtain ⟨run,rows⟩ := s.issued base pages m (fun t=>pin t.1 t.2) before extent read live cap
  refine ⟨run,fun t=>⟨(rows t).1,?_⟩⟩
  have eqn : (fun h g=>marked short (pin t.1 t.2 h g)) =
      (fun (h : Fin N) g=>PackedFlow.Padded.tokens A native S ready groups hosts short h g t) :=
    funext fun h=>funext fun g=>dated_token A native S ready groups hosts ph short h g t
  rw [←eqn]
  exact (rows t).2

end
end Hierarchy.DescentResetSignedTokens

end OAI
