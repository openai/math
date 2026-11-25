import OAI.Hierarchy.DescentResetBothPayloads
import OAI.Hierarchy.DescentPackedMatchPrepareIssued
import OAI.Hierarchy.DescentGroupPeerOrder

namespace OAI
/-! # Exact reciprocal receipts on the actual padded old source and target banks -/
namespace Hierarchy.DescentResetOppositePayload
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentIssuedFallbackPanel DescentSIMDLookup DescentSixParty
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentHostDirectory DescentColonies
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i b H G : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {pow : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W pow price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J↪Fin G) (hosts : V↪Fin H)
local notation "rank" => groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "names" => cableNames k rank
local notation "old"=>DescentSharedCableNames.Stage.Host J V k
local notation "E"=>DescentSharedCableNames.Stage.Grain A
local notation "adj"=>hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))
local notation "panel"=>DescentSharedCableNames.Stage.signedPanel A native S ready names
local notation "addr"=>DescentIssuedFallbackPanel.address A native S ready
local notation "peer"=>physicalPeer A names

def widened (D cap b : ℕ) (r : Option (DescentSharedCableNames.Stage.Live D cap)) : Cell b:=(DescentSignedCableCodec.encode r).val
def rectangular (x : Block k) (j : Fin (2*A.cap)) (h : Fin H) (g : Fin G) : Cell b:=
  widened A.degree A.cap b (Prepare.signed A native S ready groups hosts x j h g)

theorem decoded {D cap : ℕ} (enough : DescentSignedCableCodec.width D cap≤b) (r : Option (DescentSharedCableNames.Stage.Live D cap)) :
    chip D cap (widened D cap b r)=r:=by
  apply chip_at
  exact Fin.val_cast_of_lt ((DescentSignedCableCodec.encode r).isLt.trans_le (Nat.pow_le_pow_right (by decide) enough))

theorem host_at (v : V) (i : Fin A.degree) :
    adj (hosts v) i=((hostRoster A (hosts.trans Fin.valEmbedding)) v i).map hosts:=by
  have hit:∃u,hosts u=hosts v:=⟨v,rfl⟩
  rw [hostRotor,dite_eq_left hit,hosts.injective hit.choose_spec]

theorem signed_at (h : old) (j : Fin (2*A.cap)) :
    Prepare.signed A native S ready groups hosts h.2 j (hosts h.1.2) (groups h.1.1)=panel h j:=by
  have hit : ∃z : J×V,groups z.1=groups h.1.1 ∧ hosts z.2=hosts h.1.2:=⟨h.1,rfl,rfl⟩
  have same : hit.choose=h.1:=Prod.ext (groups.injective hit.choose_spec.1) (hosts.injective hit.choose_spec.2)
  simp only [Prepare.signed,Prepare.spreadField,dite_eq_left hit,same]

theorem peering (h : old) (i : Fin A.degree) :
    peer h i=((hostRoster A (hosts.trans Fin.valEmbedding)) h.1.2 i).map (fun z=>((h.1.1,z),h.2)):=
  physicalPeer_group A (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding) h.1.1 h.1.2 h.2 i

def bookAt (payload : Block k→Fin (2*A.cap)→Fin H→Fin G→Cell b) (h : old) (j : Fin (2*A.cap)) : Cell b:=
  payload h.2 j (hosts h.1.2) (groups h.1.1)

/-- The predecessor hardware executes one fixed orientation on every group,
including padded groups. On any actual old grain the full returned register
is exactly the remote old measured register for this grain. -/
theorem rectangle (enough : DescentSignedCableCodec.width A.degree A.cap≤b) (positive : 0<b)
    (payload : Block k→Fin (2*A.cap)→Fin H→Fin G→Cell b) (side : Bool) (e : E) :
    let p:=port A side e
    let other:=port A (!side) e
    let raw:=rectangular (b:=b) A native S ready groups hosts p.1.2
    let x:=digits adj (raw (addr p).2) raw (payload p.1.2) (hosts p.1.1.2) (groups p.1.1.1)
    both A.degree A.cap b (!side) x=bookAt A groups hosts payload other.1 (addr other).2:=by
  intro p other raw x
  let h:=p.1
  let values:=bookAt A groups hosts payload
  let reads:=fun j : Slot A.degree A.cap=>(peer h j.1).bind (fun v=>panel v j.2)
  let cargo:=fun j : Slot A.degree A.cap=>(peer h j.1).elim 0 (fun v=>values v j.2)
  have readQuery : chip A.degree A.cap (raw (addr p).2 (hosts h.1.2) (groups h.1.1))=panel h (addr p).2:=by
    change chip A.degree A.cap (widened A.degree A.cap b
      (Prepare.signed A native S ready groups hosts h.2 (addr p).2 (hosts h.1.2) (groups h.1.1))) = _
    rw [decoded enough, signed_at A native S ready groups hosts h]
  have readField (j : Slot A.degree A.cap) : chip A.degree A.cap
      ((adj (hosts h.1.2) j.1).elim 0 (fun v=>raw j.2 v (groups h.1.1)))=reads j:=by
    rw [host_at A hosts]
    dsimp only [reads]
    rw [peering A groups hosts]
    cases leg : hostRoster A (hosts.trans Fin.valEmbedding) h.1.2 j.1 with
    | none=>
      simp only [Option.map_none,Option.elim_none,Option.bind_none]
      apply chip_at (row:=none)
      rw [DescentSignedCableCodec.empty];rfl
    | some z=>
      simp only [Option.map_some,Option.elim_some,Option.bind_some]
      change chip A.degree A.cap (widened _ _ b (Prepare.signed A native S ready groups hosts h.2 j.2 (hosts z) (groups h.1.1)))=_
      rw [decoded enough,signed_at A native S ready groups hosts ((h.1.1,z),h.2)]
  have readPay (j : Slot A.degree A.cap) : (adj (hosts h.1.2) j.1).elim 0 (fun z=>payload h.2 j.2 z (groups h.1.1))=cargo j:=by
    rw [host_at A hosts];dsimp only [cargo];rw [peering A groups hosts]
    cases hostRoster A (hosts.trans Fin.valEmbedding) h.1.2 j.1 <;>rfl
  have back (a c : Fin A.degree) :
      decide ((if DescentResetReciprocalPeer.reaches adj (hosts h.1.2) a c then (1:Cell b) else 0).val≠0)=guardAt A names h a c:=by
    simp only [DescentResetReciprocalPeer.reaches,guardAt,host_at A hosts,peering A groups hosts]
    cases hop : hostRoster A (hosts.trans Fin.valEmbedding) h.1.2 a with
    | none=>simp
    | some z=>
      simp only [Option.map_some,Option.bind_some,host_at A hosts]
      have mapped (h₀ : old) (o : Option V) :
          decide ((if o.map hosts = some (hosts h₀.1.2) then (1:Cell b) else 0).val ≠ 0) =
          decide (o.map (fun z => ((h₀.1.1,z),h₀.2)) = some h₀) := by
        rcases h₀ with ⟨⟨g,v⟩,block⟩
        cases o with
        | none => simp
        | some t => by_cases eqn : t=v <;> simp [eqn,hosts.injective.eq_iff,positive.ne']
      exact mapped h _
  change both _ _ _ _ (project _ _ _ _)=_
  rw [both_at,readQuery,funext readField,funext readPay,funext (fun a=>funext (back a))]
  cases side
  · exact returned A native S ready names e values
  · exact paired A native S ready names e values

end
end Hierarchy.DescentResetOppositePayload

end OAI
