import OAI.Hierarchy.DescentSeedNativeReadout
import OAI.Hierarchy.DescentSeedResidentPorts
import OAI.Hierarchy.DescentSeedOriginIdentity
import OAI.Hierarchy.DescentSeedNamedSigned

namespace OAI
/-! The literal signed startup pages realize precisely the named initial
placement's published socket chip, including unused padded host coordinates. -/
namespace Hierarchy.DescentSeedInitialTable
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentColonies DescentSIMDLookup DescentPackedColony
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {S:AtomSchedule} {G:PoweredGadget F} {q ε:ℝ} {k cp p wire s z H w:ℕ}
  (X:Approximation F cp p) {c:(initialGroup X S.copies s).Choice}
  {digits:Fin S.copies≃Fin (S.groupCount 0)×Block k}
  (o:Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z) (wire:=wire) c digits)
local notation "A" => o.raw.placement
local notation "T" => placed o.raw
local notation "g₀" => S.groupCount 0
variable (wide:Fintype.card o.raw.V≤H)
local notation "hs" => o.raw.vertex.trans (Fin.castLEEmb wide)
local notation "hs₀" => originalHosts X o wide
local notation "fresh" => Function.Embedding.trans (Reached.order (reached o.raw)) Fin.valEmbedding
local notation "header" => Prepare.signed T fresh S (Reached.valid (reached o.raw)) (Function.Embedding.refl _) hs

private theorem spread_at {J V B : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {groups hosts : ℕ}
    (gi : J ↪ Fin groups) (vi : V ↪ Fin hosts) (zero : B) (f : J × V → B) (g : J) (v : V) :
    Prepare.spreadField gi vi zero f (vi v) (gi g) = f (g,v) := by
  have found : ∃ a : J × V, gi a.1 = gi g ∧ vi a.2 = vi v := ⟨(g,v),rfl,rfl⟩
  unfold Prepare.spreadField
  rw [dite_eq_left found]
  exact congrArg f (Prod.ext (gi.injective found.choose_spec.1) (vi.injective found.choose_spec.2))

private theorem spread_padding {J V B : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {groups hosts : ℕ}
    (gi : J ↪ Fin groups) (vi : V ↪ Fin hosts) (zero : B) (f : J × V → B) (h : Fin hosts) (g : Fin groups)
    (absent : ¬ ∃ v, vi v = h) : Prepare.spreadField gi vi zero f h g = zero :=
  dite_eq_right (fun ⟨a,_,same⟩ => absent ⟨a.2,same⟩)

theorem code_at (x:Block k) (j:Fin (2*(T).cap)) (h:Fin H) (g:Fin g₀):
    (DescentSignedCableCodec.encode (header x j h g)).val=
    (DescentSignedCableCodec.encode ((rack X hs₀ h).bind (fun v=>Signed.Plane.panelAt X v (j.val:Fin 512)))).val:=by
  let root:=Signed.Plane.initialTicket X o.raw.vertex o.seed.hostSize
  have labels (v:o.raw.V) : hs₀ (root v)=hs v:=by
    apply Fin.ext
    simp [originalHosts,root,Signed.Plane.initialTicket]
  have all : Function.Surjective root:=by
    intro v
    have num:Function.Surjective o.raw.vertex:=(Finite.injective_iff_surjective_of_equiv (Fintype.equivFin o.raw.V)).1 o.raw.vertex.injective
    obtain ⟨y,same⟩:=num (Fin.cast o.seed.hostSize.symm (Fintype.equivFin _ v))
    exact ⟨y,by simp [root,Signed.Plane.initialTicket,same]⟩
  let names:=Signed.Plane.panelNames (r:=k) S o.raw.vertex
  have names_eq : cableNames k (DescentStageEdgeReceipt.groupRank
      ((Function.Embedding.refl (Fin g₀)).trans Fin.valEmbedding) ((hs).trans Fin.valEmbedding))=names:=by
    have v:((hs).trans Fin.valEmbedding)=o.raw.vertex.trans Fin.valEmbedding:=Function.Embedding.ext (fun _=>rfl)
    rw [v];rfl
  by_cases hit:∃v,hs v=h
  · obtain ⟨v,rfl⟩:=hit
    let startNames := cableNames k (DescentStageEdgeReceipt.groupRank
      ((Function.Embedding.refl (Fin g₀)).trans Fin.valEmbedding) ((hs).trans Fin.valEmbedding))
    let field := fun y : Fin g₀ × o.raw.V => Stage.signedPanel T fresh S (Reached.valid (reached o.raw))
      startNames (y,x) j
    have selected : header x j (hs v) g = field (g,v) :=
      spread_at (Function.Embedding.refl _) hs none field g v
    have named := congrArg (fun n => Stage.signedPanel T fresh S (Reached.valid (reached o.raw)) n ((g,v),x) j) names_eq
    have prior := SeedNamed.Signed.panel o.raw names ((g,v),x) j
    have word := congrArg (fun t : Option (Stage.Live (A).degree (A).cap) =>
      (DescentSignedCableCodec.encode t).val) (selected.trans (named.trans prior))
    have output := o.seed.signed o.raw.valid g v x j
    have lookup : (rack X hs₀ (hs v)).bind (fun u => Signed.Plane.panelAt X u (j.val : Fin 512)) =
        Signed.Plane.panelAt X (root v) (j.val : Fin 512) := by
      rw [←labels v,rack_real];rfl
    exact word.trans (output.trans (congrArg (fun t : Option (Stage.Live 3 256) =>
      (DescentSignedCableCodec.encode t).val) lookup.symm))
  · have empty : ¬ ∃ v, hs₀ v = h := by
      rintro ⟨v,same⟩;obtain ⟨y,rfl⟩:=all v;exact hit ⟨y,(labels y).symm.trans same⟩
    have missing : header x j h g = none :=
      spread_padding (Function.Embedding.refl _) hs none _ h g hit
    have vacant : rack X hs₀ h = none := dite_eq_right empty
    calc
      _ = (DescentSignedCableCodec.encode (none : Option (Stage.Live (A).degree (A).cap))).val :=
        congrArg (fun t : Option (Stage.Live (A).degree (A).cap) => (DescentSignedCableCodec.encode t).val) missing
      _ = 0 := by rw [DescentSignedCableCodec.empty];rfl
      _ = _ := by rw [vacant];simp [DescentSignedCableCodec.empty]

private theorem reads_equal {a b N m M:ℕ} {mem:Memory w} {banks:Bank} (same:a=b)
    (f:Fin N→Fin m→Cell a) (g:Fin N→Fin m→Cell b) (codes:∀h x,(f h x).val=(g h x).val)
    (reads:Reads banks g M mem):Reads banks f M mem:=by
  subst b
  have eqn:f=g:=funext fun h=>funext fun x=>Fin.ext (codes h x)
  rw [eqn];exact reads

theorem signed_on_final (l:DescentDatedSeedStartup.Layout) (m:Memory w)
    (signedWidth:DescentSignedCableCodec.width 3 256*l.packedLanes≤w)
    (fieldsFit:l.operandBits*l.operandLanes≤w) (room:DescentDatedSeedStartup.endAddress X l H g₀ k<2^w)
    (x:Block k) (j:Fin (2*(T).cap)):
    Reads ((DescentDatedSeedStartup.operands X l k H g₀).wire x.val j.val)
      (fun h g=>DescentSignedCableCodec.encode (header x j h g)) l.packedLanes
      (DescentDatedSeedStartup.output X (Equiv.refl _) digits hs₀ l m):=by
  have bounds:DescentSignedCableCodec.width (T).degree (T).cap=DescentSignedCableCodec.width 3 256:=by
    change DescentSignedCableCodec.width (A).degree (A).cap=_
    rw [o.raw.branch,o.seed.capacity]
  apply reads_equal bounds _ _ (code_at X o wide x j)
  exact DescentDatedSeedStartup.signed_read X (Equiv.refl _) digits hs₀ l m signedWidth fieldsFit room (j.val:Fin 512)

end
end Hierarchy.DescentSeedInitialTable

end OAI
