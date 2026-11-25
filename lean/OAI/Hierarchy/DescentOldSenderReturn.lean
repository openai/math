import OAI.Hierarchy.DescentOldSenderPhysical
import OAI.Hierarchy.DescentResetOppositeRectangle

namespace OAI
/-! # Sending an emitted old ticket to the matching signed donor on the measured GL rows -/
namespace Hierarchy.DescentOldSenderReturn
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentIssuedFallbackPanel DescentSIMDLookup DescentSixParty
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentHostDirectory DescentColonies DescentGL
open DescentResetOppositePayload DescentPlainTerminal
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i b H G m c : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {pow : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W pow price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J↪Fin G) (hosts : V↪Fin H) (word : Block m≃J×Block k) (basis : Layout m) (small : c≤ m)
local notation "L" => 2^(m-c)
local notation "E"=>DescentSharedCableNames.Stage.Grain A
local notation "addr"=>DescentIssuedFallbackPanel.address A native S ready
local notation "remix"=>rearrange basis
local notation "adj"=>hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))
local notation "chart"=>fun hi lo=>word ((remix).symm (join small hi lo))
local notation "old"=>DescentSharedCableNames.Stage.Host J V k
local notation "signed"=>rectangular (b:=b) A native S ready groups hosts

def previousSigned (lo : Fin L) (j : Fin (2*A.cap)) (h : Fin H) (hi : Block c) : Cell b :=
  signed ((chart hi lo).2) j h (groups (chart hi lo).1)

local notation "names" => cableNames k (groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))

theorem previous_signed_at (v : V) (hi : Block c) (lo : Fin L) (j : Fin (2*A.cap)) :
    previousSigned (b:=b) A native S ready groups hosts word basis small lo j (hosts v) hi=
      widened A.degree A.cap b (DescentSharedCableNames.Stage.signedPanel A native S ready names
        (donor word basis small v hi lo) j) := by
  exact congrArg (widened A.degree A.cap b) (signed_at A native S ready groups hosts (donor word basis small v hi lo) j)

/-- Interpretation of an already emitted payload in the old signed address scheme. The
opposite lookup itself executes on the fixed remixed low slice, across physical host ports. -/
def previousPayload (cargo : Fin (2*A.cap)→Fin H→Block c→Fin L→Cell b)
    (x : Block k) (j : Fin (2*A.cap)) (h : Fin H) (g : Fin G) : Cell b :=
  if active : ∃a,groups a=g then
    let pos:=remix (word.symm (active.choose,x))
    cargo j h (high small pos) (low pos)
  else 0

theorem previous_at (cargo : Fin (2*A.cap)→Fin H→Block c→Fin L→Cell b)
    (s : J) (x : Block k) (j : Fin (2*A.cap)) (h : Fin H) :
    previousPayload A groups word basis small cargo x j h (groups s)=
      cargo j h (high small (remix (word.symm (s,x)))) (low (remix (word.symm (s,x)))) := by
  have active : ∃a,groups a=groups s:=⟨s,rfl⟩
  simp only [previousPayload,dite_eq_left active,groups.injective active.choose_spec]

theorem previous_here (cargo : Fin (2*A.cap)→Fin H→Block c→Fin L→Cell b)
    (lo : Fin L) (hi : Block c) (j : Fin (2*A.cap)) (h : Fin H) :
    previousPayload A groups word basis small cargo (chart hi lo).2 j h (groups (chart hi lo).1)=cargo j h hi lo := by
  rw [previous_at]
  simp

def returned (cargo : Fin (2*A.cap)→Fin H→Block c→Fin L→Cell b)
    (s : Bool) (lo : Fin L) (j : Fin (2*A.cap)) (h : Fin H) (hi : Block c) : Cell b :=
  let rows:=previousSigned (b:=b) A native S ready groups hosts word basis small lo
  both A.degree A.cap b (!s) (digits adj (rows j) rows (fun t v a=>cargo t v a lo) h hi)

/-- A physically padded prepared board can have arbitrary ghost rows. All the pointers
followed by a real previous receiver end at real old host names. -/
theorem prepared_return (cargo : Fin (2*A.cap)→Fin H→Block c→Fin L→Cell b)
    (marks : Fin H→Block c→Fin L→Fin (2*A.cap)→Option (DescentSharedCableNames.Stage.Live A.degree A.cap))
    (physical : ∀v hi lo j,marks (hosts v) hi lo j=DescentSharedCableNames.Stage.signedPanel A native S ready
      names (donor word basis small v hi lo) j)
    (s : Bool) (lo : Fin L) (j : Fin (2*A.cap)) (v : V) (hi : Block c) :
    let row:=fun (j : Fin (2*A.cap)) h g=>widened A.degree A.cap b (marks h g lo j)
    both A.degree A.cap b (!s) (digits adj (row j) row (fun t u a=>cargo t u a lo) (hosts v) hi)=
      returned A native S ready groups hosts word basis small cargo s lo j (hosts v) hi := by
  intro row
  have atV (u : V) (z : Fin (2*A.cap)) : row z (hosts u) hi=
      previousSigned A native S ready groups hosts word basis small lo z (hosts u) hi := by
    rw [previous_signed_at]
    exact congrArg (widened A.degree A.cap b) (physical u hi lo z)
  let real := previousSigned (b:=b) A native S ready groups hosts word basis small lo
  have peers :
      (fun t : Slot A.degree A.cap => (adj (hosts v) t.1).elim 0 (fun u => row t.2 u hi)) =
      (fun t : Slot A.degree A.cap => (adj (hosts v) t.1).elim 0 (fun u => real t.2 u hi)) := by
    funext t
    have lift (o : Option V) (f g : Fin H → Cell b) (h : ∀ u, f (hosts u) = g (hosts u)) :
        (o.map hosts).elim 0 f = (o.map hosts).elim 0 g := by
      cases o with
      | none => rfl
      | some v => exact h v
    simp only [host_at A hosts]
    exact lift _ _ _ (fun u => atV u t.2)
  apply congrArg (both A.degree A.cap b (!s))
  exact congrArg₂ (fun q cable => project q cable
    (fun t : Slot A.degree A.cap => (adj (hosts v) t.1).elim 0 (fun u => cargo t.2 u hi lo))
    (fun x y => if DescentResetReciprocalPeer.reaches adj (hosts v) x y then (1 : Cell b) else 0))
    (atV v j) peers

/-- At a true prior signed port, the result of the physical reverse selection on this remixed
slice is the payload at the actual opposite port, including loops and parallel old cables. -/
theorem returned_at (enough : DescentSignedCableCodec.width A.degree A.cap≤b) (positive : 0<b)
    (cargo : Fin (2*A.cap)→Fin H→Block c→Fin L→Cell b) (s : Bool)
    (v : V) (hi : Block c) (lo : Fin L) (z : Fin (2*A.cap)) (e : E)
    (found : atSlot A native S ready s (donor word basis small v hi lo) z=some e) :
    let other:=port A (!s) e
    let y:=remix (oldBlock word other.1)
    returned A native S ready groups hosts word basis small cargo s lo z (hosts v) hi=
      cargo (addr other).2 (hosts other.1.1.2) (high small y) (low y) := by
  intro other y
  let p:=port A s e
  let a:=chart hi lo
  have slot:=(atSlot_iff A native S ready ..).mp found
  have src : p.1=donor word basis small v hi lo:=congrArg Prod.fst slot
  have index : (addr p).2=z:=congrArg Prod.snd slot
  let taken:=previousPayload A groups word basis small cargo
  let rows:=previousSigned (b:=b) A native S ready groups hosts word basis small lo
  have agree : digits adj (rows z) rows (fun t v g=>cargo t v g lo) (hosts v) hi=
      digits adj (signed a.2 z) (signed a.2) (taken a.2) (hosts v) (groups a.1) := by
    change project _ _ _ _=project _ _ _ _
    congr 1
    funext j
    cases adj (hosts v) j.1 with
    | none=>rfl
    | some u=>exact (previous_here A groups word basis small cargo lo hi j.2 u).symm
  have physical:=rectangle A native S ready groups hosts enough positive taken s e
  change both _ _ _ _ (digits adj (signed p.1.2 (addr p).2) (signed p.1.2) (taken p.1.2)
    (hosts p.1.1.2) (groups p.1.1.1))=taken other.1.2 (addr other).2 (hosts other.1.1.2) (groups other.1.1.1) at physical
  rw [index,src] at physical
  change both _ _ _ _ _=_
  rw [agree]
  exact physical.trans (previous_at A groups word basis small cargo other.1.1.1 other.1.2 _ _)

theorem opposite_slot (s : Bool) (e : E) :
    let p:=port A (!s) e
    let y:=remix (oldBlock word p.1)
    atSlot A native S ready (!s) (donor word basis small p.1.1.2 (high small y) (low y)) (addr p).2=some e := by
  intro p y
  apply (atSlot_iff A native S ready ..).2
  apply Prod.ext
  · change p.1 = _
    symm
    exact donor_locates word basis small p.1 p.1.1.2 (high small y) rfl rfl
  · rfl

end
end Hierarchy.DescentOldSenderReturn

end OAI
