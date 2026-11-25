import OAI.Hierarchy.DescentPhysicalResetJointScene
import OAI.Hierarchy.DescentPrivateMaskPeriod
import OAI.Hierarchy.DescentContactOutputDate

namespace OAI
/-! # Dated private and public target words for the four actual peer ranks -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentResetDenseOperand DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput) (base : ℕ)
local notation "co₀" => v.contactShape
local notation "pr₀" => v.privateShape
local notation "pitch₀" => v.front.contactLayout (v.actorEnd base)
local notation "h₀" => v.jointEnd base
local notation "role₀" => Fin 3
local notation "C₀" => (co₀).sockets
local notation "D₀" => (pr₀).keys

/-- The endpoint code for each private wire combines its proper raw shape with the
reached old receiver's compact self-halo ordinal. Both endpoints are at that old host. -/
def privateJoint (x : Fin (pr₀).blocks) (key : Fin D₀) (role : Fin 3) : Operand :=
  if role.val<2 then
    .privateEndpoint (Nat.clog 2 (v.front.peer.oldDegree+2)) ((pr₀).operand h₀ key role x) (v.peerAux base 0)
  else .compact (v.peerAux base 1)

def privateRaw (x : Fin (pr₀).blocks) (key : Fin D₀) : Fin 9→Operand :=
  let units:=Operand.sparse ((pr₀).operand h₀ key 2 x)
  let roles:=v.privateJoint base x key
  ![units,roles 0,roles 1,roles 2,.compact (.lit 0),.compact (.lit 0),.compact (.lit 0),
    .compact (v.peerAux base 2),units]

/-- Decode the two static sectors of the published job. A malformed or padded public
index has a deterministic zero operand. -/
def jobAt (n : ℕ) : Option ((Fin (co₀).blocks×Fin C₀) ⊕ (Fin (pr₀).blocks×Fin D₀)) :=
  let step:=C₀+D₀
  let x:=n/step
  let j:=n%step
  if c:x<(co₀).blocks ∧ j<C₀ then some (.inl (⟨x,c.1⟩,⟨j,c.2⟩))
  else if p:x<(pr₀).blocks ∧ C₀≤j ∧ j-C₀<D₀ then some (.inr (⟨x,p.1⟩,⟨j-C₀,p.2.2⟩))
  else none

def actualRaw (n : ℕ) (i : Fin 9) : Operand :=
  match v.jobAt n with
  | some (.inl (x,j)) => (co₀).raw (v.trunkEnd base) x j (.compact (v.peerAux base 2)) i
  | some (.inr (x,j)) => v.privateRaw base x j i
  | none => .compact (.lit 0)

def actualTarget (n : ℕ) : Operand :=
  let role : Fin 3:=⟨n%3,Nat.mod_lt _ (by decide)⟩
  match v.jobAt (n/3) with
  | some (.inl (x,j))=>(co₀).candidate (v.trunkEnd base) x j ⟨role.val+1,by omega⟩
  | some (.inr (x,j))=>v.privateJoint base x j role
  | none=>.compact (.lit 0)

theorem privateJob (x : Fin (pr₀).blocks) (j : Fin D₀) :
    v.jobAt (x.val*(C₀+D₀)+(C₀+j.val))=some (.inr (x,j)) := by
  let s:=C₀+D₀
  have lt : C₀+j.val<s:=Nat.add_lt_add_left j.isLt _
  have pos : 0<s:=Nat.zero_lt_of_lt lt
  have quo : (x.val*s+(C₀+j.val))/s=x.val:=by
    rw [Nat.mul_comm x.val s,Nat.mul_add_div pos,Nat.div_eq_of_lt lt,Nat.add_zero]
  have rem : (x.val*s+(C₀+j.val))%s=C₀+j.val:=by
    rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt lt]
  simp [jobAt,←show s=C₀+D₀ from rfl,quo,rem,x.isLt,j.isLt]

theorem contactJob (x : Fin (co₀).blocks) (j : Fin C₀) :
    v.jobAt (x.val*(C₀+D₀)+j.val)=some (.inl (x,j)) := by
  let s:=C₀+D₀
  have lt : j.val<s:=j.isLt.trans_le (Nat.le_add_right ..)
  have pos : 0<s:=Nat.zero_lt_of_lt lt
  have quo : (x.val*s+j.val)/s=x.val:=by rw [Nat.mul_comm x.val s,Nat.mul_add_div pos,Nat.div_eq_of_lt lt,Nat.add_zero]
  have rem : (x.val*s+j.val)%s=j.val:=by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt lt]
  simp [jobAt,←show s=C₀+D₀ from rfl,quo,rem,x.isLt,j.isLt]

theorem receipt_order : v.massEnd base≤h₀ ∧ h₀≤v.privateEnd base :=by
  have p:=(pr₀).cuts h₀
  refine ⟨?_,p.1.trans p.2⟩
  unfold jointEnd
  rw [JointAtlas.shift]
  exact Nat.le_add_right ..

theorem mixed_term_room {w : ℕ} (roof : v.privateEnd base<2^w) :
    (∀q,(v.actualTarget base q).term.Fits w (v.privateEnd base)) ∧
      ∀q f,(v.actualRaw base q f).term.Fits w (v.privateEnd base) := by
  have bounds:=v.receipt_order base
  have co := bounds.1.trans bounds.2
  have contact (x : Fin (co₀).blocks) (q : Fin C₀) (f : Fin 4) :
      ((co₀).candidate (v.trunkEnd base) x q f).term.Fits w (v.privateEnd base):=
    ProtocolRAMGeneratedWrite.fits_mono _ co ((co₀).fields_fit (v.trunkEnd base) (co.trans_lt roof) x q f)
  have aux (j : Fin 4) : (v.peerAux base j).Fits w (v.privateEnd base) :=
    ProtocolRAMGeneratedWrite.fits_mono _ bounds.2 (v.aux_fits base (bounds.2.trans_lt roof) j)
  have private_ (x : Fin (pr₀).blocks) (q : Fin D₀) (i : Fin 3) :
      (v.privateJoint base x q i).term.Fits w (v.privateEnd base) := by
    unfold privateJoint
    split
    · exact DescentContactEndpointFields.fits _ _ _ _ ((pr₀).output_fits h₀ q i x roof) (aux 0)
    · exact aux 1
  constructor
  · intro n
    cases e:v.jobAt (n/3) with
    | none=>simp [actualTarget,e,Operand.term,Expr.Fits]
    | some t=>
      rcases t with ⟨x,q⟩|⟨x,q⟩
      · simpa only [actualTarget,e] using contact x q ⟨n%3+1,by omega⟩
      · simpa only [actualTarget,e] using private_ x q ⟨n%3,Nat.mod_lt _ (by decide)⟩
  · intro n i
    cases e:v.jobAt n with
    | none=>simp [actualRaw,e,Operand.term,Expr.Fits]
    | some t=>
      rcases t with ⟨x,q⟩|⟨x,q⟩
      · simp only [actualRaw,e]
        fin_cases i
        · exact contact x q 0
        · exact contact x q 1
        · exact contact x q 2
        · exact contact x q 3
        · trivial
        · trivial
        · trivial
        · exact aux 2
        · exact contact x q 0
      · simp only [actualRaw,e]
        fin_cases i
        · exact (pr₀).output_fits h₀ q 2 x roof
        · exact private_ x q 0
        · exact private_ x q 1
        · exact private_ x q 2
        · trivial
        · trivial
        · trivial
        · exact aux 2
        · exact (pr₀).output_fits h₀ q 2 x roof

variable (old : v.OriginalOperands base)
def privateInputs := (pr₀).fieldTerm h₀ pitch₀ old.pages

theorem private_inputs_fit {w : ℕ} (earlier : ∀s t,(old.pages s t).Fits w h₀)
    (room : v.privateEnd base<2^w) : ∀q,(v.privateInputs base old q).Fits w ((pr₀).projected h₀) := by
  have p:=(v.front.peer.ordered (v.front.peers (v.actorEnd base)))
  have after : v.front.peers (v.actorEnd base)≤v.massEnd base :=
    p.1.trans (p.2.1.trans (p.2.2.1.trans (p.2.2.2.trans (v.peer_prefix base))))
  have before : (pitch₀).markerBase≤v.front.peers (v.actorEnd base) :=
    (pitch₀).ordered.2.2.2.1.trans (pitch₀).ordered.2.2.2.2
  exact (pr₀).incoming_fits h₀ pitch₀ old.pages earlier
    (before.trans (after.trans (v.receipt_order base).1)) (((pr₀).cuts h₀).2.trans_lt room)

def privatePhase {w : ℕ} (batch : 0<(pr₀).batch) (blocks : 0<(pr₀).blocks)
    (fits : ∀q,(v.privateInputs base old q).Fits w ((pr₀).projected h₀)) (roof : v.privateEnd base<2^w) :
    NativePhase w:=(pr₀).phase h₀ pitch₀ old.pages batch blocks fits roof

theorem private_any {w : ℕ} (m : Memory w) (batch : 0<(pr₀).batch) (blocks : 0<(pr₀).blocks)
    (fits : ∀q,(v.privateInputs base old q).Fits w ((pr₀).projected h₀)) (roof : v.privateEnd base<2^w) :
    let phase:=v.privatePhase base old batch blocks fits roof
    phase.Runs m ∧ ∀z,z<h₀ ∨ v.privateEnd base≤z→phase.image m z=m z := by
  have paid:=(pr₀).any h₀ pitch₀ old.pages m batch blocks fits roof
  exact ⟨paid.1,paid.2.2⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
