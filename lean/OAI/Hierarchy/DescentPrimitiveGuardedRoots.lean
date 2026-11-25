import OAI.Hierarchy.DescentPrimitivePreparedGuards
import OAI.Hierarchy.DescentPhysicalRootBook
import OAI.Hierarchy.DescentInstalledRotorRoleRun

namespace OAI
/-! # The common attained depth in the actual prepared primitive role packets -/
namespace Hierarchy.DescentPrimitiveBirth
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHostDirectory DescentIssuedRotorRoles
open DescentSixParty.Chronology DescentFallbackPeriod.Projected DescentLaneGates DescentResetGates
open DescentResetHostSize ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- The depth in a valid role packet is tagged one-based. A vacant value and an
out-of-range value both disable the entire depth menu. -/
def activeDepth (r k : ℕ) : Option (Fin (r+1)) :=
  if h:0<k ∧ k≤r+1 then some ⟨k-1,by omega⟩ else none

theorem activeDepth_at (r k : ℕ) (l : Fin (r+1)) : activeDepth r k=some l ↔ k=l.val+1:=by
  unfold activeDepth
  split
  next h=>simp only [Option.some.injEq,Fin.ext_iff];omega
  next h =>
    constructor
    · intro bad
      cases bad
    · intro eqn
      have := l.isLt
      omega

theorem role_depth_source {D cap r : ℕ} (src : RootSources D (2^r) cap) (H : ℕ) (root : Code r) :
    src.roleRow H root (Fin.natAdd (DescentRotorWindowArchive.count D (2^r) cap+1) (0:Fin 2))=src.relativeDepth :=by
  simp [RootSources.roleRow]

theorem role_kind_source {D cap r : ℕ} (src : RootSources D (2^r) cap) (H : ℕ) (root : Code r) :
    src.roleRow H root (Fin.natAdd (DescentRotorWindowArchive.count D (2^r) cap+1) (1:Fin 2))=
      src.self (DescentRotorRootPresence.sample root):=by
  simp [RootSources.roleRow]


section OriginalPage
variable {r n hw field b D cap : ℕ} (src : RootSources D (2^r) cap)
    (board : NonlinearExpanders.Graph n hw) (packet f Ht C groupDigits batches layerBits : ℕ)
    (primitive : CanonicalTag (2^n)→Cell b) (H factor hubBits : ℕ) (neighbors hubs : Bank)
    (ranks : Bool→(Code r×Option (Fin (2^n)))→DescentSharedLeafLookup.Header)
local notation "book" => src.specification (field:=field) board packet f Ht C groupDigits batches layerBits primitive H factor hubBits neighbors hubs ranks
theorem prior_role_value (side : Bool) (root : Code r) (gate : Fin (2^n))
    (x : Fin (guardInputs D (2^r) cap)→Cell field) :
    ((book).table (side,.inl (root,.inr gate))).2.law (encode field _ x)=
      guarded (D:=D) (L:=2^r) (cap:=cap) n r packet f groupDigits batches layerBits primitive side root.val gate x:=by
  change guarded (D:=D) (L:=2^r) (cap:=cap) n r packet f groupDigits batches layerBits primitive side root.val gate
    ((encode field _).symm (encode field _ x)) = _
  rw [Equiv.symm_apply_apply]
end OriginalPage

namespace Layout
variable (z : DescentPrimitiveBirth.Layout) {D cap field w : ℕ}
set_option quotPrecheck false
local notation "N" => z.rotorBits
local notation "r" => z.residual
local notation "rootWidth" => 2^r
local notation "P" => z.placement
local notation "J" => (P).groups*(P).blocks
local notation "H" => (P).oldHosts
local notation "M" => z.sourceLanes
local notation "Q" => Fin z.roots
abbrev GuardPacket (D cap field : ℕ) :=Fin (guardInputs D rootWidth cap)→Cell field

variable (pay f groupDigits layers : ℕ) (primitive : CanonicalTag (2^z.rotorBits)→Cell z.rootBits)
  (inputs : Fin z.roots → Fin (z.residual+1) → Fin z.placement.oldHosts →
    Fin (z.placement.groups*z.placement.blocks) → z.GuardPacket D cap field)

def observedWord (q : Q) (l : Fin (r+1)) (h : Fin H) (g : Fin J) :=
  let p:=rootParts r N q
  if p.2.1.val<2^l.val then
    guarded (D:=D) (L:=rootWidth) (cap:=cap) N r pay f groupDigits z.stop layers primitive
      p.1 (l.val,p.2.1.val) p.2.2 (inputs q l h g)
  else 0

theorem observed_depth (floor : ℕ) (m : Memory w) (k : Fin H→Fin J→ℕ)
    (read : ∀q l B,guards floor H J M r N D q l=some B→
      Source (.lookup B .row) (fun h g=>z.observedWord pay f groupDigits layers primitive inputs q l h g) M m)
    (common : ∀q l h g,(flagPart (D:=D) (L:=rootWidth) (cap:=cap) (inputs q l h g) 0).val=k h g) :
    z.Observed (guards floor H J M r N D) m (fun h g=>activeDepth r (k h g))
      (z.observedWord pay f groupDigits layers primitive inputs):=by
  constructor
  · intro q l B yes
    have eqn h g : (if activeDepth r (k h g)=some l then z.observedWord pay f groupDigits layers primitive inputs q l h g else 0)=
        z.observedWord pay f groupDigits layers primitive inputs q l h g:=by
      by_cases here:activeDepth r (k h g)=some l
      · simp [here]
      · have notHere:k h g≠l.val+1:=fun hit=>here ((activeDepth_at _ _ _).mpr hit)
        simp [here,observedWord,guarded,common,notHere]
    simpa only [eqn] using read q l B yes
  · intro q l no h g _
    have absent : ¬(rootParts r N q).2.1.val<2^l.val:=by
      intro fit
      simp [guards,rootPage,fit] at no
    simp [observedWord,absent]

theorem observed_active (q : Q) (l : Fin (r+1)) (h : Fin H) (g : Fin J)
    (present : (rootParts r N q).2.1.val<2^l.val)
    (relative : (flagPart (D:=D) (L:=rootWidth) (cap:=cap) (inputs q l h g) 0).val=l.val+1)
    (good : (flagPart (D:=D) (L:=rootWidth) (cap:=cap) (inputs q l h g) 1).val%2=0) :
    z.observedWord pay f groupDigits layers primitive inputs q l h g=
      issue (D:=D) (L:=rootWidth) (cap:=cap) N r pay f groupDigits z.stop layers primitive
        (rootParts r N q).1 (l.val,(rootParts r N q).2.1.val) (rootParts r N q).2.2
        (chartPart (D:=D) (L:=rootWidth) (cap:=cap) (inputs q l h g)):=by
  simp [observedWord,present,guarded,relative,good]

end Layout
end
end Hierarchy.DescentPrimitiveBirth

end OAI
