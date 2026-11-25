import OAI.Hierarchy.DescentPrimitivePaletteToken
import OAI.Hierarchy.DescentResetPrimitiveWords
import OAI.Hierarchy.DescentIssuedRotorRoles

namespace OAI
/-! # One-based printed role words for the actual three reset branches -/
namespace Hierarchy.DescentPrimitivePalette
open DescentSixParty DescentCompiler DescentResetGates DescentKernelHistory DescentEpochTagKeys
open DescentSIMDLookup DescentPackedResetRotorRoles DescentIssuedRotorRoles
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec)

def relayToken : Cell (printedBits G s Z op) :=
  token G s Z op (.inr (.inr (.inl ())))

def freshToken (gate : CanonicalTag (2^op.n)) : Cell (printedBits G s Z op) :=
  token G s Z op (.inr (.inr (.inr gate)))

/-- A static lookup with one key per raw gate number. Both holes and zero-padded
slots remain zero even if the global menu's first entry is an occupied primitive. -/
def decoded (raw : ℕ) : Cell (printedBits G s Z op) :=
  primitive (freshToken G s Z op) raw

theorem decoded_at (gate : CanonicalTag (2^op.n)) :
    decoded G s Z op (role gate)=freshToken G s Z op gate:=
  primitive_read _ gate

theorem decoded_zero : decoded G s Z op 0=0:=primitive_zero _

theorem relayToken_val : (relayToken G s Z op).val=censusCount s+gadgetCount G Z+1:=by
  simp [relayToken,token,codec,Codec.birth,Codec.ofEquiv,finSumFinEquiv_apply_right,finSumFinEquiv_apply_left]

theorem freshToken_val (t : CanonicalTag (2^op.n)) : (freshToken G s Z op t).val=
    censusCount s+(gadgetCount G Z+(1+(Fintype.equivFin _ t).val))+1:=rfl

/-- All four physical origins of a checkpoint cell. Retained cells already contain
one-based words. Padding bypasses all gate and donor reads. -/
inductive PrintedInput (bits : ℕ) where
  | padding
  | retained (prior : Cell bits)
  | relay
  | bank (localRole : ℕ)

def emit : PrintedInput (printedBits G s Z op)→Cell (printedBits G s Z op)
  | .padding=>0
  | .retained prior=>prior
  | .relay=>relayToken G s Z op
  | .bank raw=>decoded G s Z op raw

section Reached
variable {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail p : ℕ}
    {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (menu : Runnable F op) (b : ClosedReset cap ctl) (hp : 0<p) (whole : p∣b.reset.unit)
    (fixed : Chronology.resetSpec b=op) (a : Chronology.Archive W)
    (old : Encoding (Label G s Z op) (dictionary G op menu p) a.bit)
local notation "key" => DescentOrderedReset.grains W b.count b.order
local notation "fit" => (Nat.div_mul_cancel whole).symm
local notation "prg" => b.reset.laneRecipe key (b.reset.unit/p) p hp fit
local notation "next" => (Chronology.resetArchive b p hp whole a).bit
local notation "enc" => Encoding.reset op menu b hp whole fixed a old

/-- The stage-specific transport changes types only. The packed opcode read from
the real rotor is exactly its raw numerical code in the permanent finite table. -/
theorem raw_resetTag (same : actualSpec b=op) (t : CanonicalTag (2^b.reset.n)) :
    role (resetTag op b same t)=role t:=by
  subst op
  rfl

def reachedInput (x : NodeOrder.All next) : PrintedInput (printedBits G s Z op) :=
  Sum.elim (fun v=>.retained (token G s Z op (old.atNode v)))
    (Sum.elim (fun _=>.relay) (fun v : NodeOrder.Global prg=>
      .bank (role ((prg v.1).tag v.2))))
    (resetOrigin b hp whole a x)

theorem reached_emit (x : NodeOrder.All next) :
    emit G s Z op (reachedInput G s Z op menu b hp whole a old x)=token G s Z op ((enc).atNode x):=by
  rw [reset_at op menu b hp whole fixed a old x]
  unfold reachedInput
  rcases resetOrigin b hp whole a x with kept|r|v
  · rfl
  · rfl
  · change decoded G s Z op (role _) = freshToken G s Z op (resetTag op b ((actual_eq b).trans fixed) _)
    rw [←raw_resetTag (G:=G) (op:=op) (b:=b) ((actual_eq b).trans fixed) ((prg v.1).tag v.2)]
    exact decoded_at G s Z op _

theorem published_word (x : Option (NodeOrder.All next)) :
    (emit G s Z op (x.elim .padding (reachedInput G s Z op menu b hp whole a old))).val=
      x.elim 0 (fun n=>((codec (G:=G) op).store ((enc).atNode n)).val+1):=by
  cases x with
  | none=>simp [emit]
  | some n=>exact congrArg Fin.val (reached_emit G s Z op menu b hp whole fixed a old n)

end Reached
end
end Hierarchy.DescentPrimitivePalette

end OAI
