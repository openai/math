import OAI.Hierarchy.DescentRecordedStencilCell
import OAI.Hierarchy.DescentResetPeerGoodInputs

namespace OAI
/-! # The sampled good-root flag from the actual recorded predecessor stencil -/
namespace Hierarchy.DescentSixParty.ClosedReset.Recorded
open DescentCompiler DescentColonies DescentIssuedFallbackPanel DescentGL DescentPlainTerminal DescentPlainTerminal.Suffix
open DescentSIMDLookup DescentResetHostSize DescentRotorRootPresence
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (recorded : B.Recorded p)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "r" => (Z).k-cc
local notation "old" => input.placement
local notation "full" => (old).wire*((old).z*G.b)*(old).cap
local notation "hs" => B.frame.enough.trans (Nat.sub_le ..)
local notation "here" v => B.frame.host v

include recorded in
/-- Only the low flag of the sampled old cell participates in the root decision. It
comes from that original cell's hub flag and the actual selected exceptional classes. -/
theorem private_mode {nbits t : ℕ} (μ : Layout (Z).k) (won : HEq μ B.frame.basis)
    (level : r < 2^nbits) (one : 1 < 2^nbits) (capacity : 2^r*full < 2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*(old).degree))
    (v : input.V) (hi : Block cc) (lo : Block r) :
    (realPanel (reset:=B) B.keyWidth μ nbits t v hi lo).val%2=
      Bool.toNat (decide ((Z).placement.hub (here v) ∨
        (here v,group ((Z).placement.b (here v)) (join (((T).commonLow (here v)).trans ((Z).placement.depth _)) hi lo))∈(Z).placement.keys)) := by
  have read:=recorded.stencil_cell B.keyWidth μ won level one capacity shape active quotaPos degreePos v hi lo
  dsimp only at read
  have tick : group ((Z).placement.b (here v))
      (join hs hi (Fin.cast (congrArg (fun z=>2^(z-cc)) B.keyWidth) lo))=
    group ((Z).placement.b (here v)) (join (((T).commonLow (here v)).trans ((Z).placement.depth _)) hi lo) := by
    simp only [group,DescentColonies.width,join,Fin.val_cast,B.keyWidth]
  rw [read,Equiv.apply_symm_apply,tick]
  let flag:=((old).hub v || decide ((here v,group ((Z).placement.b (here v))
    (join (((T).commonLow (here v)).trans ((Z).placement.depth _)) hi lo))∈(Z).placement.keys))
  have same : Bool.toNat (decide ((Z).placement.hub (here v) ∨
    (here v,group ((Z).placement.b (here v)) (join (((T).commonLow (here v)).trans ((Z).placement.depth _)) hi lo))∈(Z).placement.keys))=flag.toNat := by
    simp [flag,B.frame.rotorHub]
  rw [same]
  change (2*_+flag.toNat)%2=flag.toNat
  cases flag <;> simp

open DescentFallbackPeriod.Projected.Receiver
variable {H a : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "num" => Fintype.card input.V

include recorded in
/-- At every actual old host the three broadcast inputs recover the calendar
capacity, its attained depth and the selected flag at the sampled old block. -/
theorem private_good_inputs {nbits t : ℕ} (μ : Layout (Z).k) (won : HEq μ B.frame.basis)
    (level : r < 2^nbits) (one : 1 < 2^nbits) (capacity : 2^r*full < 2^nbits)
    (shape : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*(old).degree))
    (levels : Fin H→ℕ) (values : Fin H→Block cc→Block r→Cell t)
    (attained : ∀v,levels (id_ v)=(Z).placement.b (here v))
    (stamped : ∀v hi lo,values (id_ v) hi lo=realPanel (reset:=B) B.keyWidth μ nbits t v hi lo)
    (precision : t ≤ a) (depthBits : r+1 < 2^a) (capBits : (old).cap < 2^a)
    (v : input.V) (hi : Block cc) (root : Code r) :
    let head:=goodInput cc a (old).cap num levels (fun v hi lo=>((values v hi lo).val:Cell a))
      root (id_ v) hi
    (head 0).val=(old).cap ∧ (head 1).val=(Z).placement.b (here v)-cc+1 ∧
    (head 2).val%2=Bool.toNat (decide ((Z).placement.hub (here v) ∨
      (here v,group ((Z).placement.b (here v))
        (join (((T).commonLow (here v)).trans ((Z).placement.depth _)) hi (sample root)))∈(Z).placement.keys)) := by
  let x:=values (id_ v) hi (sample root)
  have exactX : x.val < 2^a:=x.isLt.trans_le (Nat.pow_le_pow_right (by decide) precision)
  have inside : (id_ v).val < num:=(input.vertex v).isLt
  have small : (Z).placement.b (here v)-cc+1 < 2^a:=
    (Nat.succ_le_succ (Nat.sub_le_sub_right ((Z).placement.depth (here v)) cc)).trans_lt depthBits
  dsimp only
  refine ⟨Fin.val_cast_of_lt capBits,?_,?_⟩
  · change (((depthDigit cc num levels (id_ v):ℕ):Cell a).val)=_
    simp only [depthDigit, inside, ↓reduceIte, attained, Fin.val_cast_of_lt small]
  · change ((x.val:Cell a).val)%2=_
    rw [Fin.val_cast_of_lt exactX]
    change (values (id_ v) hi (sample root)).val%2=_
    rw [stamped]
    exact recorded.private_mode μ won level one capacity shape active quotaPos degreePos v hi (sample root)


end
end Hierarchy.DescentSixParty.ClosedReset.Recorded

end OAI
