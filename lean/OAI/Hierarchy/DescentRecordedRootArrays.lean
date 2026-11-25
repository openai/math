import OAI.Hierarchy.DescentRecordedRootSnapshot
import OAI.Hierarchy.DescentResetStemClosedStencil

namespace OAI
/-! # Original fallback arrays from the recorded signed receiver -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentCompiler DescentSIMDLookup DescentGL DescentColonies DescentFallbackPeriod.Projected
open DescentPacking.PackedMatch.Local.Stage DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open DescentPlainTerminal DescentPlainTerminal.Suffix DescentRelativeContacts DescentGroupPeerOrder
open DescentStageEdgeReceipt DescentSharedBookScan DescentRosterOrder DescentFallbackShapeTable
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail H field p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fit" => B.frame.enough.trans (Nat.sub_le ..)
local notation "whole" => (A).wire*((A).z*G.b)*(A).cap
local notation "own" u => B.frame.host ((A).pos u).2
local notation "idx" u => StarKeys.filled W.graph (A).pos (A).block digits u

private theorem endpoint_word (s : Bool) (e : Grain A) :
    let u:=endSite A s e
    ClosedReset.Window.signedStemWord B s (home A u)=
      2*cell (m-cc) (shortName cc ((T).code ((T).home u))).2+
        ((A).hub ((A).pos u).2 || decide ((own u,group ((Z).placement.b (own u))
          (rearrange B.frame.basis (idx u)))∈(Z).placement.keys)).toNat := by
  intro u
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,order,vertex,edgeName,siteName⟩
  rcases B with ⟨count,rfl,grainFit,old,orderEq,R,T₀,age,date,extent,tickets,unit,dim,
    width,graph,frm,roster,raw,place,hub,valid,grain,wireEq,atoms,branch,capacity⟩
  let ds:=S.resetInputDigits ctl.base ctl.radix i
  change 2*cell (R.k-T₀.commonDepth) (shortName T₀.commonDepth (T₀.code
    (GroupStage.fallbackCell phase S ready ds R T₀ frm s (home phase u)))).2+
    (GroupStage.exceptionalCell phase S ready ds R T₀ frm (home phase u)).toNat=_
  dsimp only [u]
  rw [GroupStage.cell_home phase S ready ds R T₀ frm s e,
    GroupStage.issued_base_mode phase S ready ds R T₀ frm (endSite phase s e)]
  refine congrArg₂ Nat.add ?_ rfl
  apply congrArg (2 * ·)
  exact congrArg (fun depth => cell depth _) (congrArg (· - T₀.commonDepth) extent)


/-- The word at an old actor can be addressed by recombining its group and block,
then applying the chosen permutation and splitting it at the common depth. -/
def originalWord (nbits t : ℕ) (u : Host (Fin (S.groupCount i)) input.V k) : ℕ :=
  let y:=rearrange B.frame.basis (oldBlock digits u)
  (ClosedReset.Recorded.realPanel (reset:=B) rfl B.frame.basis nbits t u.1.2 (high fit y) (low y)).val

theorem original_donor (nbits t : ℕ) (v : input.V) (hi : Block cc) (lo : Block (m-cc)) :
    originalWord B nbits t (donor digits B.frame.basis fit v hi lo)=
      (ClosedReset.Recorded.realPanel (reset:=B) rfl B.frame.basis nbits t v hi lo).val := by
  simp only [originalWord,donor,oldBlock,Prod.mk.eta,Equiv.symm_apply_apply,Equiv.apply_symm_apply,high_join,low_join]

variable {nbits t : ℕ} (recorded : B.Recorded p) (level : m-cc < 2^nbits) (one : 1 < 2^nbits)
  (capacity : 2^(m-cc)*whole < 2^nbits) (shapeRoom : 2*rows (m-cc) (2^(Z).n) ≤ 2^t)
  (active : 0 < whole) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*(A).degree))

include recorded level one capacity shapeRoom active quotaPos degreePos in
theorem original_end (s : Bool) (e : Grain A) :
    originalWord B nbits t (home A (endSite A s e))=
      ClosedReset.Window.signedStemWord B s (home A (endSite A s e)) := by
  let u:=endSite A s e
  let y : Block m := rearrange B.frame.basis (idx u)
  have measured:=recorded.stencil_cell rfl B.frame.basis HEq.rfl level one capacity shapeRoom active quotaPos degreePos
    ((A).pos u).2 (high fit y) (low (c:=cc) y)
  dsimp only at measured
  simp only [Fin.cast_refl, id_eq, join_high_low, y, Equiv.symm_apply_apply] at measured
  have literal:= (ClosedReset.Recorded.old_roster (reset:=B)).2.2.2.2.2.choose_spec.1 u
  have code : DescentPlainTerminal.fields (((T).code ((T).home u)).2)=
      ClosedReset.Recorded.originalCell (reset:=B) ((A).pos u).2 (idx u):=literal
  rw [endpoint_word B s e]
  change (ClosedReset.Recorded.realPanel (reset:=B) rfl B.frame.basis nbits t
    ((A).pos u).2 (high fit y) (low y)).val=_
  rw [measured,←code,←fields_relative,Stencil.shapeCode_fields]

private theorem double_bit_div (n : ℕ) (b : Bool) : (2*n+b.toNat)/2=n := by
  cases b <;> simp
  omega

variable (pad : Fintype.card input.V ≤ H)
local notation "id_" => input.vertex.trans (Fin.castLEEmb pad)
local notation "key" => Fin.valEmbedding (n:=S.groupCount i)
local notation "names" => cableNames k (groupRank key ((id_).trans Fin.valEmbedding))
local notation "bitsAt" => ClosedReset.Recorded.realPanel (reset:=B) rfl B.frame.basis nbits t
local notation "who" => donor digits B.frame.basis fit

/-- Construct the full snapshot input from the two arrays returned by the same
previous receiver. Empty and padded rows keep the words read by that receiver. -/
def original_arrays (values : Fin H→Block cc→Block (m-cc)→Cell t)
    (ports : Fin H→Block cc→Block (m-cc)→Fin (2*(A).cap)→Option (Live (A).degree (A).cap))
    (neighbors : Fin H→Fin (A).degree→Option (Fin H))
    (row : ∀v j,neighbors (id_ v) j=(hostRoster A ((id_).trans Fin.valEmbedding) v j).map id_)
    (sample : ∀v hi lo,values (id_ v) hi lo=bitsAt v hi lo)
    (cables : ∀v hi lo j,ports (id_ v) hi lo j=signedPanel A (input.order.trans Fin.valEmbedding) S input.valid
      names (who v hi lo) j) (wider : t < field)
    (record : B.Recorded p) (boundLevel : m-cc < 2^nbits) (firstBit : 1 < 2^nbits)
    (massBound : 2^(m-cc)*whole < 2^nbits) (codes : 2*rows (m-cc) (2^(Z).n) ≤ 2^t)
    (paid : 0 < whole) (quotaPaid : 0 < quota S.rounds) (degreePaid : 0 < 32*Nat.clog 2 (2*(A).degree)) :
    OriginalArrays B pad field where
  word :=originalWord B nbits t
  stencil :=fun v hi lo=>(values v hi lo).val
  marks :=ports
  peers :=neighbors
  peerRead :=row
  fits :=by
    intro u
    let y:=rearrange B.frame.basis (oldBlock digits u)
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt (bitsAt u.1.2 (high fit y) (low y)).isLt)
      (Nat.pow_lt_pow_right (by decide : 1 < 2) wider)
  onWire :=original_end B record boundLevel firstBit massBound codes paid quotaPaid degreePaid
  localRead :=by intro v hi lo; rw [original_donor,sample]
  markRead :=by simpa only [B.order_eq] using cables
  shape :=by
    intro v hi lo
    have observed:=record.stencil_cell rfl B.frame.basis HEq.rfl boundLevel firstBit massBound codes paid quotaPaid
      degreePaid v hi lo
    dsimp only at observed
    rw [original_donor,observed]
    simp only [Fin.cast_refl]
    exact double_bit_div _ _

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
