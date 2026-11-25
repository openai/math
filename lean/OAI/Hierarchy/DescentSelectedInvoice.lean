import OAI.Hierarchy.DescentSparseStep
import OAI.Hierarchy.DescentRecordedCore

namespace OAI
/-! # The physical matched demands pay the normalized core invoice -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentColonies DescentWalshTables
open scoped BigOperators Classical
noncomputable section

private theorem rescale {B Q X K n : ℝ} (w : ℝ) (hw : 0≤w)
    (invoice : X/2-Real.sqrt (B*Q*X)/2-2*B*K*Q≤n) :
    (w*X)/2-Real.sqrt ((w*B)*Q*(w*X))/2-2*(w*B)*K*Q≤w*n := by
  have back : Real.sqrt ((w*B)*Q*(w*X))=w*Real.sqrt (B*Q*X) := by
    rw [show (w*B)*Q*(w*X)=(w*w)*(B*Q*X) by ring,Real.sqrt_mul (mul_nonneg hw hw),Real.sqrt_mul_self hw]
  rw [back]
  nlinarith only [mul_le_mul_of_nonneg_left invoice hw]

private theorem colorPick_mem {n : ℕ} {P : Type*} {bits : P → ℕ}
    (N : Network n P bits) (core : Finset N.Edge) {C : Type} [Fintype C] [DecidableEq C]
    (group : N.Site → C) (color : N.Site → Bool) (cap : ℕ)
    (t : NativePair N core group color cap × Fin 2) :
    colorPick N core group color cap t ∈ core := by
  unfold colorPick
  apply pairedCore_mem

variable {V : Type} [Fintype V] [DecidableEq V] {k d : ℕ} {P : Type*} {bits : P→ℕ}
variable {F : Type*} [Field F] (A : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (position : A.graph.Site→V) (block : A.graph.Site→Block k) (full : A.graph.Site→ℕ)
variable (near : V→Finset V) (D a pairCap unit : ℕ)
variable (small : ∀ (v : V) (x : Block k), blockMass A.graph position block full v x ≤ unit*pairCap)
local notation "home" => occupiedHome A.graph position block full near D a (unit*pairCap) small
local notation "Col" => (occupied A.graph (unit*pairCap) near D a (blockMass A.graph position block full) small position block)

/-! The affine color supplied by the native scan determines each selected pair. -/
set_option maxHeartbeats 1200000 in
omit [Fintype V] in
theorem selected_invoice_of_bound (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (hu : 0<unit)
    (covered : ∀v,unit*live (nativeTraffic A.graph A.core home) v≤full v)
    (adj : ∀e∈A.core,position (A.graph.dst e)∈near (position (A.graph.src e)))
    (rev : ∀e∈A.core,position (A.graph.src e)∈near (position (A.graph.dst e)))
    (same : ∀e∈A.core,block (A.graph.src e)=block (A.graph.dst e))
    (z : ℕ) (fixed : ∀e∈A.core,A.graph.width e=z*G.b) (u : ℝ) (scale : 0<u) (alpha : Bits k) (beta : ZMod 2)
    (balanced : affineBalance A.graph A.core position block full near D a pairCap unit small alpha beta) :
      let color := fun v=>decide (binaryRow alpha ((DescentColonies.address k).symm (block v))+beta=0)
      let I := NativePair A.graph A.core home color pairCap
      let pick := colorPick A.graph A.core home color pairCap
      let Q := Fintype.card Col
      let K := (Δ+1)*(D+1+2*2^D)
      let B := u*(z*G.b:ℕ)*pairCap
      (∀t,pick t∈A.core) ∧ (∀i s,A.graph.width (pick (i,s))=z*G.b) ∧
      (u*A.liveWidth)/2-Real.sqrt (B*Q*(u*A.liveWidth))/2-2*B*K*Q≤u*(G.b*(∑ _i : I,z):ℕ) := by
  have h := sparse_pairs_of_bound A.graph A.core position block full near D a pairCap unit small
    Δ degree hu covered adj rev same alpha beta balanced
  let col := fun v=>decide (binaryRow alpha ((DescentColonies.address k).symm (block v))+beta=0)
  let pick := colorPick A.graph A.core home col pairCap
  have inCore (t : NativePair A.graph A.core home col pairCap × Fin 2) : pick t∈A.core :=
    colorPick_mem A.graph A.core home col pairCap t
  refine ⟨inCore,fun i s=>fixed _ (inCore _),?_⟩
  dsimp only at h ⊢
  have total : A.liveWidth=(z*G.b)*A.core.card := uniform_volume A.graph A.core fixed
  rw [total]
  let scale' := u*(z*G.b:ℕ)
  have inv := rescale scale' (by dsimp [scale'];positivity) h
  dsimp [scale'] at inv
  let pairs : ℕ := Fintype.card (NativePair A.graph A.core home col pairCap)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.cast_mul] at inv ⊢
  convert inv using 1
  all_goals first
    | change u*((G.b:ℝ)*((pairs:ℝ)*(z:ℝ))) = (u*((z:ℝ)*(G.b:ℝ)))*(pairs:ℝ)
      ring
    | ring_nf

omit [Fintype V] in
/-- Both the counted old core and the selected graph edges use the same
normalization. The local binary phase determines the physical pick in every
old block and the total allowance only pays the actual finite neighbor support. -/
theorem selected_invoice (Δ : ℕ) (degree : ∀v,(near v).card≤Δ) (hu : 0<unit)
    (covered : ∀v,unit*live (nativeTraffic A.graph A.core home) v≤full v)
    (adj : ∀e∈A.core,position (A.graph.dst e)∈near (position (A.graph.src e)))
    (rev : ∀e∈A.core,position (A.graph.src e)∈near (position (A.graph.dst e)))
    (same : ∀e∈A.core,block (A.graph.src e)=block (A.graph.dst e))
    (z : ℕ) (fixed : ∀e∈A.core,A.graph.width e=z*G.b) (u : ℝ) (scale : 0<u) :
    ∃ (alpha : Bits k) (beta : ZMod 2),
      let color := fun v=>decide (binaryRow alpha ((DescentColonies.address k).symm (block v))+beta=0)
      let I := NativePair A.graph A.core home color pairCap
      let pick := colorPick A.graph A.core home color pairCap
      let Q := Fintype.card Col
      let K := (Δ+1)*(D+1+2*2^D)
      let B := u*(z*G.b:ℕ)*pairCap
      (∀t,pick t∈A.core) ∧ (∀i s,A.graph.width (pick (i,s))=z*G.b) ∧
      (u*A.liveWidth)/2-Real.sqrt (B*Q*(u*A.liveWidth))/2-2*B*K*Q≤u*(G.b*(∑ _i : I,z):ℕ) := by
  obtain ⟨alpha,beta,h⟩ := exists_affineBalance A.graph A.core position block full near D a pairCap unit small hu covered
  exact ⟨alpha,beta,selected_invoice_of_bound A G position block full near D a pairCap unit small
    Δ degree hu covered adj rev same z fixed u scale alpha beta h⟩

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
