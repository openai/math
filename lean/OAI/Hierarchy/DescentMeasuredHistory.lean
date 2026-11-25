import OAI.Hierarchy.DescentScannedShrink
import OAI.Hierarchy.DescentNormalize

namespace OAI
/-! # Finite weighted histories of successive measured physical subrounds -/

namespace Hierarchy.DescentSixParty
open DescentColonies Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {d : ℕ} {P : Type} {bits : P→ℕ}

/-- Placement and integer charging data available on the incoming graph.
The candidate multiplier, color, matched volume, branch coefficient and
successor weight are computed by the stage. -/
structure StageInput (A : MarkedWorld F d P bits) (G : PoweredGadget F) (u ε : ℝ) where
  V : Type
  [finite : Fintype V]
  [decideV : DecidableEq V]
  Atoms : Type
  k : ℕ
  pos : A.graph.Site→V
  block : A.graph.Site→Block k
  hub : A.graph.Site→Bool
  records : A.graph.Site→List Atoms
  wire : ℕ
  hist : ℕ
  z : ℕ
  cap : ℕ
  Δ : ℕ
  near : V→Finset V
  fieldBits : 0<k
  degreeMin : 2≤Δ
  degree : ∀v,(near v).card≤Δ
  wirePos : 0<wire
  unitPos : 0<z
  capPos : 0<cap
  small : ∀v i,StarKeys.blockMass A.graph pos block (A.siteUnits hub records wire 256 hist) v i≤wire*(z*G.b)*cap
  adjacent : ∀e∈A.core,pos (A.graph.dst e)∈near (pos (A.graph.src e))
  reverse : ∀e∈A.core,pos (A.graph.src e)∈near (pos (A.graph.dst e))
  internal : ∀e∈A.core,block (A.graph.src e)=block (A.graph.dst e)
  widths : ∀e∈A.core,A.graph.width e=z*G.b
  inside : ∀e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false
  outside : ∀e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e)
  q : ℝ
  qpos : 0<q
  unitPrice : q*wire=u
  retained : (q*hist)*(∑v,((records v).length:ℝ))≤ε
  roots : (Fintype.card V:ℝ)*((2:ℝ)^(DescentHostDegree.packExponent 20 Δ)*
    (q*((wire*(z*G.b)*cap):ℕ)))≤ε

attribute [instance] StageInput.finite StageInput.decideV

namespace StageInput
variable {A : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ}
variable (T : StageInput A G u ε) (he : 0≤ε)

include he in
private theorem measured :
    ∃ H : Histories.{_, _, 0} F d P bits, StarKeys.IsScanned A G T.pos T.block T.hub T.records
      T.wire T.hist T.z T.cap T.Δ T.near T.fieldBits T.small H ∧ (∀x,H.value x=A.value x) ∧ (∀c,H.weight c=1) ∧
      ∀c,(H.state c).tetherWidth≤A.tetherWidth ∧
        u*(H.state c).liveWidth≤(1-(2-G.rate)/4)*(u*A.liveWidth)+
          (2-G.rate)*((257*(u*A.tetherWidth)+ε)/4) := by
  have actual := StarKeys.scanned_shrink_named A G T.pos T.block T.hub T.records
    T.wire T.hist T.z T.cap T.Δ T.near T.fieldBits T.degreeMin T.degree T.wirePos
    T.unitPos T.capPos T.small T.adjacent T.reverse T.internal T.widths T.inside T.outside
    T.q ε T.qpos he T.retained T.roots
  simpa only [T.unitPrice] using actual

def result := (measured T he).choose
theorem result_scanned : StarKeys.IsScanned A G T.pos T.block T.hub T.records
    T.wire T.hist T.z T.cap T.Δ T.near T.fieldBits T.small (T.result he) :=
  (measured T he).choose_spec.1
theorem result_value (x : Ports bits) : (T.result he).value x=A.value x :=
  (measured T he).choose_spec.2.1 x

theorem result_weight (c : (T.result he).Choice) : (T.result he).weight c=1 :=
  (measured T he).choose_spec.2.2.1 c

theorem result_bill (c : (T.result he).Choice) :
    ((T.result he).state c).tetherWidth≤A.tetherWidth ∧
        u*((T.result he).state c).liveWidth≤(1-(2-G.rate)/4)*(u*A.liveWidth)+
          (2-G.rate)*((257*(u*A.tetherWidth)+ε)/4) :=
  (measured T he).choose_spec.2.2.2 c
end StageInput

/-- The profile-specific reblocking is read on the exact selected graph. -/
structure SubroundInput (H : Histories F d P bits) (G : PoweredGadget F) {u ε : ℝ} (he : 0≤ε) where
  placement : ∀c,StageInput (H.state c) G u ε
  reblock : ∀ c p,Normalize (((placement c).result he).state p)

namespace Histories
variable {G : PoweredGadget F} {u ε : ℝ} (he : 0≤ε)
variable (H : Histories F d P bits) (data : SubroundInput H G (u:=u) he)
local notation "ports" => data.placement

/-- Keep the actual old choice and append the profile in its own dependent fiber. -/
def extend : Histories F d P bits where
  Choice := Σc : H.Choice,((ports c).result he).Choice
  finite := inferInstance
  state f := (data.reblock f.1 f.2).result
  weight f := H.weight f.1

theorem extend_value (x : Ports bits) : (H.extend he data).value x=H.value x := by
  unfold value extend
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Normalize.value]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [value,StageInput.result_weight,one_mul] using (ports c).result_value he x

theorem extend_bill (hu : 0≤u) {E X : ℝ}
    (before : ∀ c,u*(H.state c).tetherWidth ≤ E ∧ u*(H.state c).liveWidth≤X)
    (f : (H.extend he data).Choice) :
    u*((H.extend he data).state f).tetherWidth ≤ E ∧
    u*((H.extend he data).state f).liveWidth ≤ (1-(2-G.rate)/4)*X+
      (1-(1-(2-G.rate)/4))*(257*E+ε) := by
  obtain ⟨p,c⟩ := f
  obtain ⟨tether,core⟩ := (ports p).result_bill he c
  have next := (data.reblock p c).bills
  have tr := (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (next.2.trans tether)) hu).trans (before p).1
  have reduced := (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr next.1) hu).trans core
  refine ⟨tr,reduced.trans ?_⟩
  have r : 0≤1-(2-G.rate)/4 := by linarith [G.rate_nonneg]
  have g : 0≤(2-G.rate)/4 := by linarith [G.rate_lt_two]
  nlinarith only [mul_le_mul_of_nonneg_left (before p).2 r,
    mul_le_mul_of_nonneg_left (before p).1 g]

end Histories


end
end Hierarchy.DescentSixParty

end OAI
