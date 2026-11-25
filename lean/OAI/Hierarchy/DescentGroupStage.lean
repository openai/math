import OAI.Hierarchy.DescentGroupStageData
import OAI.Hierarchy.DescentSelectedHubs
import OAI.Hierarchy.DescentSeedStage

namespace OAI
/-! # The actual group invariant for measured subrounds, including exterior rows -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing DescentHostDirectory DescentColonies StarKeys
open scoped BigOperators Classical
noncomputable section
variable {P : Type} {d : ℕ} {bits : P→ℕ} {F : Type} [Field F]

namespace GroupStage
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {k : ℕ}

def stage (A : GroupStage W G price ε J V k) : StageInput W G (price*A.wire) ε where
  V := J×V
  Atoms := A.Atoms
  k := k
  pos := A.pos
  block := A.block
  hub := fun u=>A.hub (A.pos u).2
  records := A.records
  wire := A.wire
  hist := A.hist
  z := A.z
  cap := A.cap
  Δ := A.degree
  near := groupedNear A.near
  fieldBits := A.fieldBits
  degreeMin := A.degreeMin
  degree := fun v=>(grouped_degree A.near v).le.trans (A.degreeBound v.2)
  wirePos := A.wirePos
  unitPos := A.unitPos
  capPos := A.capPos
  small := A.small
  adjacent := fun e _=>(A.peers e).1
  reverse := fun e _=>(A.peers e).2
  internal := fun e _=>A.same e
  widths := A.widths
  inside := A.incidence.inside
  outside := A.incidence.outside
  q := price
  qpos := A.pricePos
  unitPrice := rfl
  retained := A.retained
  roots := by simpa only [Fintype.card_prod] using A.roots

end GroupStage
end
end Hierarchy.DescentSixParty

namespace Hierarchy.DescentInitialHost
open DescentSixParty StarKeys DescentHostDirectory DescentColonies Computability.BorderVNP.Crossing Catalyst
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
variable (G : PoweredGadget F) {J : Type} [Fintype J] [DecidableEq J]
variable {R s r : ℕ} (digits : Fin R≃J×Block r) (c : (initialGroup X R s).Choice)
local notation "N" => X.network.copyGraph

def source_group {ε : ℝ} (q : ℝ) (w hist z : ℕ) (field : 0<r) (hq : 0<q)
    (hw : 0<w) (hz : 0<z) (units : s=z*G.b) (room : 3*(w*s)+hist≤256*(w*s))
    (retained : (q*hist)*((R*Fintype.card (N).Site:ℕ):ℝ)≤ε)
    (root : ((Fintype.card J*Fintype.card (Site N):ℕ):ℝ)*
      ((2:ℝ)^DescentHostDegree.packExponent 20 3*(q*((w*s*256:ℕ):ℝ)))≤ε) :
    GroupStage ((initialGroup X R s).state c) G q ε J (Site N) r := by
  let T := seedStage X G digits c q w hist z field hq hw hz units room retained root
  refine {
    Atoms := T.Atoms
    wire := w
    hist := hist
    z := z
    cap := 256
    degree := 3
    pos := seedPos X c digits
    block := seedBlock X c digits
    near := near N
    hub := hubFlag N
    records := seedRecords X c
    fieldBits := field
    degreeMin := by decide
    degreeBound := («initialize» X).1
    symmetric := near_symm N
    pricePos := hq
    wirePos := hw
    unitPos := hz
    capPos := by decide
    small := T.small
    saturated := ?_
    noHubAtoms := ?_
    peers := ?_
    same := ?_
    incidence := ⟨T.inside,T.outside⟩
    widths := T.widths
    retained := T.retained
    roots := ?_ }
  · rintro ⟨j,v⟩ hv i
    cases v with
    | inl v => cases hv
    | inr t =>
      change blockMass _ (seedPos X c digits) (seedBlock X c digits)
        (((initialGroup X R s).state c).siteUnits (seedHub X c) (seedRecords X c) w 256 hist)
        (j, Sum.inr t) i = w*(z*G.b)*256
      exact (seed_hub_full X c digits w hist j t i).trans
        (by rw [←units, Nat.mul_comm 256])
  · rintro ⟨j,v⟩ hh
    cases v with
    | inl v=>cases hh
    | inr t=>rfl
  · rintro ⟨i,e⟩
    exact ⟨Finset.mem_map.mpr ⟨_,(wire_near N e).1,rfl⟩,Finset.mem_map.mpr ⟨_,(wire_near N e).2,rfl⟩⟩
  · rintro ⟨i,e⟩
    rfl
  · simpa only [←units] using root

end
end Hierarchy.DescentInitialHost

end OAI
