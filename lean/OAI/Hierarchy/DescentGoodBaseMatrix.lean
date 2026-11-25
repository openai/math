import OAI.Hierarchy.DescentTerminalMatrix
import OAI.Hierarchy.DescentPackedWords
import OAI.Hierarchy.DescentSelectedRotor
import OAI.Hierarchy.DescentMatrixScheduler

namespace OAI
/-! # A configured degree-three reset of the good base's original bundle rows -/

namespace Hierarchy.DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits Expander NonlinearExpanders DescentBaseProfile
open scoped BigOperators Classical
noncomputable section
variable {E : Type*} [Fintype E] {K : Type*} [Field K] {n h : ℕ}

/-- The physical layers, tables and packet selections, with coefficient equality
for all possible assignments to the concrete source and destination bundles.
The size counts the complete traversals through the degree-three row paths. -/
structure BaseCircuit (K : Type*) [Field K] (G : Graph n h) (C w u : ℕ) (hw : 0<w)
    (src dst : E → Fin (2^n)) (S : ℝ) where
  layers : ℕ
  choose : Packet w (matrixOfBundles src dst) → Fin layers
  tables : Fin layers → (v : Fin (2^n)) → Fin (2^w) → Fin (2^w) →
    (supplyGraph G.arcs).State (fun _ => Fin (2^(C*w))) v → K
  menu : ∀ π : Equiv.Perm (Fin (2^n)), Configures K G.arcs C w π
  rotation : Fin layers → Equiv.Perm (Fin (2^n))
  selected : ∀r,tables r=fixedTable menu (rotation r)
  routed : ∀p,rotation (choose p) p.1=p.2.1
  proper : ∀p q,choose p=choose q → p.1=q.1 → p=q
  scheduled : ∃ (L : ℕ) (eqn : layers=2*L+1),
    (∀p,Fin.cast eqn (choose p)=Scheduler.color (Scheduler.matrixRun w L (matrixOfBundles src dst))
      (Scheduler.packetIDs (matrixOfBundles src dst) hw p)) ∧
    ∀r v,rotation r v=Scheduler.rotate (Scheduler.matrixRun w L (matrixOfBundles src dst)) (Fin.cast eqn r) v
  realizes : ∀ x y : E → Fin u → Bool,
    (∏ r,attachedLayer (tables r) u
      (fun v => fillRows 0 (fun e => (choose e,e.1)) (packetWord (packetAddress src dst hw) x) (r,v))
      (fun v => fillRows 0 (fun e => (choose e,e.2.1)) (packetWord (packetAddress src dst hw) y) (r,v))) =
        if ∀e,x e=y e then 1 else 0
  bitCost : ((layers * (∑ v : Fin (2^n),Attachment.bitCost
    (fun i => SlotWidth G.arcs C w v ((Fintype.equivFin (Slot G.arcs v)).symm i)) u):ℕ):ℝ)
    ≤21*((2*h+4)*(2*h*C+2):ℕ)*S
  /-- The uniform layer count is computed when the physical reset is installed. -/
  canonicalLayers : layers=2*⌊(10*S)/(((2^n:ℕ):ℝ)*w*u)⌋₊+1

/-- The matrix entries and their actual bundle identities determine a powered
circuit on the common rotor. Ceilings, dummy packets, padding bits, the two
degree-three row paths and all layer multiplicities are included. -/
theorem circuit_of_matrix (G : Graph n h) (C w u : ℕ) (hw : 0<w) (hu : 0<u)
    (menu : ∀ π : Equiv.Perm (Fin (2^n)), Configures K G.arcs C w π)
    (src dst : E → Fin (2^n)) {F B : ℝ} (unit : (u:ℝ)≤B)
    (scale : ((2^n:ℕ):ℝ)^2*w≤F)
    (row : ∀ i,(∑j,(matrixOfBundles src dst i j:ℝ))≤9*F*B/((2^n:ℕ)*u:ℕ))
    (col : ∀ j,(∑i,(matrixOfBundles src dst i j:ℝ))≤9*F*B/((2^n:ℕ)*u:ℕ)) :
    Nonempty (BaseCircuit K G C w u hw src dst (F*B)) := by
  let Y := 2^n
  let m := matrixOfBundles src dst
  let P := Packet w m
  let YR : ℝ := Y
  have hY : 0<YR := by dsimp [YR,Y]; positivity
  have hYone : 1≤YR := by
    dsimp [YR,Y]
    exact_mod_cast Nat.two_pow_pos n
  have hU : (0:ℝ)<u := by exact_mod_cast hu
  have hW : (0:ℝ)<w := by exact_mod_cast hw
  have hS : YR^2*w≤F := scale
  let L := ⌊10*F*B/(YR*w*u)⌋₊
  have hr (i : Fin Y) : (Finset.univ.filter fun e : P => e.1=i).card≤L := by
    rw [packet_rows]
    apply Nat.le_floor
    rw [Nat.cast_sum]
    have packed := row_reset_bound (m i) hw (F:=F) (by simpa only [Fintype.card_fin] using hY) hU unit
      (by simpa only [Fintype.card_fin] using hS)
      (by simpa only [Fintype.card_fin,Nat.cast_mul] using row i)
    simpa only [Fintype.card_fin] using packed
  have hc (j : Fin Y) : (Finset.univ.filter fun e : P => e.2.1=j).card≤L := by
    rw [packet_cols]
    apply Nat.le_floor
    rw [Nat.cast_sum]
    have packed := row_reset_bound (fun i => m i j) hw (F:=F) (by simpa only [Fintype.card_fin] using hY) hU unit
      (by simpa only [Fintype.card_fin] using hS)
      (by simpa only [Fintype.card_fin,Nat.cast_mul] using col j)
    simpa only [Fintype.card_fin] using packed
  let state := Scheduler.matrixRun w L m
  have routing := Scheduler.matrix_correct m hw hr hc
  let choose (e : P) := Scheduler.color state (Scheduler.packetIDs m hw e)
  let rotations (r : Fin (2*L+1)) := Equiv.ofBijective (Scheduler.rotate state r) (routing.1 r)
  have correct := routed_layers menu (fun e : P=>e.1) (fun e=>e.2.1) L choose rotations routing.2.1 routing.2.2
  refine ⟨⟨2*L+1,choose,fun r=>fixedTable menu (rotations r),menu,rotations,fun _=>rfl,routing.2.1,routing.2.2,
    ⟨L,rfl,fun _=>rfl,fun _ _=>rfl⟩,?_,?_,?_⟩⟩
  · intro x y
    rw [correct]
    exact if_congr (packetWord_eq (packetAddress src dst hw) (packetAddress_injective src dst hw) x y) rfl rfl
  · let k := (2*h+4)*(2*h*C+2)
    have kpos : 0≤(k:ℝ) := by positivity
    have cheap : YR*w≤F := by
      have yy := mul_le_mul_of_nonneg_left hYone hY.le
      nlinarith only [mul_le_mul_of_nonneg_right yy hW.le,hS]
    have one : YR*w*u≤F*B := (mul_le_mul_of_nonneg_right cheap hU.le).trans
      (mul_le_mul_of_nonneg_left unit ((mul_nonneg hY.le hW.le).trans cheap))
    have limit : (L:ℝ)≤10*F*B/(YR*w*u) := Nat.floor_le (by
      have f := (mul_nonneg hY.le hW.le).trans cheap
      have b := hU.le.trans unit
      positivity)
    have price := layer_charge kpos hY hW hU limit one
    rw [attached_bit_cost]
    push_cast
    dsimp only [k,YR,Y] at price
    push_cast at price
    linarith only [price]
  · simp only [L,YR,Y,mul_assoc]

/-- The assumption on each occurrence is its total original incident bit load;
all matrix row bounds and the physical height are derived inside the proof. -/
theorem circuit_of_good_base {I T : Type*} [Fintype I] [Fintype T]
    (G : Graph n h) (C w u : ℕ) (hw : 0<w) (hu : 0<u)
    (menu : ∀ π : Equiv.Perm (Fin (2^n)), Configures K G.arcs C w π)
    (cap : T → ℝ) (N : T → ℕ) (wt : I → ℝ) (owner : (Σ t,Fin (N t)) → I)
    {F B : ℝ} (unit : (u:ℝ)≤B) (scale : ((2^n:ℕ):ℝ)^2*w≤F)
    (weights : ∀i,0≤wt i ∧ wt i≤B) (full : ∑i,wt i≤2*(F*B))
    (traffic : ∀t,(N t:ℝ)*u≤cap t) (budget : ∑t,cap t≤2*(F*B))
    (contacts : 4*Fintype.card T≤2^n)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*u≤wt i) :
    ∃ (input : I → Fin (2^n)) (fit : (∑t,rowCount (2^n) (F*B) (cap t))≤2^n)
      (sPos : 0<F*B) (uPos : (0:ℝ)<u),
      Nonempty (BaseCircuit K G C w u hw (input ∘ owner)
        (fun e => outputSlot _ fit (chooseOutput cap N sPos uPos traffic e)) (F*B)) := by
  have hp : (0:ℝ)<u := by exact_mod_cast hu
  have hy : (1:ℝ)≤(2^n:ℕ) := by exact_mod_cast Nat.two_pow_pos n
  have hw1 : (1:ℝ)≤w := by exact_mod_cast hw
  have sy : ((2^n:ℕ):ℝ)≤F := by
    have a := mul_le_mul_of_nonneg_left hy (zero_le_one.trans hy)
    nlinarith only [a,scale,mul_le_mul_of_nonneg_left hw1 (sq_nonneg ((2^n:ℕ):ℝ))]
  have sPos := mul_pos (lt_of_lt_of_le (by positivity : (0:ℝ)<1) (hy.trans sy)) (hp.trans_le unit)
  have yB := mul_le_mul_of_nonneg_right sy (hp.le.trans unit)
  let fit := output_room cap sPos (fun c => (mul_nonneg (Nat.cast_nonneg _) hp.le).trans (traffic c)) budget contacts
  obtain ⟨input,rows,cols⟩ := good_base_matrix cap N wt owner sPos hp unit yB weights full traffic budget contacts actual
  refine ⟨input,fit,sPos,hp,circuit_of_matrix G C w u hw hu menu _ _ unit scale ?_ ?_⟩
  · intro i
    simpa only [Nat.cast_mul,mul_assoc] using rows i
  · intro j
    simpa only [Nat.cast_mul,mul_assoc] using cols j

/-- The paper bills a rational amount for each bundle, independently of its
integer bit width. This form consumes traffic in its original units, and
routes exactly the same named outputs chosen using those capacities. -/
theorem circuit_of_raw_base {I T : Type*} [Fintype I] [Fintype T]
    (G : Graph n h) (C w bits : ℕ) (hw : 0<w) (hb : 0<bits)
    (menu : ∀ π : Equiv.Perm (Fin (2^n)), Configures K G.arcs C w π)
    (cap : T → ℝ) (N : T → ℕ) (wt : I → ℝ) (owner : E → I) (serial : E ↪ (Σ t,Fin (N t)))
    {F B unit : ℝ} (positive : 0<unit) (affordable : unit≤B) (scale : ((2^n:ℕ):ℝ)^2*w≤F)
    (weights : ∀i,0≤wt i ∧ wt i≤B) (full : ∑i,wt i≤2*(F*B))
    (traffic : ∀t,(N t:ℝ)*unit≤cap t) (budget : ∑t,cap t≤2*(F*B))
    (contacts : 4*Fintype.card T≤2^n)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*unit≤wt i) :
    ∃ (input : I → Fin (2^n)) (fit : (∑t,rowCount (2^n) (F*B) (cap t))≤2^n)
      (sPos : 0<F*B), Nonempty (BaseCircuit K G C w bits hw (input ∘ owner)
        (fun e => outputSlot _ fit (chooseOutput cap N sPos positive traffic (serial e))) (F*(B/unit*bits))) := by
  have hp : (0:ℝ)<bits := by exact_mod_cast hb
  have hy : (1:ℝ)≤(2^n:ℕ) := by exact_mod_cast Nat.two_pow_pos n
  have hw1 : (1:ℝ)≤w := by exact_mod_cast hw
  have sy : ((2^n:ℕ):ℝ)≤F := by
    have a := mul_le_mul_of_nonneg_left hy (zero_le_one.trans hy)
    nlinarith only [a,scale,mul_le_mul_of_nonneg_left hw1 (sq_nonneg ((2^n:ℕ):ℝ))]
  have sPos := mul_pos (lt_of_lt_of_le (by positivity : (0:ℝ)<1) (hy.trans sy)) (positive.trans_le affordable)
  have yB := mul_le_mul_of_nonneg_right sy (positive.le.trans affordable)
  let fit := output_room cap sPos (fun c => (mul_nonneg (Nat.cast_nonneg _) positive.le).trans (traffic c)) budget contacts
  obtain ⟨input,rows,cols⟩ := good_base_matrix_raw cap N wt owner serial sPos positive affordable yB weights full traffic budget contacts actual
  have one : 1≤B/unit := (le_div_iff₀ positive).2 (by simpa using affordable)
  have bitPrice : (bits:ℝ)≤B/unit*bits := by simpa using mul_le_mul_of_nonneg_right one hp.le
  have conversion : 9*(F*B)/(((2^n:ℕ):ℝ)*unit)=9*F*(B/unit*bits)/((2^n:ℕ)*bits:ℕ) := by
    push_cast
    field_simp

  refine ⟨input,fit,sPos,circuit_of_matrix G C w bits hw hb menu _ _ bitPrice scale ?_ ?_⟩
  · exact fun i => (rows i).trans_eq conversion
  · exact fun j => (cols j).trans_eq conversion

theorem circuit_of_weighted_base {I T : Type*} [Fintype I] [Fintype T]
    (G : Graph n h) (C w bits : ℕ) (hw : 0<w) (hb : 0<bits)
    (menu : ∀ π : Equiv.Perm (Fin (2^n)), Configures K G.arcs C w π)
    (cap : T → ℝ) (N : T → ℕ) (wt : I → ℝ) (owner : (Σ t,Fin (N t)) → I)
    {F B unit : ℝ} (positive : 0<unit) (affordable : unit≤B) (scale : ((2^n:ℕ):ℝ)^2*w≤F)
    (weights : ∀i,0≤wt i ∧ wt i≤B) (full : ∑i,wt i≤2*(F*B))
    (traffic : ∀t,(N t:ℝ)*unit≤cap t) (budget : ∑t,cap t≤2*(F*B))
    (contacts : 4*Fintype.card T≤2^n)
    (actual : ∀i,((Finset.univ.filter fun e => owner e=i).card:ℝ)*unit≤wt i) :
    ∃ (input : I → Fin (2^n)) (fit : (∑t,rowCount (2^n) (F*B) (cap t))≤2^n)
      (sPos : 0<F*B), Nonempty (BaseCircuit K G C w bits hw (input ∘ owner)
        (fun e => outputSlot _ fit (chooseOutput cap N sPos positive traffic e)) (F*(B/unit*bits))) :=
  circuit_of_raw_base G C w bits hw hb menu cap N wt owner (Function.Embedding.refl _)
    positive affordable scale weights full traffic budget contacts actual

/-- Converting the literal physical bit count to the original units gives
the scale bound even when one bundle has amount strictly less than one. -/
theorem BaseCircuit.weighted_bitCost {G : Graph n h} {C w bits : ℕ} {hw : 0<w}
    {src dst : E → Fin (2^n)} {F B unit : ℝ} (P : BaseCircuit K G C w bits hw src dst (F*(B/unit*bits)))
    (positive : 0<unit) (hb : 0<bits) :
    (((P.layers * (∑ v : Fin (2^n),Attachment.bitCost
      (fun i => SlotWidth G.arcs C w v ((Fintype.equivFin (Slot G.arcs v)).symm i)) bits):ℕ):ℝ)*
      (unit/bits)) ≤21*((2*h+4)*(2*h*C+2):ℕ)*(F*B) := by
  have hp : (0:ℝ)<bits := by exact_mod_cast hb
  apply (mul_le_mul_of_nonneg_right P.bitCost (div_nonneg positive.le hp.le)).trans_eq
  field_simp


end
end Hierarchy.DescentRotor

end OAI
