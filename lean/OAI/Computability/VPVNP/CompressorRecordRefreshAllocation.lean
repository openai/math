import OAI.Computability.VPVNP.CompressorRecordRefreshFinish

/-!
# Packed allocation of one degree-refresh level

Seven equal-capacity segment columns are followed by dense demands, strided terms,
selected expander supplies, the two fixed expander columns, and the next state's six
incidence columns. The one-past-the-end word count bounds the complete allocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Allocation

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh
open SpectralGeometry NewSlots

/-- Dimensions and start address determining the packed segment, motif, expander, and refreshed
incidence arrays for one level. -/
structure Plan where
  /-- First address of the seven refresh segment columns. -/
  start : ℕ
  /-- Number of promoted sites, counting the base vertex, promoted port, and residual lane. -/
  sites : ℕ
  /-- Number of motif blocks, one for each old base vertex and residual lane. -/
  blocks : ℕ
  /-- Number of old ports promoted into the new base. -/
  ports : ℕ
  /-- Number of expander slots at each promoted port. -/
  expander : ℕ
  /-- Restored number of slots at each output site. -/
  degree : ℕ
  /-- Number of ordered demand entries in one block's dense demand vector. -/
  ties : ℕ
  /-- Number of words reserved for each block's selected term record. -/
  stride : ℕ

/-- Compute the refresh allocation dimensions from the old state, restored degree exponent,
expander degree, and record sizes. -/
def plan {a g : ℕ} (X : State a (a+g)) (a₀ dH tieCount termStride start : ℕ) : Plan :=
  ⟨start,Fintype.card X.Base * 2^a * 2^g,Fintype.card X.Base * 2^g,2^a,dH,2^a₀,tieCount,termStride⟩

namespace Plan

variable (P : Plan)

/-- Number of segment entries in each scratch column, one per promoted site and old port. -/
def segments := P.sites*P.ports
/-- Capacity of each output incidence column, one slot for each site and restored local slot
number. -/
def capacity := P.sites*P.degree
/-- First demand-vector address, immediately after the seven segment columns. -/
def demand := P.start+7*P.segments
/-- First term-record address, following all blocks' dense demand vectors. -/
def term := P.demand+P.blocks*P.ties
/-- First selected-supply address, following the fixed-stride term records. -/
def supply := P.term+P.blocks*P.stride
/-- First expander target-port address, following the selected per-site supplies. -/
def targetPort := P.supply+P.sites*P.expander
/-- First expander reverse-slot address, following the target-port table. -/
def reverseSlot := P.targetPort+P.ports*P.expander
/-- First address of the refreshed incidence columns, following both expander tables. -/
def next := P.reverseSlot+P.ports*P.expander
/-- Exclusive end address of the allocation after the six output incidence columns. -/
def stop := P.next+6*P.capacity

/-- Public scratch operand zero gives the port count, and operands one through seven give the
segment-column addresses. -/
def scratch (bits : ℕ) (c : Fin 8) : W bits :=
  if c = 0 then word P.ports else word (P.start+(c.val-1)*P.segments)

/-- The bundle-target, total-width, expander-target, reverse-slot, and supply pointers passed
to the actual-slot scans. -/
def inputs (bits : ℕ) : AllSlots.Tables bits :=
  ⟨P.scratch bits 2,P.scratch bits 4,word P.targetPort,word P.reverseSlot,word P.supply⟩

/-- The six output incidence pointers at consecutive column-capacity intervals starting at
`next`. -/
def output (bits : ℕ) : IncidenceDirectory bits :=
  let col := fun k => word (P.next + k*P.capacity)
  ⟨col 0,col 1,col 2,col 3,col 4,col 5⟩

theorem output_column (bits : ℕ) (c : Fin 6) :
    (P.output bits).column c = word (P.next+c.val*P.capacity) := by fin_cases c <;> rfl

/-- The scratch bases satisfy the external pass's common-capacity region convention. -/
theorem scratch_regions {bits : ℕ} (room : P.stop ≤ 2^bits) (pos : 0 < P.capacity) :
    RefreshRAM.Regions (P.scratch bits) P.segments := by
  have upto : P.demand < 2^bits := by
    dsimp only [stop,next,reverseSlot,targetPort,supply,term] at room; omega
  apply RefreshRAM.Regions.packed (P.scratch bits) (base := P.start) (n := P.segments) upto.le
  intro c hc
  have hk : (c.val-1)*P.segments ≤ 7*P.segments := Nat.mul_le_mul_right _ (by have := c.isLt; omega)
  rw [scratch,ite_eq_right hc]
  exact Nat.mod_eq_of_lt (by dsimp only [demand] at upto; omega)

private theorem address_val {bits head len : ℕ} (fit : head+len ≤ 2^bits)
    (j : W bits) (hj : j.val < len) : (word head+j).val = head+j.val := by
  rw [Fin.val_add,show (word (bits := bits) head).val = head from Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

private theorem scratch_addr {bits : ℕ} (room : P.demand ≤ 2^bits) (c : Fin 8) (hc : c ≠ 0)
    (j : W bits) (hj : j.val < P.segments) : (P.scratch bits c+j).val < P.demand := by
  have h := Nat.mul_le_mul_right P.segments (show (c.val-1)+1 ≤ 7 by have := c.isLt; omega)
  rw [Nat.add_mul,Nat.one_mul] at h
  change P.start+7*P.segments ≤ 2^bits at room
  rw [scratch,ite_eq_right hc,address_val (len := P.segments) (by omega) _ hj]
  change _ < P.start+7*P.segments
  omega

private theorem column_addr {bits : ℕ} (room : P.stop ≤ 2^bits) (c : Fin 6)
    (j : W bits) (hj : j.val < P.capacity) : P.next ≤ ((P.output bits).column c+j).val := by
  have h := Nat.mul_le_mul_right P.capacity c.isLt
  rw [Nat.succ_mul] at h
  rw [output_column,address_val (len := P.capacity) (by dsimp only [stop] at room; omega) _ hj]
  omega

/-- Every actual or base output column lies inside the final six-column allocation. -/
theorem column_interval {bits : ℕ} (room : P.stop ≤ 2^bits) (c : Fin 6) (j : W bits)
    (hj : j.val < P.capacity) :
    P.next ≤ ((P.output bits).column c+j).val ∧ ((P.output bits).column c+j).val < P.stop := by
  have h := Nat.mul_le_mul_right P.capacity c.isLt
  rw [Nat.succ_mul] at h
  rw [output_column,address_val (len := P.capacity) (by dsimp only [stop] at room; omega) _ hj]
  dsimp only [stop]; constructor <;> omega

end Plan

private theorem packed_lt {w N d : ℕ} (x y h : W w) (hx : x.val < N) (hy : y.val < d) (hh : h.val = d) :
    (x*h+y).val < N*d := by
  have bound := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hx)
  rw [Nat.succ_mul] at bound
  rw [Fin.val_add,Fin.val_mul,hh]
  exact (Nat.mod_le ..).trans_lt (by have := Nat.mod_le (x.val*d) (2^w); omega)

private theorem read_before_next {bits D R dH d₀ N : ℕ} (P : Plan) (T : IncidenceDirectory bits)
    (room : P.stop ≤ 2^bits) (ports : D = P.ports) (degree : dH = P.expander)
    (sites : N = P.sites) (hports : D < 2^bits) (hh : dH < 2^bits) (hD : 0 < D)
    (sbound : N ≤ P.segments) (i : Fin N) (k : RefreshSlot dH d₀)
    (x : W bits) (used : x ∈ NewSlots.inputs (kindOf k) (AllSlots.words D R (P.inputs bits) T k) (word i.val)) :
    x.val < P.next := by
  let b : W bits := word i.val
  have hb : b.val < N := (Nat.mod_le ..).trans_lt i.isLt
  have hnext : P.next ≤ 2^bits := by dsimp only [Plan.stop] at room; omega
  have ord₁ : P.demand ≤ P.supply := by dsimp only [Plan.supply,Plan.term]; omega
  have ord₂ : P.supply+N*dH = P.targetPort := by rw [sites,degree]; rfl
  have ord₃ : P.targetPort+D*dH = P.reverseSlot := by rw [ports,degree]; rfl
  have ord₄ : P.reverseSlot+D*dH = P.next := by rw [ports,degree]; rfl
  cases k with
  | inl k =>
    change x ∈ [P.scratch bits 2+b,P.scratch bits 4+b] at used
    rcases List.mem_cons.mp used with rfl | h
    · have h := P.scratch_addr (by omega) 2 (by decide) b (hb.trans_le sbound); omega
    · obtain rfl := List.mem_singleton.mp h
      have h := P.scratch_addr (by omega) 4 (by decide) b (hb.trans_le sbound); omega
  | inr k =>
    cases k with
    | inr k => exact (List.not_mem_nil used).elim
    | inl k =>
      let p := AllSlots.words D R (P.inputs bits) T (.inr (.inl k) : RefreshSlot dH d₀)
      let v := BinaryOp.mod.eval (BinaryOp.div.eval b (p 3)) (p 0)
      have hv : v.val < D := by
        have he : (p 0).val = D := Nat.mod_eq_of_lt hports
        change (_ % (p 0).val) % (2^bits) < D
        rw [he]; exact (Nat.mod_le ..).trans_lt (Nat.mod_lt _ hD)
      have h₁ : (p 1).val = dH := Nat.mod_eq_of_lt hh
      have h₄ : (p 4).val < dH := (Nat.mod_le ..).trans_lt k.isLt
      let e := v*p 1+p 4
      let y := b*p 1+p 4
      have he : e.val < D*dH := packed_lt v _ _ hv h₄ h₁
      have hy : y.val < N*dH := packed_lt b _ _ hb h₄ h₁
      change x ∈ [word P.targetPort+e,word P.reverseSlot+e,word P.supply+y] at used
      rcases List.mem_cons.mp used with rfl | h
      · rw [Plan.address_val (len := D*dH) (by omega) _ he]; omega
      rcases List.mem_cons.mp h with rfl | h
      · rw [Plan.address_val (len := D*dH) (by omega) _ he]; omega
      obtain rfl := List.mem_singleton.mp h
      rw [Plan.address_val (len := N*dH) (by omega) _ hy]; omega

section Dyadic

variable {bits a a₀ g dH : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH)
  (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K')
  (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀) (choice : DyadicRefreshChoice X E hdH conn F)
  (tieCount termStride start : ℕ)

local notation "P" => plan X a₀ dH tieCount termStride start
local notation "N" => Fintype.card X.Base * 2^a * 2^g
local notation "Y" => dyadicRefreshNext X E hdH conn F hD hd choice

private theorem sites_pos : 0 < N := by positivity

private theorem newBaseCount : Fintype.card (Y).Base = Fintype.card X.Base * 2^a := by
  change Fintype.card (X.Base × Fin (2^a)) = _; simp

/-- The packed address recipe meets every word-size and aliasing requirement for
post-term completion. No contents of the incoming memory enter the layout proof. -/
theorem finish_layout (rowSize : 2+2^a*dH ≤ termStride) (room : (P).stop ≤ 2^bits) :
    Finish.Layout X E hdH conn F hD hd choice ((P).scratch bits) (word (P).term) termStride ((P).inputs bits) ((P).output bits) := by
  have capPos : 0 < (P).capacity := Nat.mul_pos (sites_pos X) (Nat.two_pow_pos a₀)
  have nextLt : (P).next < 2^bits := by change (P).next+6*(P).capacity ≤ 2^bits at room; omega
  have h₁ : (P).demand ≤ (P).term := Nat.le_add_right ..
  have h₂ : (P).term + (Fintype.card X.Base * 2^g)*termStride = (P).supply := rfl
  have h₃ : (P).supply+N*dH = (P).targetPort := rfl
  have h₄ : (P).targetPort+2^a*dH = (P).reverseSlot := rfl
  have h₅ : (P).reverseSlot+2^a*dH = (P).next := rfl
  have h₆ : (P).start+7*(P).segments = (P).demand := rfl
  have capLt : (P).capacity < 2^bits := by change (P).next+6*(P).capacity ≤ 2^bits at room; omega
  have ncap : N ≤ (P).capacity := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a₀)
  have nseg : N ≤ (P).segments := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)
  have dg : 2^a₀ < 2^bits := (Nat.le_mul_of_pos_left _ (sites_pos X)).trans_lt capLt
  have dp : 2^a < 2^bits := by
    have hs : 2^a ≤ (P).segments := Nat.le_mul_of_pos_left _ (sites_pos X); omega
  have dr : 2^g < 2^bits := (Nat.le_mul_of_pos_left _ (Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos a))).trans_lt
    (ncap.trans_lt capLt)
  have eh : dH < 2^bits := by omega
  have supDims : SupplyScan.Fits (dH := dH) X bits :=
    ⟨dp,dr,eh,(Nat.mul_le_mul_left N (by omega : dH ≤ 2^a₀)).trans capLt.le⟩
  have termVal : (word (bits := bits) (P).term).val = (P).term := Nat.mod_eq_of_lt (by omega)
  have supplyVal : (((P).inputs bits).supply).val = (P).supply := Nat.mod_eq_of_lt (by omega)
  have targetVal : (((P).inputs bits).targetPort).val = (P).targetPort := Nat.mod_eq_of_lt (by omega)
  have reverseVal : (((P).inputs bits).reverseSlot).val = (P).reverseSlot := Nat.mod_eq_of_lt (by omega)
  have rb : ExpanderROM.Regions ((P).inputs bits) (2^a*dH) := by
    constructor
    · rw [targetVal]; omega
    · rw [reverseVal]; omega
    · rw [targetVal,reverseVal]; exact Or.inl h₄.le
  have sc (j : W bits) (hj : j.val < N*dH) : (((P).inputs bits).supply+j).val = (P).supply+j.val :=
    Plan.address_val (len := N*dH) (by omega) j hj
  have readonly (addr : ℕ) (ha : addr < (P).targetPort) : Finish.ROMOutside ((P).inputs bits) (2^a*dH) addr :=
    ⟨Or.inl (targetVal ▸ ha),Or.inl (by rw [reverseVal]; omega)⟩
  have anext (c : Column) (j : W bits) (hj : j.val < (P).capacity) :
      (P).next ≤ (AllSlots.columnBase ((P).output bits) c+j).val := by
    cases c with
    | outgoing => exact (P).column_addr room 3 _ hj
    | incoming => exact (P).column_addr room 4 _ hj
    | width => exact (P).column_addr room 5 _ hj
  have yn := newBaseCount X E hdH conn F hD hd choice
  refine ⟨rfl,rfl,⟨dp,dr,dg,capLt.le⟩,?_,rb,?_,?_,?_,?_⟩
  · apply SupplyScan.apart_of_intervals X E hdH conn F (word (P).term) termStride ((P).inputs bits).supply supDims rowSize
    · rw [termVal]; omega
    · rw [supplyVal]; omega
    · rw [termVal,supplyVal]; exact Or.inl h₂.le
  · intro j hj
    exact readonly _ (by rw [sc _ hj]; omega)
  · apply IncidenceDirectory.Layout.packed Y (P).next
    · rw [yn]; exact room
    · intro c
      rw [yn,(P).output_column]
      have h := Nat.mul_le_mul_right (P).capacity c.isLt
      rw [Nat.succ_mul] at h
      exact Nat.mod_eq_of_lt (show (P).next+c.val*(P).capacity < 2^bits by
        change (P).next+6*(P).capacity ≤ 2^bits at room; omega)
  · intro k i z used c j hj hz
    have hread := read_before_next (R := 2^g) P ((P).output bits) room rfl rfl rfl dp eh (Nat.two_pow_pos a)
      nseg i ((refreshSlots hd).symm k) z used
    exact (Nat.not_le_of_lt hread) ((congrArg Fin.val hz).symm ▸ anext c j hj)
  · intro c hc j hj
    let addr := ((P).scratch bits c+j).val
    have ha : addr < (P).demand := (P).scratch_addr (by omega) c hc j hj
    refine ⟨?_,readonly addr (by omega),?_,?_⟩
    · intro i hi
      have he := sc i hi
      change addr ≠ (((P).inputs bits).supply+i).val; omega
    · intro col i hi
      have hh := anext col i hi
      change addr ≠ (AllSlots.columnBase ((P).output bits) col+i).val; omega
    · intro i hi
      have hbase : BaseOutput.baseCount Y ≤ (P).capacity := by
        rw [BaseOutput.baseCount,yn]
        exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g))
      have hi' := hi.trans_le hbase
      have h0 := (P).column_addr room 0 i hi'
      have h1 := (P).column_addr room 1 i hi'
      have h2 := (P).column_addr room 2 i hi'
      change addr ≠ (((P).output bits).column 0+i).val ∧ addr ≠ (((P).output bits).column 1+i).val ∧
        addr ≠ (((P).output bits).column 2+i).val
      exact ⟨by omega,by omega,by omega⟩

/-- The finish phase protects all earlier arrays, including the selected term headers,
and every address beyond the six next-state incidence columns. -/
theorem outside_finish (room : (P).stop ≤ 2^bits) (addr : ℕ)
    (outside : addr < (P).supply ∨ (P).stop ≤ addr) :
    Finish.Outside X E hdH conn F hD hd choice (word (P).term) termStride ((P).inputs bits) ((P).output bits) addr := by
  have capPos : 0 < (P).capacity := Nat.mul_pos (sites_pos X) (Nat.two_pow_pos a₀)
  have s₁ : (P).supply+N*dH = (P).targetPort := rfl
  have s₂ : (P).targetPort+2^a*dH = (P).reverseSlot := rfl
  have s₃ : (P).reverseSlot+2^a*dH = (P).next := rfl
  have s₄ : (P).next+6*(P).capacity = (P).stop := rfl
  have hport : (((P).inputs bits).targetPort).val = (P).targetPort :=
    Nat.mod_eq_of_lt (show (P).targetPort < 2^bits by omega)
  have hslot : (((P).inputs bits).reverseSlot).val = (P).reverseSlot :=
    Nat.mod_eq_of_lt (show (P).reverseSlot < 2^bits by omega)
  have miss (c : Fin 6) (i : W bits) (hi : i.val < (P).capacity) :
      addr ≠ (((P).output bits).column c+i).val := by
    obtain ⟨hl,hu⟩ := (P).column_interval room c i hi
    omega
  constructor
  · intro i hi
    change addr ≠ (word (P).supply+i).val
    rw [Plan.address_val (len := N*dH) (by omega) _ hi]; omega
  · change (addr < (((P).inputs bits).targetPort).val ∨ _ ≤ addr) ∧
      (addr < (((P).inputs bits).reverseSlot).val ∨ _ ≤ addr)
    rw [hport,hslot]; constructor <;> omega
  · intro c i hi
    cases c with
    | outgoing => exact miss 3 i hi
    | incoming => exact miss 4 i hi
    | width => exact miss 5 i hi
  · intro i hi
    have hbase : BaseOutput.baseCount Y ≤ (P).capacity := by
      rw [BaseOutput.baseCount,newBaseCount X E hdH conn F hD hd choice]
      exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos g))
    exact ⟨miss 0 _ (hi.trans_le hbase),miss 1 _ (hi.trans_le hbase),miss 2 _ (hi.trans_le hbase)⟩

theorem outside_finish_of_lt_supply (room : (P).stop ≤ 2^bits) (addr : ℕ) (ha : addr < (P).supply) :
    Finish.Outside X E hdH conn F hD hd choice (word (P).term) termStride ((P).inputs bits) ((P).output bits) addr :=
  outside_finish X E hdH conn F hD hd choice tieCount termStride start room addr (.inl ha)

theorem outside_finish_of_outside (room : (P).stop ≤ 2^bits) (addr : ℕ)
    (ha : addr < start ∨ (P).stop ≤ addr) :
    Finish.Outside X E hdH conn F hD hd choice (word (P).term) termStride ((P).inputs bits) ((P).output bits) addr := by
  apply outside_finish X E hdH conn F hD hd choice tieCount termStride start room addr
  have hs : start ≤ (P).supply := by
    dsimp only [Plan.supply, Plan.term, Plan.demand]; change start ≤ start+_+_+_; omega
  exact ha.imp (fun h => h.trans_le hs) id

end Dyadic
end CompressorRecords.PortRefresh.Allocation

end VPVNP
end Computability
end OAI
