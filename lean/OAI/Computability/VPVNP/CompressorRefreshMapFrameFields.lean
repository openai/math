import OAI.Computability.VPVNP.CompressorRefreshOperandInputs
import Mathlib.Data.LawfulXor.Basic

/-!
# Native operand bases and lengths of the refresh motif

The same field descriptor table serves all promoted ports. Old demand endpoints read
their designated old slot, while new endpoints read the appropriate slice of the packed
external word. Supply endpoints read their designated expander slot. Lengths select the
payload part of the incident fields using the port computed from the current site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.MapFrameFields

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe NewSlots OperandInputs PairSimulation PairSimulation.NodeArguments MapLookup RefreshMapOperands
open MotifSelector MotifConversion SpectralGeometry
open scoped Fin.CommRing

variable {D d₀ dH t bits : ℕ}

/-- A source or target endpoint field of a demand tie or a directed expander supply incidence. -/
abbrev FieldId (D dH : ℕ) := LabelField (Tie D) (Fin D × Fin dH)

/-- Local base pointer of a map-row field. The table uses the fixed reverse incidence
of a supply and the stored segment offset at either end of an external demand. -/
def base (P : SlotGraph (Fin D) dH) (hd : dH+1 ≤ d₀) (I : Input) : FieldId D dH → Expr
  | .inl (false,e) => ArgumentAddress.fieldStatic I.child (!e.1) (tieTarget e)
  | .inl (true,e) =>
    let loc := ArgumentAddress.fieldStatic I.parent (!e.1) (refreshSlots hd (.inl 0))
    let index := ArgumentSite.segment D I.parent.siteOrd (.lit (tieSource e).val)
    loc.add (.load ((if !e.1 then I.offIn else I.offOut).add index))
  | .inr (false,e) => ArgumentAddress.fieldStatic I.parent false (refreshSlots hd (.inr (.inl e.2)))
  | .inr (true,e) => ArgumentAddress.fieldStatic I.parent true (refreshSlots hd (.inr (.inl (P.target e).2)))

/-- A present endpoint gives one and an absent endpoint gives zero. -/
def present (port : Expr) (endpoint : Fin D) : Expr :=
  (.lit 1 : Expr).div ((Expr.binary .bitXor port (.lit endpoint.val)).add (.lit 1))

/-- The port at which the indexed demand or supply endpoint is incident. -/
def endpoint (P : SlotGraph (Fin D) dH) : FieldId D dH → Fin D
  | .inl (false,e) => tieSource e
  | .inl (true,e) => tieTarget e
  | .inr (false,e) => e.1
  | .inr (true,e) => (P.target e).1

/-- Recover the stored demand width or chosen supply payload for a fixed motif role.
The grid and repetition headers precede the payload vector. -/
def storedWidth (ties : Fin t ≃ Tie D) (stride : ℕ) (I : Input) : FieldId D dH → Expr
  | .inl (_,e) =>
    let b := ArgumentSite.blockIndex D I.parent.siteOrd I.lanes
    .load ((I.demandBase.add (b.mul (.lit t))).add (.lit (ties.symm e).val))
  | .inr (_,e) =>
    let b := ArgumentSite.blockIndex D I.parent.siteOrd I.lanes
    .load ((I.termBase.add (b.mul (.lit stride))).add (.lit (2+e.1.val*dH+e.2.val)))

/-- Only the endpoint incident to the runtime port contributes a readable slice. -/
def length (P : SlotGraph (Fin D) dH) (ties : Fin t ≃ Tie D) (stride : ℕ) (I : Input) (f : FieldId D dH) : Expr :=
  (present (ArgumentSite.portIndex D I.parent.siteOrd I.lanes) (endpoint P f)).mul (storedWidth ties stride I f)

private theorem word_add (x y : ℕ) : word x + word y = word (bits := bits) (x+y) :=
  Fin.ext (Nat.add_mod x y _).symm

private theorem word_mul (x y : ℕ) : word x * word y = word (bits := bits) (x*y) :=
  Fin.ext (Nat.mul_mod x y _).symm

private theorem of_val (x : W bits) {n : ℕ} (h : x.val = n) : x = word n :=
  Fin.ext (h.trans (Nat.mod_eq_of_lt (h ▸ x.isLt)).symm)

theorem present_eval {a : ℕ} (pub : Fin 5 → W bits) (state : W bits) (m : Memory bits)
    (port : Expr) (j k : Fin (2^a)) (dFit : 2^a < 2^bits) (rep : port.eval pub state m = word j.val) :
    (present port k).eval pub state m = if j=k then (1 : W bits) else 0 := by
  have hj : (port.eval pub state m).val = j.val := (congrArg Fin.val rep).trans (Nat.mod_eq_of_lt (j.isLt.trans dFit))
  have hk : ((k.val : W bits)).val = k.val := Nat.mod_eq_of_lt (k.isLt.trans dFit)
  let x := j.val ^^^ k.val
  have hl : x < 2^a := Nat.xor_lt_two_pow j.isLt k.isLt
  have hw : 1 < 2^bits := (Nat.one_le_two_pow).trans_lt dFit
  have hone : (1 : W bits).val = 1 := Nat.mod_eq_of_lt hw
  have hxor : (BinaryOp.bitXor.eval (port.eval pub state m) (k.val : W bits)).val = x := by
    change ((port.eval pub state m).val ^^^ (k.val : W bits).val) % _ = _
    rw [hj,hk]; exact Nat.mod_eq_of_lt (hl.trans dFit)
  change Fin.ofNat _ ((1 : W bits).val / (BinaryOp.bitXor.eval (port.eval pub state m) (k.val : W bits)+1).val) = _
  rw [Fin.val_add,hxor,hone,Nat.mod_eq_of_lt (by omega)]
  by_cases he : j=k
  · subst k; simp [x]
  · have hn : x ≠ 0 := fun h => he (Fin.ext (xor_eq_zero_iff.mp h))
    rw [ite_eq_right he,Nat.div_eq_of_lt (by omega)]
    rfl

section Base

variable {a g a₀ : ℕ} (X : State a (a+g)) (p : (X.Base × BitWord g) × Fin (2^a))
  (P : SlotGraph (Fin (2^a)) dH) (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀)
  (internal : X.Base × BitWord g → Fin (2^a) × Fin dH → ℕ) (A : Arena) (child parent : ℕ)
  (old next : IncidenceDirectory bits) (q : Fin 8 → W bits) (demand term : W bits)
  (pub : Fin 5 → W bits) (state : W bits) (m : Memory bits) (I : Input)

local notation "Y" => newState X P hD hd internal
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "N" => Fintype.card X.Base*2^a*2^g*2^a

/-- Every operand expression evaluates to the independent slot or packed-segment base
used by the resident map call, including its unselected fields. -/
theorem base_eval {fit : N ≤ 2^bits}
    (args : Describes I pub state m X p P hD hd internal A child parent old next q demand term)
    (oldCols : old.ActualColumns X m) (newCols : next.ActualColumns Y m)
    (segments : SegmentFields X q fit m) (dFit : 2^a < 2^bits) (f : FieldId (2^a) dH) :
    (base P hd I f).eval pub state m = word (operandBase X p P hD hd internal A child parent f) := by
  rcases f with ⟨dir,e⟩ | ⟨dir,e⟩
  · cases dir with
    | false => exact ArgumentAddress.eval_fieldStatic args.childRep oldCols _ _
    | true =>
      let idx := ArgumentSite.segment (2^a) I.parent.siteOrd (.lit (tieSource e).val)
      have he : idx.eval pub state m = idWord O fit (p,tieSource e) :=
        ArgumentSite.segment_eval X p pub state m _ args.site (.lit (tieSource e).val) (tieSource e)
          (Nat.mod_eq_of_lt ((tieSource e).isLt.trans dFit)) fit
      have hread : m (((if !e.1 then I.offIn else I.offOut).eval pub state m) + idx.eval pub state m).val =
          word (externalOffset X p (!e.1) (tieSource e)) := by
        obtain ⟨ho,hi⟩ := Readback.interval_spec X q m segments (p,tieSource e)
        cases h : e.1
        · rw [he]
          simp only [Bool.not_false,ite_true,args.offIn]
          exact of_val _ (congrArg Prod.snd hi)
        · rw [he]
          change m (I.offOut.eval pub state m + idWord O fit (p,tieSource e)).val = _
          rw [args.offOut]
          exact of_val _ (congrArg Prod.snd ho)
      change (ArgumentAddress.fieldStatic I.parent (!e.1) (refreshSlots hd (.inl 0))).eval pub state m +
        m (((if !e.1 then I.offIn else I.offOut).eval pub state m)+idx.eval pub state m).val = _
      rw [ArgumentAddress.eval_fieldStatic args.parentRep newCols,hread]
      exact word_add _ _
  · cases dir <;> exact ArgumentAddress.eval_fieldStatic args.parentRep newCols _ _

end Base

section Selected

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {g : ℕ}
  (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (oldDir newDir : IncidenceDirectory bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (start stride : ℕ)
  (pub : Fin 5 → W bits) (state : W bits) (m : Memory bits) (I : Input)

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh hD hd choice
local notation "Pₗ" => Allocation.plan X (S.degreeExponent 0) H t stride start
local notation "Q" => Allocation.Plan.scratch Pₗ bits
local notation "src" => word (bits := bits) (Allocation.Plan.demand Pₗ)
local notation "term" => word (bits := bits) (Allocation.Plan.term Pₗ)
local notation "N" => Fintype.card X.Base*D*2^g*D
local notation "dem" => blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X)

/-- The demand width or supply payload width of a field before restriction to the runtime port. -/
def nominal (d : Tie D → ℕ) (v : Fin D × Fin H → ℕ) : FieldId D H → ℕ
  | .inl (_,e) => d e
  | .inr (_,e) => v e

/-- The live reads of the dense demand and strided term columns recover the selected
integer lengths in the fixed coordinate ordering. -/
theorem storedWidth_eval {fit : N ≤ 2^bits}
    (args : Describes I pub state m X p P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (dFit : D < 2^bits) (f : FieldId D H) :
    (storedWidth ties stride I f).eval pub state m = word (nominal (dem p.1) (choice p.1).val f) := by
  let b := ArgumentSite.blockIndex D I.parent.siteOrd I.lanes
  have hb : b.eval pub state m = word (DemandScan.blocks X p.1).val :=
    ArgumentSite.blockIndex_eval X p pub state m _ _ args.site args.lanes dFit
  rcases f with ⟨dir,e⟩ | ⟨dir,e⟩
  · change m (I.demandBase.eval pub state m + b.eval pub state m * word t + word (ties.symm e).val).val = _
    rw [args.demandBase,hb,word_mul]
    exact of_val _ (congrFun (stored.demands p.1) e)
  · let head := SupplyScan.recordBase X term stride p.1
    let slot := finProdFinEquiv e
    have hs : slot.val = e.1.val*H+e.2.val := by change e.2.val+H*e.1.val = _; ring
    have hb' : term + word (DemandScan.blocks X p.1).val * word stride = head := by rw [DemandScan.blocks_val]; rfl
    have room := stored.terms.fits p.1
    change head.val + 2 + D*H < 2^bits at room
    have hi := slot.isLt
    have index : (head + word (2+e.1.val*H+e.2.val)).val = head.val+2+slot.val := by
      rw [Fin.val_add,Fin.val_ofNat]
      have eqn : 2+e.1.val*H+e.2.val = 2+slot.val := by omega
      rw [eqn,Nat.mod_eq_of_lt (show 2+slot.val < 2^bits by omega),
        Nat.mod_eq_of_lt (show head.val+(2+slot.val) < 2^bits by omega),Nat.add_assoc]
    change m (I.termBase.eval pub state m + b.eval pub state m * word stride + word (2+e.1.val*H+e.2.val)).val = _
    rw [args.termBase,hb,hb',index]
    exact of_val _ (congrFun (Readback.payload_eq X m S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride stored p.1) e)

variable (old : X.network.Half (oldSite X p)) (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites p))
  (grid : B.refresh.grid.demands) (θ : Fin (repetitions B.refresh (entryInput B X choice p old new).demand) → Selector B.refresh)

/-- A field at the wrong local port has length zero. At its correct port the stored
demand or payload gives the length of the exact resident buffer of the refresh call. -/
theorem length_eval {fit : N ≤ 2^bits}
    (args : Describes I pub state m X p P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (dFit : D < 2^bits) (f : FieldId D H) :
    (length P ties stride I f).eval pub state m =
      word ((buffers B X choice p old new A child parent grid θ 0).len f) := by
  let port := ArgumentSite.portIndex D I.parent.siteOrd I.lanes
  have hp : port.eval pub state m = word p.2.val :=
    ArgumentSite.portIndex_eval X p pub state m _ _ args.site args.lanes dFit
  change (present port (endpoint P f)).eval pub state m * (storedWidth ties stride I f).eval pub state m = _
  rw [present_eval pub state m port p.2 _ dFit hp,
    storedWidth_eval B X choice p A child parent oldDir newDir ties start stride pub state m I args stored dFit]
  rcases f with ⟨dir,e⟩ | ⟨dir,e⟩
  · cases dir with
    | false => by_cases he : p.2 = tieSource e <;>
        simp [endpoint,nominal,buffers,MapRowLoop.buffers,MapRow.endpoint,entryInput,he]
    | true => by_cases he : p.2 = tieTarget e <;>
        simp [endpoint,nominal,buffers,MapRowLoop.buffers,MapRow.endpoint,entryInput,he]
  · cases dir with
    | false => by_cases he : p.2 = e.1 <;>
        simp [endpoint,nominal,buffers,MapRowLoop.buffers,MapRow.endpoint,entryInput,BlockSchedule.portSupply,expanderSupply,he]
    | true => by_cases he : p.2 = (S.graph.reverse e).1 <;>
        simp [endpoint,nominal,buffers,MapRowLoop.buffers,MapRow.endpoint,entryInput,BlockSchedule.portSupply,expanderSupply,
          SpectralGeometry.RegularArcGraph.toSlotGraph,he]

end Selected
end CompressorRecords.PortRefresh.MapFrameFields

end VPVNP
end Computability
end OAI
