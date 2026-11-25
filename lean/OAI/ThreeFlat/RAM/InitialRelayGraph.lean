import OAI.ThreeFlat.Diagonal.InitialSlotImage
import OAI.ThreeFlat.RAM.HeaderScanProcedure
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Native initialization of all six columns of the cyclic XOR relay graph -/
namespace ThreeFlat.RAM.InitialRelayGraph
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr PhysicalProcedure DescriptorExpr
open Diagonal.InitialSlotImage
open scoped Fin.CommRing
variable {W : ℕ}
abbrev F := Formula 1

/-- The boot header holds (graph base, 6*edge rows, width base, width count,
cursor positions, base degree, lane count). The dimensions and base are
public literals, so the row generator never consults the array it is writing. -/
def formula (base axes degree : ℕ) : F :=
  let i := Formula.cut (.reg 0) (.lit base)
  let rows := Formula.lit (n:=1) (axes*degree)
  let col := Formula.op .div i rows
  let within := Formula.op .mod i rows
  let v := Formula.op .div within (.lit degree)
  let p := Formula.op .mod within (.lit degree)
  let pv := Formula.select .eq v (.lit 0) (.lit (axes-1)) (.cut v (.lit 1))
  let nx := Formula.select .lt (.op .add v (.lit 1)) (.lit axes) (.op .add v (.lit 1)) (.lit 0)
  let dst := Formula.select .lt col (.lit 3) nx pv
  let axis := Formula.select .lt col (.lit 3) v pv
  let delta := Formula.op .mul (.op .mod p (.lit 2)) (.op .shiftLeft (.lit 1) axis)
  let field := Formula.op .mod col (.lit 3)
  .select .eq field (.lit 0) dst (.select .eq field (.lit 1) p delta)

def term (base axes degree : ℕ) : Term W 0 1 := HeaderScan.closed (formula base axes degree)

def procedure (current : Word W) (base axes degree : ℕ) : Procedure W :=
  HeaderScan.procedure current 0 1 (term base axes degree)

def loaded (current : Word W) (base axes degree : ℕ) (m : Memory W) : Prop :=
  m (m current.val+0).val = (base : Word W) ∧ m (m current.val+1).val = (6*(axes*degree) : ℕ)

def image (base axes degree : ℕ) (m : Memory W) : Memory W :=
  fillSegment base (6*(axes*degree)) (fun a => (row axes degree (a-base) : Word W)) m

private theorem testEq (x y : ℕ) : (natTest .eq x y = true) ↔ x = y := by
  by_cases h : x=y <;> simp [natTest,h]

private theorem testLt (x y : ℕ) : (natTest .lt x y = true) ↔ x < y := by
  by_cases h : x<y <;> simp [natTest,h]

theorem value (base axes degree a : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ)
    (h : a-base<6*(axes*degree)) (hd : 0<degree) (axes_fit : axes≤W) :
    (formula base axes degree).natural W data mem (fun _ => a) = row axes degree (a-base) := by
  let i := a-base
  let v := i%(axes*degree)/degree
  have pos : 0<axes*degree := by omega
  have hv : v<axes := (Nat.div_lt_iff_lt_mul hd).2 (Nat.mod_lt i pos)
  have positiveAxes : 0 < axes := (Nat.zero_le v).trans_lt hv
  have hp : prev axes v < W := by
    unfold prev
    split <;> omega
  have ha : (if i/(axes*degree)<3 then v else prev axes v)<W := by split <;> omega
  simp only [formula,Formula.natural,natOp,testEq,testLt]
  change (if _ then _ else if _ then _ else _*(if (if i/(axes*degree)<3 then v else prev axes v)<W
      then 1 <<< (if i/(axes*degree)<3 then v else prev axes v) else 0)) = _
  rw [ite_eq_left ha,Nat.shiftLeft_eq,Nat.one_mul]
  rfl

theorem fits (base axes degree a : ℕ) (data : Param → ℕ) (mem : ℕ → ℕ)
    (start : base ≤ a) (stop : a<base+6*(axes*degree)) (bound : base+6*(axes*degree)<2^W)
    (hd : 0<degree) (wide : 6<2^W) :
    (formula base axes degree).Fits W data mem (fun _ => a) := by
  let i := a-base
  let n := axes*degree
  have ine : i < 6*n := by dsimp [i,n]; omega
  have hn : 0<n := by omega
  have ax : 0<axes := by by_contra! e; simp [n,show axes=0 by omega] at hn
  have dv : degree≤n := by dsimp [n]; simpa using Nat.mul_le_mul_right degree ax
  have av : axes≤n := Nat.le_mul_of_pos_right _ hd
  have bn : n<2^W := by change axes*degree<2^W; omega
  have acol : i/n<6 := (Nat.div_lt_iff_lt_mul hn).2 ine
  have inside := Nat.mod_lt i hn
  have hv : i%n/degree<axes := (Nat.div_lt_iff_lt_mul hd).2 inside
  have hport := Nat.mod_lt (i%n) hd
  have hfield := Nat.mod_lt (i/n) (show 0<3 by decide)
  have hrem := Nat.mod_lt (i%n%degree) (show 0<2 by decide)
  let v := i%n/degree
  have v_nonnegative : 0 ≤ v := Nat.zero_le _
  have next_fit : v+1 < 2^W := by change i%n/degree+1<2^W; omega
  have old_fit : (if v=0 then axes-1 else v-1) < 2^W := by
    dsimp only [v]
    split <;> omega
  have axis_fit : (if i/n<3 then v else if v=0 then axes-1 else v-1) < 2^W := by
    split
    · exact hv.trans_le (av.trans bn.le)
    · exact old_fit
  have addr : a<2^W := stop.trans bound
  have startFit : base<2^W := start.trans_lt addr
  change (formula base axes degree).Fits W data mem (fun _ => a)
  simp only [formula,Formula.Fits,Formula.natural,opFits,natOp,testEq,testLt,true_and,and_true]
  dsimp only [i,n] at ine acol inside hv hport hfield hrem av dv bn
  dsimp only [v,i,n] at next_fit old_fit axis_fit v_nonnegative
  repeat' first | apply And.intro | split
  all_goals first | assumption | trivial | omega

theorem spec (current : Word W) (base axes degree : ℕ)
    (bound : base+6*(axes*degree)<2^W) (hd : 0<degree) (ha : axes≤W) (wide : 6<2^W) :
    (procedure current base axes degree).Spec (loaded current base axes degree)
      (fun m out => out=image base axes degree m) (13+6*(axes*degree)*(2*(term (W:=W) base axes degree).binds+4)) := by
  apply HeaderScan.spec current 0 1 (term base axes degree) _ (fun _ => base) (fun _ => 6*(axes*degree))
    (fun _ a => (row axes degree (a-base) : Word W))
  · exact fun _ _ => ⟨bound,le_rfl⟩
  · exact fun _ h => h
  · intro m h a m' lo hi outside
    rw [term,HeaderScan.eval_closed]
    let naturalMem := fun i => (m' i).val
    have safe := fits base axes degree a.val (fun _ => 0) naturalMem lo hi bound hd wide
    have ev := (formula base axes degree).value_eq_natural (fun _ => 0) naturalMem (fun _ => a.val) safe
    rw [value _ _ _ _ _ _ (by omega) hd ha] at ev
    simpa [naturalMem] using ev

open Diagonal

theorem image_fields {k r : ℕ} (hk : 2≤k+1) (C : SlotImage.Columns) (m : Memory W)
    (hrows : C.rows=(k+1)*(r*2)) (haf : k+1≤W) (hfit : C.graph+6*C.rows<2^W)
    (p : Fin (k+1) × Fin (r*2)) (back : Bool) (f : Fin 3) :
    (image C.graph (k+1) (r*2) m (SlotImage.cell C (Equiv.refl _) p back f)).val =
      SlotImage.fields (LaneCursor.graph hk r) (Equiv.refl _) (CompressorPacking.Native.tagOrdinal _) p back f := by
  let G := LaneCursor.graph hk r
  let a := SlotImage.cell C (Equiv.refl _) p back f
  let lane := CompressorPacking.Native.tagOrdinal (k+1)
  have index : SlotImage.ordinal (Equiv.refl _) p<C.rows := hrows ▸ SlotImage.ordinal_lt (Equiv.refl _) p
  have col : SlotImage.column back f<6 := by cases back <;> dsimp [SlotImage.column] <;> have := f.isLt <;> omega
  have range : C.graph≤a ∧ a<C.graph+6*C.rows := by
    change _ ≤ C.graph+C.rows*SlotImage.column back f+_ ∧ _ < _
    dsimp only [a,SlotImage.cell]
    have h₁ := Nat.add_lt_add_left index (SlotImage.column back f*C.rows)
    have h₂ := Nat.mul_le_mul_right C.rows col
    rw [Nat.succ_mul] at h₂
    rw [Nat.mul_comm C.rows]
    omega
  have hdeg : r*2 ≤ C.rows := hrows ▸ (by simpa using Nat.mul_le_mul_right (r*2) (show 1≤k+1 by omega))
  have word : (SlotImage.fields G (Equiv.refl _) lane p back f)<2^W := by
    fin_cases f
    · exact (SlotImage.oriented G back p).1.isLt.trans (haf.trans_lt Nat.lt_two_pow_self)
    · exact (SlotImage.oriented G back p).2.isLt.trans_le (by omega)
    · exact (lane (SlotImage.shift G back p)).isLt.trans_le (Nat.pow_le_pow_right (by decide) haf)
  change (fillSegment C.graph (6*((k+1)*(r*2))) (fun a => (row (k+1) (r*2) (a-C.graph) : Word W)) m a).val = _
  rw [← hrows]
  simp only [fillSegment,ite_eq_left range]
  rw [show row (k+1) (r*2) (a-C.graph) = _ from (row_cell C hrows p back f).trans
    (congrFun (fields hk p back).symm f),Fin.val_cast_of_lt word]

end ThreeFlat.RAM.InitialRelayGraph

end OAI
