import OAI.Hierarchy.DescentResetBranchRead
import OAI.Hierarchy.DescentMeasuredDoubling
import OAI.Hierarchy.DescentNativeInputRow
import Mathlib.Algebra.Order.Floor.Div

namespace OAI
/-! # The physical integer threshold for the selected paid-contact reservation -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators

/-- All de-normalizations cancel. Only the total from the actual contact
traffic, its measured deeper bin count, and the public load scale remain. -/
theorem reservation_integer {k d e K S wire : ℕ} (Y : ℕ) (table : Fin (2^k)→ℕ)
    (dk : d≤k) (ek : e≤k) (hw : 0<wire) (hK : 0<K) (hS : 0<S) :
    rowCount Y ((S:ℝ)/wire) (pairCapacity k d e (blockMean k (fun i=>(table i:ℝ))) S K/wire)=
      (Y*(K*(∑i,table i)+S*2^max d e)) ⌈/⌉ (8*K*(S*2^max d e)) := by
  let j:=max d e
  have jk : j≤k := max_le dk ek
  have p : (2:ℝ)^k=(2:ℝ)^(k-j)*(2:ℝ)^j := by rw [←pow_add,Nat.sub_add_cancel jk]
  have pw : (0:ℝ)<wire := by exact_mod_cast hw
  have pk : (0:ℝ)<K := by exact_mod_cast hK
  have ps : (0:ℝ)<S := by exact_mod_cast hS
  have numerator :
      pairCapacity k d e (blockMean k (fun i=>(table i:ℝ))) S K/wire*Y/(8*((S:ℝ)/wire)) =
        ((Y*(K*(∑i,table i)+S*2^j):ℕ):ℝ)/((8*K*(S*2^j):ℕ):ℝ) := by
    unfold pairCapacity blockMean
    change (2^(k-j)*((∑i,(table i:ℝ))/2^k)+S/K)/wire*Y/(8*((S:ℝ)/wire))=_
    push_cast
    rw [p]
    field_simp
  have den : 0<8*K*(S*2^j) := by positivity
  apply eq_of_forall_ge_iff
  intro n
  rw [rowCount,Nat.ceil_le,numerator,div_le_iff₀ (by exact_mod_cast den : 0<((8*K*(S*2^j):ℕ):ℝ)),
    ceilDiv_le_iff_le_mul den]
  rw [Nat.mul_comm (8*K*(S*2^j)) n]
  exact_mod_cast (Iff.rfl : Y*(K*(∑i,table i)+S*2^j)≤n*(8*K*(S*2^j)) ↔ _)


end Hierarchy.DescentBaseProfile

namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentChosenRouter DescentBaseProfile
open scoped Classical BigOperators
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (traffic : V→V→Block k→ℕ)
local notation "flow" => fun v w i=>(traffic v w i:ℝ)
local notation "scale" => ((2:ℕ)^f*B)
local notation "b" => fun v=>Z.placement.b (frame.host v)
private theorem scaled_reservation {k dv dw f B K wire : ℕ} (Y : ℕ) (table : Fin (2^k) → ℕ)
    (dv_le : dv ≤ k) (dw_le : dw ≤ k) (hw : 0 < wire) (hK : 0 < K) (hB : 0 < B) :
    rowCount Y ((2:ℝ)^f*(B/wire))
      (pairCapacity k dv dw (blockMean k (fun i => (table i : ℝ))) ((2:ℕ)^f*B) K/wire) =
      (Y*(K*(∑ i, table i)+((2:ℕ)^f*B)*2^max dv dw)) ⌈/⌉
        (8*K*(((2:ℕ)^f*B)*2^max dv dw)) := by
  have hS : 0 < (2:ℕ)^f*B := Nat.mul_pos (by positivity) hB
  have counted := reservation_integer (k:=k) (d:=dv) (e:=dw) (K:=K) (S:=2^f*B) (wire:=wire)
    Y table dv_le dw_le hw hK hS
  push_cast at counted ⊢
  rw [← mul_div_assoc]
  exact counted

theorem reservation_size (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
    (hw : 0<wire) (hK : 0<K) (hB : 0<B) (v w : V) :
    let j:=max (b v) (b w)
    T.columns.size (frame.host v) (frame.host w)=
      ((2^n)*(K*(∑i,traffic v w i)+scale*2^j)) ⌈/⌉ (8*K*(scale*2^j)) := by
  have dv : b v ≤ k := (Z.placement.depth (frame.host v)).trans_eq frame.extent
  have dw : b w ≤ k := (Z.placement.depth (frame.host w)).trans_eq frame.extent
  exact (roster.2.2.1 v w).trans (scaled_reservation (k:=k) (dv:=b v) (dw:=b w)
    (f:=f) (B:=B) (K:=K) (wire:=wire) (2^n) (traffic v w) dv dw hw hK hB)

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
