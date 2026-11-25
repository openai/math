import OAI.Hierarchy.DescentMeasuredHeaderRAM

namespace OAI
/-! # Native emission of all three measured row headers in one contiguous shelf -/
namespace Hierarchy.DescentMeasuredHeader
open DescentMeasuredWeights DescentPackedExchange ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H k Δ start : ℕ}
private def rate (e : Expr) (n : ℕ) := 4+n*(2*e.work+4)
def headerTime (L : Tape) (H k Δ : ℕ) :=
  let rows := H*(k+1)+H*Δ
  rate (column L H k .live) rows+rate (column L H k .depth) rows+rate (column L H k .gain) rows

def headerProgram (L : Tape) (w start H k Δ : ℕ) : Procedure w :=
  let rows := H*(k+1)+H*Δ
  ((scan w start rows (column L H k .live)).seq (scan w (start+rows) rows (column L H k .depth))).seq
    (scan w (start+2*rows) rows (column L H k .gain))

def headerMem (L : Tape) (start H k Δ : ℕ) (m : Memory w) :=
  let rows := H*(k+1)+H*Δ
  image (start+2*rows) rows (column L H k .gain) (image (start+rows) rows (column L H k .depth)
    (image start rows (column L H k .live) m))

local notation "N" => H*(k+1)+H*Δ

theorem fits_later (L : Tape) (safe : Fits L w H k Δ start) {stop : ℕ} (h : start≤ stop) : Fits L w H k Δ stop :=
  ⟨fun z hz=>⟨(safe.fits z hz).1,(safe.fits z hz).2.1,(safe.fits z hz).2.2.trans h⟩,
    safe.fixed,safe.sites,safe.ports⟩

theorem header_exec (L : Tape) (m : Memory w) (safe : Fits L w H k Δ start) (room : start+3*N<2^w) :
    (headerProgram L w start H k Δ).Exec m (headerMem L start H k Δ m) (headerTime L H k Δ) ∧
    CheapCode (headerProgram L w start H k Δ) := by
  refine ⟨?_,cheap_seq (cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)) (@scan_cheap _ _ _ _)⟩
  exact Procedure.Exec.then (Procedure.Exec.then
    (scan_exec _ _ _ _ (column_fits L safe .live) (by omega))
    (scan_exec _ _ _ _ (column_fits L (fits_later L safe (by omega)) .depth) (by omega)))
    (scan_exec _ _ _ _ (column_fits L (fits_later L safe (by omega)) .gain) (by omega))

theorem header_time (L : Tape) (H k Δ : ℕ) : headerTime L H k Δ≤12+780*(H*(k+1)+H*Δ) := by
  have a:=column_cost L H k .live
  have b:=column_cost L H k .depth
  have c:=column_cost L H k .gain
  simp only [headerTime,rate]
  have mul (n : ℕ) (hn : n≤128) : (H*(k+1)+H*Δ)*(2*n+4)≤(H*(k+1)+H*Δ)*260 :=
    Nat.mul_le_mul_left _ (by omega)
  have:=mul _ a;have:=mul _ b;have:=mul _ c
  omega

theorem image_frame {w : ℕ} (e : Expr) (m : Memory w) {out n a : ℕ} (low : a<out) :
    image out n e m a=m a := by simp [image,fillSegment,not_le.mpr low]

theorem image_val {w : ℕ} (e : Expr) (m : Memory w) {out n : ℕ} (i : Fin n) :
    image out n e m (out+i.val)=e.eval m (i.val:Word w) := by
  simp [image,fillSegment,show out+i.val<out+n by have:=i.isLt;omega,Nat.cast_add]

theorem header_frame (L : Tape) (m : Memory w) {a : ℕ} (ha : a<start) : headerMem L start H k Δ m a=m a := by
  unfold headerMem
  rw [image_frame _ _ (by omega),image_frame _ _ (by omega),image_frame _ _ ha]

def fieldNumber : Field→ℕ | .live=>0| .depth=>1| .gain=>2

theorem header_read (L : Tape) (safe : Fits L w H k Δ start) (b : Fin H→ℕ)
    (next : Port H Δ→Option (Fin H)) (f B K : ℕ) (m : Memory w)
    (head : contents (k:=k) L b next f B K m) (size : H<2^w) (wide : 2*k+1<2^w)
    (bounded : ∀v,b v≤k) (field : Field) (i : Rows H k Δ) :
    headerMem L start H k Δ m (start+fieldNumber field*N+(rowOrd H k Δ i).val)=
      (value b next f B K field i:Word w) := by
  let a:=image start N (column L H k .live) m
  let d:=image (start+N) N (column L H k .depth) a
  have ha (z : ℕ) (hz : z<start) : a z=m z :=image_frame _ _ hz
  have hd (z : ℕ) (hz : z<start) : d z=m z :=(image_frame _ _ (by omega)).trans (ha z hz)
  have hi:=(rowOrd H k Δ i).isLt
  have read:=column_read start L safe b next f B K m head size wide bounded field i
  cases field with
  | live=>
    simp only [fieldNumber,Nat.zero_mul,Nat.add_zero,headerMem]
    rw [image_frame _ _ (by omega),image_frame _ _ (by omega),image_val]
    exact read
  | depth=>
    simp only [fieldNumber,Nat.one_mul,headerMem]
    rw [image_frame _ _ (by omega),image_val]
    exact (eval_below _ _ m a (column_fits L safe .depth) ha).trans read
  | gain=>
    unfold headerMem
    rw [show fieldNumber .gain=2 by rfl,image_val]
    exact (eval_below _ _ m d (column_fits L safe .gain) hd).trans read

end
end Hierarchy.DescentMeasuredHeader

end OAI
