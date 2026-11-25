import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Clip or zero-pad packed prior operand and role banks to the current host rectangle -/
namespace Hierarchy.DescentOrdinaryHostPad
open DescentSIMDLookup DescentPackedColony DescentSixParty.Chronology ProtocolRAM DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

structure Rect where
  oldH : ℕ
  newH : ℕ
  groups : ℕ
  pages : ℕ
  lanes : ℕ

def extend {H G a : ℕ} (currentH : ℕ) (value : Fin H→Fin G→Cell a) (h : Fin currentH) (g : Fin G) : Cell a :=
  if live : h.val<H then value ⟨h.val,live⟩ g else 0

namespace Rect
variable (R : Rect)
def rows :=R.newH*chunks R.groups R.lanes
def kept :=min (R.oldH*chunks R.groups R.lanes) R.rows
def total :=(R.pages+1)*R.rows
def finish (base : ℕ) :=base+R.total+2^Nat.clog 2 (R.rows+1)
def placedBank (base page : ℕ) : Bank :=⟨base+page*R.rows,Nat.clog 2 (R.rows+1)⟩
def bank (base : ℕ) (p : Fin R.pages) :=R.placedBank base p.val
def zero (base : ℕ) :=R.placedBank base R.pages

def column (src : Fin R.pages→Bank) (j : ℕ) : Expr :=
  if live : j<R.pages then .lookup (src ⟨j,live⟩) .row else .lit 0
def copies (base : ℕ) (src : Fin R.pages→Bank) :=
  DescentPackedFlowBatch.passes base R.kept R.rows (R.column src) 0 R.pages

def phase (base : ℕ) (src : Fin R.pages→Bank) (w : ℕ) : NativePhase w :=
  ⟨(scan w base R.total (.lit 0)).seq (ProtocolRAM.program w (R.copies base src)),
    (4+R.total*6)+clock (R.copies base src),
    fun m=>result (R.copies base src) (ProtocolRAM.image base R.total (.lit 0) m),
    cheap_seq (scan_cheap w base R.total (.lit 0)) (program_cheap w (R.copies base src))⟩

theorem translated (base : ℕ) : R.finish base=base+R.finish 0:=by simp [finish,Nat.add_assoc]
theorem base_le (base : ℕ) : base≤R.finish base:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)

variable (base : ℕ) (src : Fin R.pages→Bank) {w : ℕ} (m : Memory w)
local notation "cs₀" => R.copies base src
local notation "clear₀" => ProtocolRAM.image base R.total (.lit 0) m
variable (fits : ∀p,(src p).Fits w base) (room : R.finish base<2^w)

include room in
private theorem page_placed (j : ℕ) (bound : j≤R.pages) :
    (R.placedBank base j).Fits w (R.finish base) ∧ R.rows≤(R.placedBank base j).size :=by
  have reach:=Nat.mul_le_mul_right R.rows (bound.trans (Nat.le_succ _))
  have safe:(R.placedBank base j).base+(R.placedBank base j).size≤R.finish base:=
    Nat.add_le_add_right (Nat.add_le_add_left reach _) _
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (safe.trans_lt room),safe⟩,
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)⟩

include room in
theorem placed (p : Fin R.pages) : (R.bank base p).Fits w (R.finish base) ∧ R.rows≤(R.bank base p).size :=
  R.page_placed base room p p.isLt.le

include room in
theorem zero_placed : (R.zero base).Fits w (R.finish base) ∧ R.rows≤(R.zero base).size :=
  R.page_placed base room R.pages le_rfl

include fits room in
private theorem acquired :
    (ProtocolRAM.program w cs₀).Exec clear₀ (result cs₀ clear₀) (clock cs₀) ∧
      (∀p : Fin R.pages,∀j : Fin R.kept,result cs₀ clear₀ (base+p.val*R.rows+j.val)=(R.column src p.val).eval clear₀ (j.val:Word w)) ∧
        ∀a<base,result cs₀ clear₀ a=clear₀ a :=by
  have limit : base+R.total<2^w :=(Nat.le_add_right ..).trans_lt room
  apply DescentPackedFlowBatch.execute base R.kept R.rows R.pages (R.column src) clear₀ _ _ (Nat.min_le_right ..)
  · intro j hj
    rw [column,dite_eq_left hj]
    exact ⟨fits ⟨j,hj⟩,trivial⟩
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_right R.rows (Nat.le_succ R.pages)) _).trans_lt limit

include fits room in
theorem any : (R.phase base src w).Runs m ∧ ∀i, i < base ∨ R.finish base ≤ i → (R.phase base src w).image m i=m i :=by
  have total_ : base+R.total<2^w :=(Nat.le_add_right ..).trans_lt room
  have copied:=R.acquired base src m fits room
  have zeros : (scan w base R.total (.lit 0)).Exec m clear₀ (4+R.total*6) :=
    scan_exec base R.total (.lit 0) m trivial total_
  constructor
  · intro P S K mach pc reg pub stop rom advice cfg raw enter same
    exact Procedure.Exec.then zeros copied.1 mach pc reg pub stop rom advice cfg raw enter same
  · intro i outside
    change result cs₀ clear₀ i=m i
    rcases outside with lo|hi
    · exact (copied.2.2 i lo).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl lo))
    · have after : base+R.total ≤ i :=(Nat.le_add_right ..).trans hi
      have close : base+R.pages*R.rows ≤ i :=(Nat.add_le_add_left (Nat.mul_le_mul_right R.rows (Nat.le_succ R.pages)) _).trans after
      exact (DescentPackedFlowBatch.above base R.kept R.rows _ clear₀ 0 R.pages i (Nat.min_le_right ..)
        (by simpa only [Nat.zero_add] using close)).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr after))

private theorem missed (ps : List Pass) (memory : Memory w) (address : ℕ)
    (skip : ∀p∈ps,address<p.out ∨ p.out+p.rows≤address) : result ps memory address=memory address :=by
  induction ps generalizing memory with
  | nil=>rfl
  | cons p ps ih=>
    exact (ih (p.apply memory) (fun q in_=>skip q (List.mem_cons_of_mem _ in_))).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (skip p List.mem_cons_self))

private theorem clear_at (page idx : ℕ) (padded : page≤R.pages) (valid : idx<R.rows)
    (absent : R.pages≤page ∨ R.kept ≤ idx) :
    result cs₀ clear₀ (base+page*R.rows+idx)=0 :=by
  have index_lt : page*R.rows+idx<R.total:=by
    have b:=Nat.mul_le_mul_right R.rows padded
    change _<(R.pages+1)*R.rows
    rw [Nat.succ_mul]
    omega
  rw [missed cs₀ clear₀ _ (by
    intro p h
    obtain ⟨j,_,lt,rfl⟩:=DescentPackedFlowBatch.interval _ _ _ _ _ _ _ h
    change base+page*R.rows+idx<base+j*R.rows ∨ base+j*R.rows+R.kept≤base+page*R.rows+idx
    have small:R.kept≤R.rows:=Nat.min_le_right ..
    rcases lt_trichotomy j page with lower|equal|later
    · have reach:=Nat.mul_le_mul_right R.rows (Nat.succ_le_of_lt lower)
      rw [Nat.succ_mul] at reach
      omega
    · rw [equal]
      simp only [Nat.zero_add] at lt
      rcases absent with last|ghost <;> omega
    · have reach:=Nat.mul_le_mul_right R.rows (Nat.succ_le_of_lt later)
      rw [Nat.succ_mul] at reach
      omega)]
  have cell:=ProtocolRAMGeneratedWrite.read_image base R.total (.lit 0) m ⟨page*R.rows+idx,index_lt⟩
  simpa only [Nat.add_assoc,Expr.eval,Nat.cast_zero] using cell

private theorem packed_zero (a M : ℕ) : encode a M (fun _=>0)=0 :=by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin M=>(0:Cell a))).val=0
  simp []

private theorem zero_data {H G b M} (i : Row H G M) :
    data (fun (_ : Fin H) (_ : Fin G)=>(0:Cell b)) i=0 :=by
  simp [data,packed_zero]

private theorem row_index {H G M} (p : Row H G M) :
    (row H G M p).val=p.1.val*chunks G M+p.2.val :=by
  simp [row,finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]

include fits room in
theorem reads {bits : ℕ} (page : Fin R.pages) (value : Fin R.oldH→Fin R.groups→Cell bits)
    (srcSpan : R.oldH*chunks R.groups R.lanes≤(src page).size) (read : Reads (src page) value R.lanes m) :
    Reads (R.bank base page) (extend R.newH value) R.lanes ((R.phase base src w).image m) :=by
  have acquired:=R.acquired base src m fits room
  intro t
  let pos:=(row R.newH R.groups R.lanes t).val
  have good : pos<R.rows :=(row R.newH R.groups R.lanes t).isLt
  change result cs₀ clear₀ (base+page.val*R.rows+pos)=((data (extend R.newH value) t).val:Word w)
  by_cases valid : t.1.val<R.oldH
  · let u : Row R.oldH R.groups R.lanes:=(⟨t.1.val,valid⟩,t.2)
    have same : (row R.oldH R.groups R.lanes u).val=pos:=by simp only [pos,row_index,u]
    have small : pos<R.oldH*chunks R.groups R.lanes:=same ▸ (row R.oldH R.groups R.lanes u).isLt
    have word : data (extend R.newH value) t=data value u:=by
      apply congrArg (encode _ _)
      funext j
      simp only [extend,u,dite_eq_left valid]
    have cell:=acquired.2.1 page ⟨pos,lt_min small good⟩
    simp only [column,dite_eq_left page.isLt,Fin.eta] at cell
    have mem:=DescentPackedZip.bank_read (src page) clear₀ (small.trans_le srcSpan) (fits page)
    have before : (src page).base+pos<base:=(Nat.add_lt_add_left (small.trans_le srcSpan) _).trans_le (fits page).2.2
    rw [word]
    exact ((cell.trans mem).trans (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl before))).trans
      (by simpa only [same] using read u)
  · have past : R.oldH*chunks R.groups R.lanes≤pos:=by
      change _≤(row R.newH R.groups R.lanes t).val
      rw [row_index]
      exact (Nat.mul_le_mul_right (chunks R.groups R.lanes) (Nat.le_of_not_gt valid)).trans (Nat.le_add_right ..)
    have word : data (extend R.newH value) t=0:=by
      unfold data
      have bits_ : (fun j : Fin R.lanes=>if h : t.2.val*R.lanes+j.val<R.groups then
          extend R.newH value t.1 ⟨_,h⟩ else 0)=fun _=>0 :=by funext j; simp [extend,valid]
      rw [bits_,packed_zero]
    rw [word]
    exact R.clear_at base src m page.val pos page.isLt.le good (.inr ((Nat.min_le_left ..).trans past))

theorem zero_reads {bits : ℕ} : Reads (R.zero base) (fun (_:Fin R.newH) (_:Fin R.groups)=>(0:Cell bits)) R.lanes
    ((R.phase base src w).image m) :=by
  intro t
  change result cs₀ clear₀ (base+R.pages*R.rows+(row R.newH R.groups R.lanes t).val)=_
  rw [zero_data]
  exact R.clear_at base src m R.pages _ le_rfl (row R.newH R.groups R.lanes t).isLt (.inl le_rfl)

end Rect
end
end Hierarchy.DescentOrdinaryHostPad

end OAI
