import OAI.Hierarchy.DescentMaskedLookupBook
import OAI.Hierarchy.DescentPackedCensusRAM
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Native masked unary columns with a literal program, a rounded address allocation and word reads -/

namespace Hierarchy.DescentMaskedColumn
open DescentSIMDLookup DescentSixParty DescentSixParty.Chronology
open DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  inputBits : ℕ
  outputBits : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  rule : Cell inputBits→Cell outputBits

namespace Layout
variable (L : Layout)
local notation "a" => L.inputBits
local notation "b" => L.outputBits
def rows := L.hosts*chunks L.groups L.lanes
def words := Book.words (L.inputBits) L.hosts L.groups L.lanes
def result (base : ℕ) := base+2^(a*L.lanes)+2^Nat.clog 2 L.rows
def bank (base : ℕ) : Bank := ⟨L.result base,Nat.clog 2 (L.rows+1)⟩
def finish (base : ℕ) := L.result base+(L.bank base).size
def banks (base : ℕ) (src : Bank) := Book.banks base (L.inputBits) L.hosts L.groups L.lanes src
def program (w base : ℕ) (src : Bank) :=
  (Book.install L.rule L.hosts L.groups L.lanes w base).seq
    (DescentSIMDLookup.program (L.banks base src) (L.result base) L.hosts L.groups L.lanes w)
def image {w} (base : ℕ) (src : Bank) (m : Memory w) :=
  ProtocolRAM.image (L.result base) L.rows (lookup (L.banks base src)) (Book.image L.rule L.hosts L.groups L.lanes base m)
def ticks := (4+10*L.words)+(4+44*L.rows)
theorem text (w base : ℕ) (src : Bank) :
    DescentStaticWordColumn.names (L.program w base src)=15*(L.words+1)+91 :=by
  rw [program,DescentStaticWordColumn.names_seq]
  unfold Book.install DescentSIMDLookup.program words
  rw [DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_scan,lookup_work]

theorem cheap (w base : ℕ) (src : Bank) : CheapCode (L.program w base src) :=
  cheap_seq (DescentStaticWordColumn.cheap w base _ _) (scan_cheap w (L.result base) L.rows (lookup (L.banks base src)))

def phase (base : ℕ) (src : Bank) (w : ℕ) : NativePhase w :=
  ⟨L.program w base src,L.ticks,L.image base src,L.cheap w base src⟩

theorem allocation (base : ℕ) : base+L.words≤L.result base ∧ L.result base+L.rows≤L.finish base :=by
  have mask:=Nat.le_pow_clog (by decide : 1<2) L.rows
  have out:=Nat.le_pow_clog (by decide : 1<2) (L.rows+1)
  constructor
  · simpa only [result,words,Book.words,rows,Nat.add_assoc] using Nat.add_le_add_left mask (base+2^(a*L.lanes))
  · exact Nat.add_le_add_left (Nat.le_succ _ |>.trans out) _

theorem fits {w} (base : ℕ) (src : Bank) (early : src.base+src.size≤base) (capacity : L.rows≤ src.size)
    (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w) :
    Fits (L.banks base src) a b L.lanes L.hosts L.groups w (L.result base) :=by
  have space:=(L.allocation base).2.trans_lt end_
  have limit:L.result base<2^w:=(Nat.le_add_right ..).trans_lt space
  have before:base≤L.result base:=(Nat.le_add_right ..).trans (L.allocation base).1
  let dict:=2^(a*L.lanes)
  let mask:=2^Nat.clog 2 L.rows
  have dm : base+dict+mask=L.result base:=rfl
  have all : base+dict+mask<2^w:=by rw [dm];exact limit
  have sourceSpace : src.size<2^w :=
    (Nat.le_add_left _ src.base).trans_lt (early.trans_lt (before.trans_lt limit))
  have ds : dict<2^w := (Nat.le_add_left _ base).trans_lt ((Nat.le_add_right ..).trans_lt all)
  have ms : mask<2^w := (Nat.le_add_left _ (base+dict)).trans_lt all
  refine ⟨⟨Nat.two_pow_pos _,sourceSpace,early.trans before⟩,
    ⟨Nat.two_pow_pos _,ds,(Nat.le_add_right (base+dict) mask).trans dm.le⟩,
    ⟨Nat.two_pow_pos _,ms,dm.le⟩,capacity,rfl,Nat.le_pow_clog (by decide) _,space,packed⟩

theorem framed {w} (base : ℕ) (src : Bank) (m : Memory w) (early : src.base+src.size≤base)
    (capacity : L.rows≤ src.size) (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w) :
    (L.phase base src w).Runs m ∧ ∀i,i<base ∨ L.finish base ≤ i → (L.phase base src w).image m i=m i :=by
  have fit:=L.fits base src early capacity packed end_
  obtain ⟨bounds,post⟩:=L.allocation base
  obtain ⟨loaded,_,frame,_⟩:=Book.mount L.rule L.hosts L.groups L.lanes base src m
    (bounds.trans_lt ((Nat.le_add_right ..).trans_lt fit.output))
  let e:=lookup (L.banks base src)
  let tab:=Book.image L.rule L.hosts L.groups L.lanes base m
  have cpu : (scan w (L.result base) L.rows e).Exec tab (ProtocolRAM.image (L.result base) L.rows e tab)
      (4+L.rows*(2*e.work+4)) := scan_exec (L.result base) L.rows e tab
    (show (lookup (L.banks base src)).Fits w (L.result base) from by
      simp [lookup,Expr.Fits,fit.source,fit.dictionary,fit.mask]) fit.output
  constructor
  · change (L.program w base src).Exec m _ _
    have duration : 4+L.rows*(2*e.work+4)=4+44*L.rows := by
      rw [show e.work=20 from lookup_work _,show 2*20+4=44 by decide,Nat.mul_comm L.rows 44]
    rw [duration] at cpu
    intro P R K mach pc reg pub exit rom advice cfg raw enter same
    exact Procedure.Exec.then loaded cpu mach pc reg pub exit rom advice cfg raw enter same
  · intro i away
    have lo:base≤L.result base:=(Nat.le_add_right ..).trans bounds
    change ProtocolRAM.image _ _ _ _ i=_
    rcases away with lt|gt
    · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ i (.inl (lt.trans_le lo))).trans (frame i (.inl lt))
    · have beyond : L.result base + L.rows ≤ i := post.trans gt
      exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ i (.inr beyond)).trans
        (frame i (.inr (bounds.trans ((Nat.le_add_right ..).trans beyond))))

theorem any {w} (base : ℕ) (src : Bank) (m : Memory w) (early : src.base+src.size≤base)
    (capacity : L.rows≤ src.size) (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w) :
    (L.phase base src w).Runs m :=(L.framed base src m early capacity packed end_).1

theorem reads {w} (base : ℕ) (src : Bank) (m : Memory w) (early : src.base+src.size≤base)
    (capacity : L.rows≤ src.size) (packed : L.lanes*max a b≤w/2) (end_ : L.finish base<2^w)
    (input : Fin L.hosts→Fin L.groups→Cell L.inputBits)
    (prior : Reads src input L.lanes m) :
    Reads (L.bank base) (fun h g=>L.rule (input h g))
      L.lanes ((L.phase base src w).image m) :=by
  have fit:=L.fits base src early capacity packed end_
  obtain ⟨bounds,_⟩:=L.allocation base
  obtain ⟨_,fixed,frame,_⟩:=Book.mount L.rule L.hosts L.groups L.lanes base src m
    (bounds.trans_lt ((Nat.le_add_right ..).trans_lt fit.output))
  let tab:=Book.image L.rule L.hosts L.groups L.lanes base m
  have kept : PinFrame (M:=L.lanes) (L.banks base src) L.rule input tab:=by
    refine ⟨fun i k=>congrArg (fun t : Word w=>Computability.VPVNP.RAMSerialization.wordBits w t k) (fixed i),?_⟩
    intro p
    exact (frame _ (.inl ((Nat.add_lt_add_left ((row _ _ _ p).isLt.trans_le capacity) _).trans_le early))).trans (prior p)
  intro p
  exact (PackedCensus.col_read (L.banks base src) (L.result base) fit L.rule input tab kept p)

theorem tariff (w base : ℕ) (src : Bank) :
    L.ticks+7*DescentStaticWordColumn.names (L.program w base src)=750+115*L.words+44*L.rows := by
  rw [text,ticks]
  omega

private theorem rounded (n : ℕ) : 2^Nat.clog 2 n≤2*n+1 :=by
  by_cases lo : n≤1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp lo with z|z <;> rw [z] <;> decide
  · have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
    cases dep : Nat.clog 2 n with
    | zero=>omega
    | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega

theorem half_page (h : ℕ) (pitch : a*L.lanes≤h/2) : L.words≤2^(h/2)+L.rows :=by
  exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) pitch) _

theorem end_space (base h : ℕ) (pitch : a*L.lanes≤h/2) :
    L.finish base≤base+2^(h/2)+4*L.rows+4 :=by
  have rd0:=rounded L.rows
  have rd1:=rounded (L.rows+1)
  have dict:2^(a*L.lanes)≤2^(h/2):=Nat.pow_le_pow_right (by decide) pitch
  change base+2^(a*L.lanes)+2^Nat.clog 2 L.rows+2^Nat.clog 2 (L.rows+1)≤_
  omega

theorem charged (h w base : ℕ) (src : Bank) (pitch : a*L.lanes≤h/2) :
    L.ticks+7*DescentStaticWordColumn.names (L.program w base src)≤
      750+115*2^(h/2)+159*L.rows :=by
  rw [L.tariff]
  have bound:=L.half_page h pitch
  omega
end Layout
end
end Hierarchy.DescentMaskedColumn

end OAI
