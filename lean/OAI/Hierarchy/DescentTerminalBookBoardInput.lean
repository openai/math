import OAI.Hierarchy.DescentTerminalBookBoard
import OAI.Hierarchy.DescentTerminalBookNative
import OAI.Hierarchy.DescentTerminalMaskAllocation

namespace OAI
/-! # The exact pre-Book RAM sources, with host comparator and packed group digits -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentSIMDLookup DescentTerminalPointerDigits DescentTerminalPeerChronology DescentSharedCableNames
open DescentTerminalVertexFields DescentTerminalSignedGrainWord ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def width (D blocks cap:ℕ) := D+blocks*(2+2*cap)
abbrev Source (D blocks cap:ℕ) := Fin D⊕(Fin blocks×(Fin 2⊕Fin (2*cap)))
def fieldIndex (D blocks cap:ℕ) : Source D blocks cap≃Fin (width D blocks cap) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) finSumFinEquiv).trans finProdFinEquiv)).trans finSumFinEquiv

structure Rasters (D blocks cap : ℕ) where
  roster : Bank
  geometry : MaskAllocation.Channels blocks
  wing : Fin blocks→Fin (2*cap)→Bank

def timesRow : ℕ→Expr
  | 0=>.lit 0
  | n+1=>.op .add (timesRow n) .row

theorem times_eval {H w:ℕ} (m:Memory w) (n:ℕ) (x:Fin H) : (timesRow n).eval m (x.val:Word w)=((n*x.val:ℕ):Word w) := by
  induction n with
  | zero=>simp [timesRow,Expr.eval]
  | succ n ih=>simp [timesRow,Expr.eval,RowOp.opcode,BinaryOp.eval,ih,Nat.succ_mul,Nat.cast_add]

namespace Rasters
variable {D blocks cap groups d:ℕ} (R:Rasters D blocks cap)
def neighbor (j:Fin D) : Expr:=.lookup R.roster (.op .add (timesRow D) (.lit j.val))
def compareCell (j:Fin D):Expr:=
  .branch .lt .row (R.neighbor j) (.lit 0) (.branch .lt (R.neighbor j) .row (.lit 2) (.lit 1))

def sources : Fin (width D blocks cap)→Expr:=fun j=>match (fieldIndex D blocks cap).symm j with
  | .inl l=>R.compareCell l
  | .inr (b,.inl i)=>.lookup (if i=0 then R.geometry.occupied b else R.geometry.primitive b 0) .row
  | .inr (b,.inr j)=>.lookup (R.wing b j) .row

def controller (shops base bits:ℕ) : Print.Layout (width D blocks cap):=⟨base,shops,bits,R.sources⟩

theorem source_work (equal:D=3) (j:Fin (width D blocks cap)) : (R.sources j).work≤64 := by
  subst D
  unfold sources
  cases (fieldIndex 3 blocks cap).symm j with
  | inl t => norm_num [compareCell, neighbor, timesRow, Expr.work]
  | inr t => rcases t with ⟨b, i | r⟩ <;> norm_num [Expr.work]

/-- The shared truth table splits each *single original paid RAM word* into its
group lanes locally; it issues no separate fetch per lane. -/
def measure (D blocks cap groups argc:ℕ) {d:ℕ} (z:Fin (width D blocks cap)→Cell d) : Board D groups blocks cap where
  side l:=match (z (fieldIndex D blocks cap (.inl l))).val with
    | 0=>.lt
    | 1=>.eq
    | _=>.gt
  venue g b:=
    if digit 1 g.val (z (fieldIndex D blocks cap (.inr (b,.inl 0)))).val=0 then none
    else some (digit argc g.val (z (fieldIndex D blocks cap (.inr (b,.inl 1)))).val)
  ports g b j:=
    let a:=DescentSignedCableCodec.width D cap
    DescentSignedCableCodec.decode D cap ⟨digit a g.val (z (fieldIndex D blocks cap (.inr (b,.inr j)))).val,
      digit_bound ..⟩

def lookup (D blocks cap groups argc A scale pinWords calendar:ℕ) (active:Fin groups→Fin blocks→ℕ)
    {d:ℕ} (z:Fin (width D blocks cap)→Cell d) :=
  (measure D blocks cap groups argc z).directory A scale pinWords calendar active

theorem direct {H w:ℕ} (m:Memory w) (h:Fin H) (j:Source D blocks cap)
    (short:((R.sources (fieldIndex D blocks cap j)).eval m (h.val:Word w)).val<2^d) :
    (Gather.values (d:=d) R.sources m h (fieldIndex D blocks cap j)).val=
      ((R.sources (fieldIndex D blocks cap j)).eval m (h.val:Word w)).val := by
  simp [Gather.values,Nat.mod_eq_of_lt short]

theorem side_read {H w:ℕ} (m:Memory w) (h:Fin H) (j:Fin D) (peer:Fin H) (argc:ℕ)
    (hw:2<2^w) (short:2<2^d)
    (measured:R.roster.read m ((h.val*D+j.val:ℕ):Word w)=(peer.val:Word w))
    (room:H≤2^w) :
    (measure D blocks cap groups argc (Gather.values (d:=d) R.sources m h)).side j=compare h.val peer.val := by
  have a := h.isLt.trans_le room
  have b := peer.isLt.trans_le room
  have idx : (R.neighbor j).eval m (h.val : Word w) = (peer.val : Word w) := by
    simp only [neighbor, Expr.eval, RowOp.opcode, BinaryOp.eval, times_eval]
    simpa only [Nat.mul_comm D h.val, Nat.cast_add, Nat.cast_mul] using measured
  have run : (R.compareCell j).eval m (h.val : Word w) =
      (if h.val < peer.val then 0 else if peer.val < h.val then 2 else 1) := by
    simp only [compareCell, Expr.eval, idx, DescriptorExpr.Comparison.test, decide_eq_true_eq,
      Fin.lt_def, Fin.val_cast_of_lt a, Fin.val_cast_of_lt b, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  have get (v : ℕ) (hv : v < 2^w) (hd : v < 2^d)
      (chosen : (R.compareCell j).eval m (h.val : Word w) = (v : Word w)) :
      (Gather.values (d:=d) R.sources m h (fieldIndex D blocks cap (.inl j))).val = v := by
    have src : ((R.sources (fieldIndex D blocks cap (.inl j))).eval m (h.val : Word w)).val = v := by
      simp only [sources, Equiv.symm_apply_apply, chosen, Fin.val_cast_of_lt hv]
    exact (R.direct m h (.inl j) (src.trans_lt hd)).trans src
  rcases lt_trichotomy h.val peer.val with lt | eqn | gt
  · rw [Std.compare_eq_lt.mpr lt]
    have bit := get 0 (by omega) (by omega) (by simp [run, lt])
    simp only [measure, bit]
  · rw [Std.compare_eq_iff_eq.mpr eqn]
    have bit := get 1 (by omega) (by omega) (by rw [run]; simp [eqn])
    simp only [measure, bit]
  · rw [Std.compare_eq_gt.mpr gt]
    have bit := get 2 hw short (by simp [run, gt, gt.asymm])
    simp only [measure, bit]

theorem venue_read {H w:ℕ} (m:Memory w) (h:Fin H) (b:Fin blocks) (g:Fin groups) (argc:ℕ)
    (actor:((R.geometry.occupied b).read m (h.val:Word w)).val<2^d)
    (arity:((R.geometry.primitive b 0).read m (h.val:Word w)).val<2^d) :
    (measure D blocks cap groups argc (Gather.values (d:=d) R.sources m h)).venue g b=
      if digit 1 g.val ((R.geometry.occupied b).read m (h.val:Word w)).val=0 then none
      else some (digit argc g.val ((R.geometry.primitive b 0).read m (h.val:Word w)).val) := by
  simp [measure,Gather.values,sources,Expr.eval,Nat.mod_eq_of_lt actor,Nat.mod_eq_of_lt arity]

theorem wing_read {H w:ℕ} (m:Memory w) (h:Fin H) (b:Fin blocks) (g:Fin groups) (j:Fin (2*cap)) (argc:ℕ)
    (short:((R.wing b j).read m (h.val:Word w)).val<2^d) :
    (measure D blocks cap groups argc (Gather.values (d:=d) R.sources m h)).ports g b j=
      DescentSignedCableCodec.decode D cap ⟨digit (DescentSignedCableCodec.width D cap) g.val
      ((R.wing b j).read m (h.val:Word w)).val,digit_bound ..⟩ := by
  simp [measure,Gather.values,sources,Expr.eval,Nat.mod_eq_of_lt short]

private theorem short_digit {b d n:ℕ} (g:Fin groups) (room:b*groups≤d) :
    digit b g.val (n%2^d)=digit b g.val n := by
  unfold digit
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow _ ((Nat.mul_le_mul_left b g.isLt).trans room))]

theorem venue_digits {H w:ℕ} (m:Memory w) (h:Fin H) (b:Fin blocks) (g:Fin groups) (argc:ℕ)
    (actor:groups≤d) (arity:argc*groups≤d) :
    (measure D blocks cap groups argc (Gather.values (d:=d) R.sources m h)).venue g b=
      if digit 1 g.val ((R.geometry.occupied b).read m (h.val:Word w)).val=0 then none
      else some (digit argc g.val ((R.geometry.primitive b 0).read m (h.val:Word w)).val) := by
  simp only [measure,Gather.values,sources,Equiv.symm_apply_apply,Expr.eval,
    ite_true,one_ne_zero,ite_false,Fin.val_natCast]
  rw [short_digit g (by simpa using actor : 1*groups≤d),short_digit g arity]

theorem wing_digit {H w:ℕ} (m:Memory w) (h:Fin H) (b:Fin blocks) (g:Fin groups) (j:Fin (2*cap)) (argc:ℕ)
    (short:DescentSignedCableCodec.width D cap*groups≤d) :
    (measure D blocks cap groups argc (Gather.values (d:=d) R.sources m h)).ports g b j=
      DescentSignedCableCodec.decode D cap ⟨digit (DescentSignedCableCodec.width D cap) g.val
      ((R.wing b j).read m (h.val:Word w)).val,digit_bound ..⟩ := by
  simp only [measure,Gather.values,sources,Equiv.symm_apply_apply,Expr.eval]
  congr 1
  exact Fin.ext (short_digit g short)

end Rasters
end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
