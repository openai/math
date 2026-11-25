import OAI.Hierarchy.ProtocolRAMLocalCharge
import OAI.Hierarchy.ProtocolRAMFeed

namespace OAI
/-! # Physical packet debits, unconditional reserve feeds and capped stock columns

Each demand occurrence is counted, including repeated occurrences of the same option.
One selected histogram determines both the wire credit and the debits. A second pair
of native passes records the retained bits and the exact number discharged at the cap.
-/

namespace Hierarchy.ProtocolRAM.StockAccounts
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {w k d : ℕ} {F E A : Type*} [Field F] [Nonempty (Fin k)] [Fintype E] [Fintype A]
  {edge : E → Chord k} {req : A → E}

omit [Fintype E] in
private theorem debited_mul (req : A→E) (n bits : ℕ) (e : E) :
    debited req (n*bits) e = n*debited req bits e := by
  simp [debited,Finset.mul_sum,mul_ite]

omit [Fintype E] in
theorem debited_le_card_width (req : A→E) (bits : ℕ) (e : E) :
    debited req bits e ≤ Fintype.card A*bits := by
  unfold debited
  calc
    _ ≤ ∑ _a : A,bits := Finset.sum_le_sum fun a _ => by split <;> omega
    _ = _ := by simp

/-- One fixed layout bound covers the old stock, histogram multiplicities, packet
outputs, and an unconditional feed of at most one payload. -/
def WordRoom (w terms coeff stock payload : ℕ) : Prop :=
  (terms+coeff+stock+2)*(payload+1)<2^w

/-- A fixed catalogue and stock cap fit uniformly even for payloads up to the full
native phase scale. -/
theorem eventual_room (terms coeff stock : ℕ) :
    ∀ᶠ z : ℕ in Filter.atTop, ∀ payload≤2^z, WordRoom (64*z) terms coeff stock payload := by
  filter_upwards [Filter.eventually_ge_atTop (terms+coeff+stock+2)] with z large
  intro payload small
  have fixed := large.trans (Nat.lt_two_pow_self.le : z≤2^z)
  have positive := Nat.two_pow_pos z
  have enough : 2*z+1<64*z := by omega
  unfold WordRoom
  calc
    _ ≤ 2^z*2^(z+1) := Nat.mul_le_mul fixed (by rw [pow_succ];omega)
    _ = 2^(2*z+1) := by rw [←pow_add]; congr 1; omega
    _ < _ := Nat.pow_lt_pow_right (by decide) enough

private theorem limits {terms coeff stock payload : ℕ} (room : WordRoom w terms coeff stock payload) :
    terms≤2^w ∧ coeff<2^w ∧ payload<2^w ∧ terms*payload<2^w ∧
    stock*payload+coeff*payload+payload<2^w := by
  unfold WordRoom at room
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at room
  omega

omit [Nonempty (Fin k)] in
/-- A committed fixed-length record is decoded before the natural stock equation
is asserted. The actual returned word, demand word and installed-width word all
come from the same native row. -/
theorem packet_selected (P : Probe.Packet F edge req) (extra : ℕ) (b : Batch (P.terms+extra) d)
    (m : Memory w) (r : Word w) (i : Fin d) (e : E) (tab : Fin (P.terms+extra) → Expr)
    (selected : b.selected m r) (alphabet : (b.termCount.read m (b.packet.eval m r)).val=P.terms)
    (accepted : (b.ifAdmitted (.lit 1) (.lit 0)).eval m r=1) (word : 0<w)
    (opts : ∀ j,(tab j).eval m r=(padCounts P.count extra j e : Word w))
    (coeff : ∀ j,P.count j e≤b.maxWidth)
    (demand : (b.perCopy i).eval m r=(debited req P.width e : Word w))
    (demandCap : debited req P.width e≤b.maxWidth) (stock payload : ℕ)
    (old : ((b.stock i).eval m r).val≤ stock*payload) (copies : b.copies≤payload)
    (room : WordRoom w (P.terms+extra) b.maxWidth stock payload) :
    ∃ h : Histogram (Fin P.terms) b.copies,
      (∀ j,((padHistogram h extra).val j).val=((b.field j).eval m r).val) ∧
      ((b.wire tab).eval m r).val=histWidth P.count h e ∧
      ((b.need i).eval m r).val=debited req (b.copies*P.width) e ∧
      ((b.stock i).eval m r).val+histWidth P.count h e=
        ((b.nextStock i (b.wire tab)).eval m r).val+debited req (b.copies*P.width) e ∧
      ((b.nextStock i (b.wire tab)).eval m r).val≤ stock*payload+b.maxWidth*payload := by
  obtain ⟨terms,coefFit,paid,total,space⟩ := limits room
  have copiesFit := copies.trans_lt paid
  have sumFit := (Nat.mul_le_mul_left (P.terms+extra) copies).trans_lt total
  obtain ⟨h,fields,_⟩ := decoded_packet P extra b m r selected alphabet terms copiesFit sumFit word accepted
  have ok : b.withinPacket m r ∧ (∑ j,((b.field j).eval m r).val)=b.copies := by
    by_contra fail
    rw [b.eval_ifAdmitted m r _ _ terms copiesFit sumFit] at accepted
    simp only [ite_eq_left selected,ite_eq_right fail] at accepted
    have one : 1<2^w := Nat.one_lt_two_pow word.ne'
    have no := congrArg Fin.val accepted
    change (0:Word w).val=(1:Word w).val at no
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt one] at no
    exact Nat.zero_ne_one no
  have wireSize : histWidth P.count h e ≤ b.maxWidth*payload := by
    rw [Nat.mul_comm b.maxWidth]
    exact (histWidth_le P.count h e b.maxWidth coeff).trans (Nat.mul_le_mul_right _ copies)
  have wire : ((b.wire tab).eval m r).val=histWidth P.count h e := by
    rw [packet_wire P extra b m r e tab h selected ok.1 terms copiesFit sumFit
      (fun j=>(fields j).symm) opts coeff coefFit,Fin.val_cast_of_lt (by omega)]
  have per : ((b.perCopy i).eval m r).val=debited req P.width e := by
    rw [demand,Fin.val_cast_of_lt (demandCap.trans_lt coefFit)]
  have cost : b.copies*debited req P.width e≤b.maxWidth*payload := by
    rw [Nat.mul_comm b.maxWidth]
    exact Nat.mul_le_mul copies demandCap
  have need : ((b.need i).eval m r).val=debited req (b.copies*P.width) e := by
    rw [b.need_bits m r i (per.le.trans demandCap) coefFit (by rw [per];omega),per,debited_mul]
  have haveStock := selected.2.2 i
  have next := b.nextStock_selected m r i (b.wire tab) selected ok.1 ok.2 terms copiesFit sumFit (by omega)
  exact ⟨h,fields,wire,need,by omega,by omega⟩

theorem packet_inactive {q : ℕ} (b : Batch q d) (m : Memory w) (r : Word w) (i : Fin d)
    (tab : Fin q→Expr) (inactive : ¬b.selected m r) :
    (b.wire tab).eval m r=0 ∧ (b.nextStock i (b.wire tab)).eval m r=(b.stock i).eval m r := by
  exact ⟨b.wire_skipped m r tab inactive,by rw [Batch.nextStock,b.eval_ifSelected,ite_eq_right inactive]⟩

theorem packet_invalid {q : ℕ} (b : Batch q d) (m : Memory w) (r : Word w) (i : Fin d)
    (tab : Fin q→Expr) (selected : b.selected m r)
    (invalid : ¬(b.withinPacket m r ∧ (∑ j,((b.field j).eval m r).val)=b.copies))
    {stock payload : ℕ} (copies : b.copies≤payload) (room : WordRoom w q b.maxWidth stock payload) :
    (b.wire tab).eval m r=0 ∧ (b.nextStock i (b.wire tab)).eval m r=(b.stock i).eval m r := by
  obtain ⟨terms,_,paid,total,_⟩ := limits room
  have k := (Nat.mul_le_mul_left q copies).trans_lt total
  simp only [Batch.wire,Batch.nextStock,b.eval_ifSelected,ite_eq_left selected,
    b.eval_ifPacket m r _ _ terms (copies.trans_lt paid) k,ite_eq_right invalid,Expr.eval,Nat.cast_zero,and_self]

/-- The reserve is added outside the batch's two gates. Both inactive and rejected
rows therefore receive the same prescribed mesh slice as a committed row. -/
theorem feed_exact {q : ℕ} (b : Batch q d) (i : Fin d) (tab : Fin q→Expr)
    (bank : Bank) (stride steps mesh bits : ℕ) (reserve : Expr) (m : Memory w) (r : Word w)
    (saved : reserve.eval m r=(bits : Word w))
    (entry : bank.read m ((mesh*stride+bits:ℕ):Word w)=(AdaptiveProbe.slice steps bits mesh : Word w))
    {stock payload : ℕ} (room : WordRoom w q b.maxWidth stock payload) (which : mesh<steps)
    (reserveBound : bits≤payload)
    (bound : ((b.nextStock i (b.wire tab)).eval m r).val≤ stock*payload+b.maxWidth*payload) :
    ((feed bank stride mesh reserve (b.nextStock i (b.wire tab))).eval m r).val=
      ((b.nextStock i (b.wire tab)).eval m r).val+AdaptiveProbe.slice steps bits mesh := by
  have all := AdaptiveProbe.slice_sum steps bits (by omega)
  have part : AdaptiveProbe.slice steps bits mesh≤bits := by
    exact (Finset.single_le_sum (fun j _=>Nat.zero_le (AdaptiveProbe.slice steps bits j))
      (Finset.mem_range.mpr which)).trans_eq all
  have limit := (limits room).2.2.2.2
  let x := (b.nextStock i (b.wire tab)).eval m r
  have value := feed_readback bank stride steps mesh bits x.val reserve (b.nextStock i (b.wire tab))
    m r saved (Fin.cast_val_eq_self x).symm entry
  exact (congrArg Fin.val value).trans (Fin.val_cast_of_lt (by dsimp only [x];omega))

/-- Keep the capped word and discharge the excess into its own physical column. -/
def clipped (cap : ℕ) (total : Expr) : Expr := .branch .lt total (.lit cap) total (.lit cap)
def overflow (cap : ℕ) (total : Expr) : Expr := .op .sub total (clipped cap total)

def columns (out rows cap : ℕ) (total : Expr) : List Pass :=
  [⟨out,rows,clipped cap total⟩,⟨out+rows,rows,overflow cap total⟩]

theorem clipped_word (cap : ℕ) (total : Expr) (m : Memory w) (r : Word w)
    (fit : cap<2^w) : ((clipped cap total).eval m r).val=min (total.eval m r).val cap := by
  by_cases h : (total.eval m r).val<cap
  · simp [clipped,Expr.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt fit,h,min_eq_left h.le]
  · simp [clipped,Expr.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt fit,h,min_eq_right (Nat.le_of_not_gt h)]

theorem overflow_word (cap : ℕ) (total : Expr) (m : Memory w) (r : Word w)
    (fit : cap<2^w) : ((overflow cap total).eval m r).val=(total.eval m r).val-min (total.eval m r).val cap := by
  let a := total.eval m r
  let b := (clipped cap total).eval m r
  have hb : b.val=min a.val cap := clipped_word cap total m r fit
  have h : b.val≤a.val := hb.trans_le (min_le_left ..)
  have cast : ((a.val-b.val : ℕ):Word w)=a-b := by rw [Nat.cast_sub h]; simp
  change (a-b).val=a.val-min a.val cap
  rw [←cast,Fin.val_cast_of_lt ((Nat.sub_le ..).trans_lt a.isLt),hb]

private theorem covered (out cap : ℕ) (total : Expr) (early : total.inputEnd≤out) :
    (clipped cap total).inputEnd≤out ∧ (overflow cap total).inputEnd≤out := by
  simp [clipped,overflow,Expr.inputEnd,early]

/-- Both passes are ordinary deterministic scans on a bank disjoint from their
inputs. The second pass reads the original total and costs one subtraction more. -/
theorem columns_exec (out rows cap : ℕ) (total : Expr) (m : Memory w)
    (early : total.inputEnd≤out) (endFit : out+rows+rows<2^w) :
    (program w (columns out rows cap total)).Exec m (result (columns out rows cap total) m)
      (clock (columns out rows cap total)) := by
  apply program_exec
  intro p hp
  simp only [columns,List.mem_cons,List.not_mem_nil,or_false] at hp
  obtain ⟨a,b⟩ := covered out cap total early
  rcases hp with rfl|rfl
  · exact Pass.fits_of_span _ a (by simpa only using (show out+rows<2^w by omega))
  · apply Pass.fits_of_span
    · change (overflow cap total).inputEnd≤out+rows
      omega
    · exact endFit

private theorem image_inside (out rows : ℕ) (e : Expr) (m : Memory w) (i : Fin rows) :
    image out rows e m (out+i.val)=e.eval m (i.val:Word w) := by
  have inside : out≤out+i.val ∧ out+i.val<out+rows := by omega
  simp [image,fillSegment,inside,Nat.cast_add]

/-- Project the genuinely written words. In particular, retained plus discharged
is exactly the pre-cap natural number of bits. -/
theorem columns_read (out rows cap : ℕ) (total : Expr) (m : Memory w) (i : Fin rows)
    (early : total.inputEnd≤out) (endFit : out+rows+rows<2^w) (fit : cap<2^w) :
    let final := result (columns out rows cap total) m
    let bits := (total.eval m (i.val:Word w)).val
    (final (out+i.val)).val=min bits cap ∧ (final (out+rows+i.val)).val=bits-min bits cap ∧
      (final (out+i.val)).val+(final (out+rows+i.val)).val=bits := by
  let mid := image out rows (clipped cap total) m
  let last := image (out+rows) rows (overflow cap total) mid
  have lo : ∀ j<out,mid j=m j := fun j hj=>by simp [mid,image,fillSegment,not_le.mpr hj]
  have stay : last (out+i.val)=mid (out+i.val) := by
    have hi : out+i.val<out+rows := by omega
    simp [last,image,fillSegment,not_le.mpr hi]
  have keep : (last (out+i.val)).val=min (total.eval m (i.val:Word w)).val cap := by
    exact (congrArg Fin.val (stay.trans (image_inside out rows (clipped cap total) m i))).trans
      (clipped_word cap total m _ fit)
  have saved : (last (out+rows+i.val)).val=(total.eval m (i.val:Word w)).val-
      min (total.eval m (i.val:Word w)).val cap := by
    change (image (out+rows) rows (overflow cap total) mid (out+rows+i.val)).val=_
    rw [image_inside,eval_below _ _ m mid ((overflow cap total).fits_of_inputEnd (covered out cap total early).2 (by omega)) lo]
    exact overflow_word cap total m _ fit
  exact ⟨keep,saved,by change (last _).val+(last _).val=_;rw [keep,saved];omega⟩

/-- The emitted banks give the signed physical balance even on a skipped packet.
The supplied packet balance can use zero install and zero debit in that case. -/
theorem fed_columns_account {q : ℕ} (b : Batch q d) (i : Fin d) (tab : Fin q→Expr)
    (bank : Bank) (stride steps mesh bits : ℕ) (reserve : Expr) (m : Memory w)
    (out rows cap : ℕ) (j : Fin rows) (installed consumed : ℕ) {stock payload : ℕ}
    (room : WordRoom w q b.maxWidth stock payload) (which : mesh<steps) (reserveBound : bits≤payload)
    (saved : reserve.eval m (j.val:Word w)=(bits:Word w))
    (entry : bank.read m ((mesh*stride+bits:ℕ):Word w)=(AdaptiveProbe.slice steps bits mesh:Word w))
    (budget : ((b.nextStock i (b.wire tab)).eval m (j.val:Word w)).val ≤ stock*payload+b.maxWidth*payload)
    (account : ((b.stock i).eval m (j.val:Word w)).val+installed=
      ((b.nextStock i (b.wire tab)).eval m (j.val:Word w)).val+consumed)
    (early : (feed bank stride mesh reserve (b.nextStock i (b.wire tab))).inputEnd≤out)
    (endFit : out+rows+rows<2^w) (capFit : cap<2^w) :
    let total := feed bank stride mesh reserve (b.nextStock i (b.wire tab))
    let final := result (columns out rows cap total) m
    ((b.stock i).eval m (j.val:Word w)).val+installed+AdaptiveProbe.slice steps bits mesh=
      consumed+(final (out+j.val)).val+(final (out+rows+j.val)).val := by
  intro total final
  have bitsRead := feed_exact b i tab bank stride steps mesh bits reserve m (j.val:Word w)
    saved entry room which reserveBound budget
  have rowsRead := (columns_read out rows cap total m j early endFit capFit).2.2
  change (final (out+j.val)).val+(final (out+rows+j.val)).val=(total.eval m (j.val:Word w)).val at rowsRead
  change (total.eval m (j.val:Word w)).val=_ at bitsRead
  omega

end
end Hierarchy.ProtocolRAM.StockAccounts

end OAI
