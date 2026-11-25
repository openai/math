import OAI.Hierarchy.DescentResetActorDirectoryCode
import OAI.Hierarchy.ProtocolRAMEndpointPrefixCheap

namespace OAI
/-! # Total actor compaction on every numerical input image -/
namespace Hierarchy.DescentResetNewActorDirectory.Layout
open DescentSIMDLookup DescentPackedZip DescentActorRaster ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

private theorem poll_binary (roots src : Bank) (m : Memory w) (j : Word w) (K : ℕ) :
    (Flags.poll roots src K).eval m j=0 ∨ (Flags.poll roots src K).eval m j=1 := by
  induction K with
  | zero=>exact Or.inl rfl
  | succ k ih=>
    let addr : Expr:=.lookup src (.op .add (.lookup roots .row) (.lit k))
    change (if Comparison.eq.test (addr.eval m j) (0:Word w) then (Flags.poll roots src k).eval m j else 1)=0 ∨
      (if Comparison.eq.test (addr.eval m j) (0:Word w) then (Flags.poll roots src k).eval m j else 1)=1
    by_cases test : Comparison.eq.test (addr.eval m j) (0:Word w)
    · simpa only [ite_eq_left test] using ih
    · exact Or.inr (ite_eq_right test)

private def before (bit : ℕ→ℕ) : ℕ→ℕ
  | 0=>0
  | j+1=>before bit j+bit j

private theorem before_le (bit : ℕ→ℕ) (binary : ∀k,bit k≤1) (j : ℕ) : before bit j≤j := by
  induction j with
  | zero=>rfl
  | succ j ih=>exact Nat.add_le_add ih (binary _)

theorem cheap (L : Layout) (w : ℕ) (src : Bank) : CheapCode (L.program w src) :=
  cheap_seq (DescentStaticWordColumn.cheap w L.first L.rootLiteral L.sites) (cheap_seq
    (cheap_seq (scan_cheap w L.flags.base L.sites (Flags.poll L.roots src L.preChunks))
      (ProtocolRAMRankCheap.exclusive_cheap w L.flags.base L.ranks.base L.sites))
    (ProtocolRAMRankCheap.generated w L.scratch L.values L.sites
      (Inverse.address L.flags L.ranks L.inverse.base L.sites) .row))

def result (L : Layout) (src : Bank) (m : Memory w) : Memory w :=
  let rom:=DescentStaticWordColumn.image L.first L.rootLiteral m L.sites
  let e:=Flags.poll L.roots src L.preChunks
  let flags:=ProtocolRAM.image L.flags.base L.sites e rom
  let digit (i : ℕ) : ℕ:=if e.eval rom (i:Word w)=0 then 0 else 1
  let pref:=before digit
  let ranks:=ProtocolRAMEndpointPrefix.image L.ranks.base pref flags L.sites
  let dest (j : Fin L.sites):=if digit j.val=0 then L.inverse.base+L.sites+j.val else L.inverse.base+pref j.val
  ProtocolRAMGeneratedWrite.image L.scratch L.values (Inverse.address L.flags L.ranks L.inverse.base L.sites)
    .row dest (fun j : Fin L.sites=>(j.val:Word w)) ranks

/-- The flag gate returns a bit on arbitrary source memory. Therefore all
prefixes are in range and each native scatter target stays in its two output
banks even when the preceding actor words have no structural interpretation. -/
theorem evaluate_full (L : Layout) (src : Bank) (m : Memory w) (srcFits : src.Fits w L.first)
    (parts : L.preChunks≤2^w) (room : L.endAddress<2^w) :
    (L.program w src).Exec m (L.result src m) (L.ticks src) ∧ CheapCode (L.program w src) ∧
      (∀a,a < L.flags.base → L.result src m a=DescentStaticWordColumn.image L.first L.rootLiteral m L.sites a) ∧
      ∀a,a < L.first ∨ L.endAddress ≤ a → L.result src m a=m a := by
  obtain ⟨sites,start,flagEnd,rankEnd,mid,last,inverseEnd,_⟩:=L.ordered
  obtain ⟨roots,flags,ranks,_,_⟩:=L.fits room
  have layout : L.first≤L.flags.base ∧ L.flags.base≤L.ranks.base ∧ L.ranks.base≤L.scratch ∧ L.scratch≤L.values ∧
      L.values≤L.inverse.base ∧ L.inverse.base≤L.endAddress := by
    dsimp [Layout.flags,Layout.ranks,Layout.scratch,Layout.values,Layout.inverse,Layout.endAddress,Layout.size]
    omega
  have one : 1<2^w:=by
    change L.first+(4*L.pitch+1+4*L.sites)<2^w at room
    have pos : 0<L.pitch:=Nat.two_pow_pos _
    omega
  let rom:=DescentStaticWordColumn.image L.first L.rootLiteral m L.sites
  have setup : (L.table w).Exec m rom (4+10*L.sites):=
    DescentStaticWordColumn.mount _ _ _ _ (by omega)
  let e:=Flags.poll L.roots src L.preChunks
  have srcF : src.Fits w L.flags.base:=⟨srcFits.1,srcFits.2.1,srcFits.2.2.trans layout.1⟩
  let measured:=ProtocolRAM.image L.flags.base L.sites e rom
  have scanRun : (L.scan w src).Exec rom measured (4+L.sites*(2*e.work+4)):=
    scan_exec _ _ e rom (Flags.fits _ _ _ roots srcF one _ parts) (by omega)
  let digit (i : ℕ) : ℕ:=if e.eval rom (i:Word w)=0 then 0 else 1
  have binary (i : ℕ) : digit i≤1:=by unfold digit;split <;> decide
  have truth (j : Fin L.sites) : measured (L.flags.base+j.val)=(digit j.val:Word w):=by
    rw [show measured (L.flags.base+j.val)=e.eval rom (j.val:Word w) from ProtocolRAMGeneratedWrite.read_image ..]
    rcases poll_binary L.roots src rom (j.val:Word w) L.preChunks with zero|one'
    · change e.eval rom _=0 at zero;simp [digit,zero]
    · change e.eval rom _=1 at one'
      have distinct : (1:Word w)≠0:=by
        intro eq
        have bad:=congrArg Fin.val eq
        change 1%(2^w)=0 at bad
        rw [Nat.mod_eq_of_lt one] at bad
        exact Nat.one_ne_zero bad
      simp [digit,one',distinct]
  let pref:=before digit
  let counted:=ProtocolRAMEndpointPrefix.image L.ranks.base pref measured L.sites
  have prefixes : (L.prefixCode w).Exec measured counted (10+(3+12*L.sites)) :=
    ProtocolRAMEndpointPrefix.run _ _ _ pref measured flagEnd (by omega) rfl (fun j hj=>by
      rw [truth ⟨j,hj⟩];exact Nat.cast_add _ _)
  have keepFlag (j : Fin L.sites) : counted (L.flags.base+j.val)=(digit j.val:Word w):=
    (ProtocolRAMEndpointPrefix.frame _ _ _ _ _ (.inl (by have:=j.isLt;omega))).trans (truth j)
  let dest (j : Fin L.sites):=if digit j.val=0 then L.inverse.base+L.sites+j.val else L.inverse.base+pref j.val
  let value (j : Fin L.sites):=(j.val:Word w)
  have span (j : Fin L.sites) : L.inverse.base≤dest j ∧ dest j<L.inverse.base+2*L.sites:=by
    have h:=before_le digit binary j.val
    change pref j.val≤j.val at h
    have jh:=j.isLt
    unfold dest
    split <;> omega
  have slots (j : Fin L.sites) :
      (Inverse.address L.flags L.ranks L.inverse.base L.sites).eval counted (j.val:Word w)=(dest j:Word w):=by
    have flagWord:=bank_read L.flags counted (j.isLt.trans_le sites) flags
    have posWord:=bank_read L.ranks counted (j.isLt.trans_le sites) ranks
    have rankWord : counted (L.ranks.base+j.val)=(pref j.val:Word w):=
      ProtocolRAMEndpointPrefix.read L.ranks.base pref measured L.sites j.val j.isLt.le
    have fitsDigit : digit j.val<2^w:=(binary _).trans_lt one
    have zeroIff : ((digit j.val:Word w)=0) ↔ digit j.val=0 := by
      constructor
      · intro h
        have hn:=congrArg Fin.val h
        change digit j.val%(2^w)=0 at hn
        rwa [Nat.mod_eq_of_lt fitsDigit] at hn
      · intro h
        simp [h]
    simp only [Inverse.address,Expr.eval,flagWord,posWord,keepFlag,rankWord,Comparison.test,
      Nat.cast_zero,beq_iff_eq,zeroIff,dest,RowOp.opcode,BinaryOp.eval]
    by_cases zero : digit j.val=0 <;> simp [zero,Nat.cast_add]
  let address:=Inverse.address L.flags L.ranks L.inverse.base L.sites
  let out:=ProtocolRAMGeneratedWrite.image L.scratch L.values address .row dest value counted
  have scatter : (L.inverted w).Exec counted out (ProtocolRAMGeneratedWrite.work L.sites address .row) := by
    refine ProtocolRAMGeneratedWrite.run L.scratch L.values address .row dest value counted
      ?_ trivial mid (by omega) slots (fun _=>rfl) (fun j=>(span j).2.trans (inverseEnd.trans_lt room)) ?_ ?_
    · simp [address,Inverse.address,Expr.Fits,flags,ranks]
    · intro i j;have:=i.isLt;have:=span j;omega
    · intro i j;have:=i.isLt;have:=span j;omega
  have tail (a : ℕ) (away : a < L.flags.base ∨ L.endAddress ≤ a) : out a=rom a := by
    have no (j : Fin L.sites) : a≠dest j:=by have:=span j; rcases away with h|h <;> omega
    refine (ProtocolRAMGeneratedWrite.frame L.scratch L.values address .row dest value counted a no
      (by rcases away with h|h <;> omega) (by rcases away with h|h <;> omega)).trans ?_
    refine (ProtocolRAMEndpointPrefix.frame L.ranks.base pref measured L.sites a
      (by rcases away with h|h <;> omega)).trans ?_
    exact ProtocolRAMGeneratedWrite.frame_image L.flags.base L.sites e rom a (by rcases away with h|h <;> omega)
  have first : ((L.scan w src).seq (L.prefixCode w)).Exec rom counted
      ((4+L.sites*(2*e.work+4))+(10+(3+12*L.sites))) := Procedure.Exec.then scanRun prefixes
  have later : (((L.scan w src).seq (L.prefixCode w)).seq (L.inverted w)).Exec rom out
      (((4+L.sites*(2*e.work+4))+(10+(3+12*L.sites)))+ProtocolRAMGeneratedWrite.work L.sites address .row) :=
    Procedure.Exec.then first scatter
  refine ⟨Procedure.Exec.then setup later,L.cheap w src,fun a h=>tail a (.inl h),?_⟩
  intro a away
  have kept:=tail a (away.imp (fun h=>h.trans_le layout.1) id)
  exact kept.trans (DescentStaticWordColumn.frame L.first L.sites L.rootLiteral m a
    (away.imp id (fun h=>(start.trans (layout.2.1.trans (layout.2.2.1.trans
      (layout.2.2.2.1.trans (layout.2.2.2.2.1.trans layout.2.2.2.2.2))))).trans h)))

theorem evaluate (L : Layout) (src : Bank) (m : Memory w) (srcFits : src.Fits w L.first)
    (parts : L.preChunks≤2^w) (room : L.endAddress<2^w) :
    (L.program w src).Exec m (L.result src m) (L.ticks src) ∧ CheapCode (L.program w src) ∧
      ∀a,a < L.first ∨ L.endAddress ≤ a → L.result src m a=m a := by
  obtain ⟨go,cheap,_,frame⟩:=L.evaluate_full src m srcFits parts room
  exact ⟨go,cheap,frame⟩

theorem result_roots (L : Layout) (src : Bank) (m : Memory w) (srcFits : src.Fits w L.first)
    (parts : L.preChunks≤2^w) (room : L.endAddress<2^w) (j : Fin L.sites) :
    L.result src m (L.roots.base+j.val)=(L.rootLiteral j.val:Word w) := by
  have live : L.first+j.val < L.flags.base:=(Nat.add_lt_add_left j.isLt _).trans_le L.ordered.2.1
  exact ((L.evaluate_full src m srcFits parts room).2.2.1 _ live).trans
    (DescentStaticWordColumn.read _ _ _ _ j.isLt)

theorem any (L : Layout) (src : Bank) (m : Memory w) (srcFits : src.Fits w L.first)
    (parts : L.preChunks≤2^w) (room : L.endAddress<2^w) :
    ∃out,(L.program w src).Exec m out (L.ticks src) ∧ CheapCode (L.program w src) ∧
      ∀a,a < L.first ∨ L.endAddress ≤ a → out a=m a :=
  ⟨L.result src m,L.evaluate src m srcFits parts room⟩

end
end Hierarchy.DescentResetNewActorDirectory.Layout

end OAI
