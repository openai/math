import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Four compact peer slots from the native forward and inverse ranks -/
namespace Hierarchy.DescentRankPortRoster
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentSixParty.Chronology DescentIssuedTerminalId
open scoped Fin.CommRing

structure Inputs where
  count : Bank
  inverse : Bank
  forward : Bank
  current : Bank

def span (H : ℕ) := 2^Nat.clog 2 (4*H)
def roof (base H : ℕ) := base+3*span H
private def host (base H : ℕ) : Bank := ⟨base,Nat.clog 2 (4*H)⟩
private def slot (base H : ℕ) : Bank := ⟨base+span H,Nat.clog 2 (4*H)⟩
def bank (base H : ℕ) : Bank := ⟨base+2*span H,Nat.clog 2 (4*H)⟩

theorem extent (base H : ℕ) : roof base H ≤ base+24*H+3 := by
  have rounded (n : ℕ) : 2^Nat.clog 2 n ≤ 2*n+1 := by
    by_cases small : n≤1
    · interval_cases n <;> decide
    have low := Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have pos := Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
    cases eqn : Nat.clog 2 n with
    | zero => omega
    | succ j => rw [eqn] at low; simp only [Nat.pred_succ] at low; rw [Nat.pow_succ]; omega
  have bnd := rounded (4*H)
  unfold roof span; omega

private def dbl (e : Expr) := Expr.op .add e e
private def hostExpr (base H : ℕ) := Expr.lookup (host base H) .row
private def peerExpr (base H : ℕ) (B : Inputs) :=
  let orig := Expr.lookup B.inverse (hostExpr base H)
  Expr.lookup B.current (.op .add (dbl (dbl orig)) (.lookup (slot base H) .row))

def expr (base H P : ℕ) (B : Inputs) : Expr :=
  let peer := peerExpr base H B
  .branch .lt (hostExpr base H) (.lookup B.count (.lit 0))
    (.branch .lt peer (.lit P) (.lookup B.forward peer) (.lit H)) (.lit H)

set_option maxRecDepth 4096 in
theorem work (base H P : ℕ) (B : Inputs) : (expr base H P B).work=151 := rfl

structure Room (w base H P : ℕ) (B : Inputs) : Prop where
  count : B.count.Fits w base
  inverse : B.inverse.Fits w base
  forward : B.forward.Fits w base
  current : B.current.Fits w base
  forwardSize : P ≤ B.forward.size
  currentSize : 4*P ≤ B.current.size
  limit : roof base H < 2^w

theorem bank_size (base H : ℕ) : 4*H ≤ (bank base H).size :=
  Nat.le_pow_clog (by decide) _

theorem bank_fits {w base H P : ℕ} {B : Inputs} (r : Room w base H P B) :
    (bank base H).Fits w (roof base H) := by
  have limit := r.limit
  change base+3*span H < 2^w at limit
  change 0<span H ∧ span H<2^w ∧ base+2*span H+span H≤base+3*span H
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

private def mounted {w : ℕ} (base H : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image (base+span H) (fun i=>i%4)
    (DescentStaticWordColumn.image base (fun i=>i/4) m (4*H)) (4*H)

def image {w : ℕ} (base H P : ℕ) (B : Inputs) (m : Memory w) :=
  ProtocolRAM.image (bank base H).base (4*H) (expr base H P B) (mounted base H m)

def program (w base H P : ℕ) (B : Inputs) :=
  ((DescentStaticWordColumn.program w base (fun i=>i/4) (4*H)).seq
    (DescentStaticWordColumn.program w (base+span H) (fun i=>i%4) (4*H))).seq
    (scan w (bank base H).base (4*H) (expr base H P B))

def ticks (H : ℕ) := 12+326*(4*H)

def phase (w base H P : ℕ) (B : Inputs) : NativePhase w :=
  ⟨program w base H P B,ticks H,image base H P B,
    by
      intro coeffPC coeffReg coeffSlot pc reg pub exit i
      exact cheap_seq (cheap_seq (DescentStaticWordColumn.cheap w base (fun t=>t/4) (4*H))
        (DescentStaticWordColumn.cheap w (base+span H) (fun t=>t%4) (4*H)))
        (scan_cheap w (bank base H).base (4*H) (expr base H P B)) pc reg pub exit i⟩

theorem price (w base H P : ℕ) (B : Inputs) :
    (phase w base H P B).ticks+7*DescentStaticWordColumn.names (phase w base H P B).program ≤ 5000*(H+1) := by
  change ticks H+7*DescentStaticWordColumn.names (program w base H P B) ≤ _
  rw [program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_seq,
    DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_mount,
    DescentStaticWordColumn.names_scan,work,ticks]
  omega

variable {w base H P : ℕ} {B : Inputs}

private theorem slots_fit (r : Room w base H P B) :
    (expr base H P B).Fits w (bank base H).base := by
  have before : base ≤ (bank base H).base := Nat.le_add_right _ _
  have fits (b : Bank) (hb : b.Fits w base) : b.Fits w (bank base H).base :=
    ⟨hb.1,hb.2.1,hb.2.2.trans before⟩
  have limit := r.limit
  change base+3*span H < 2^w at limit
  have hostFit : (host base H).Fits w (bank base H).base := by
    change 0<span H ∧ span H<2^w ∧ base+span H ≤ base+2*span H
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have slotFit : (slot base H).Fits w (bank base H).base := by
    change 0<span H ∧ span H<2^w ∧ base+span H+span H ≤ base+2*span H
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  simp only [expr,hostExpr,peerExpr,dbl,Expr.Fits,hostFit,slotFit,fits _ r.inverse,
    fits _ r.count,fits _ r.current,fits _ r.forward,and_self]

private theorem mounted_frame (m : Memory w) (a : ℕ) (outside : a<base ∨ roof base H≤a) :
    mounted base H m a=m a := by
  have fits : 4*H ≤ span H := Nat.le_pow_clog (by decide) _
  unfold roof at outside
  exact (DescentStaticWordColumn.frame _ _ _ _ a (by omega)).trans
    (DescentStaticWordColumn.frame _ _ _ _ a (by omega))

theorem any (r : Room w base H P B) (m : Memory w) :
    (phase w base H P B).Runs m ∧
    ∀ a, a<base ∨ roof base H≤a → image base H P B m a=m a := by
  have fits : 4*H ≤ span H := Nat.le_pow_clog (by decide) _
  have limit := r.limit
  change base+3*span H < 2^w at limit
  constructor
  · change (program w base H P B).Exec m (image base H P B m) (ticks H)
    have budget : ticks H = ((4+10*(4*H))+(4+10*(4*H)))+
        (4+(4*H)*(2*(expr base H P B).work+4)) := by rw [work,ticks]; omega
    rw [budget]
    intro targetPC targetReg targetSlots machine
    exact Procedure.Exec.then (Procedure.Exec.then
      (DescentStaticWordColumn.mount _ _ _ _ (by omega))
      (DescentStaticWordColumn.mount _ _ _ _ (by omega)))
      (scan_exec _ _ _ _ (slots_fit r) (by change base+2*span H+4*H<2^w; omega)) machine
  · intro a outside
    refine (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a ?_).trans (mounted_frame m a outside)
    change a<base+2*span H ∨ base+2*span H+4*H≤a
    unfold roof at outside
    omega

/-- The exterior array is host-major. A vacant slot and a padded compact host
both receive the sentinel H. -/
def reported (H P : ℕ) (B : Inputs) (m : Memory w) (i j : ℕ) : Word w :=
  let old := (m (B.inverse.base+i)).val
  let peer := m (B.current.base+(4*old+j))
  if i < (m B.count.base).val then
    if peer.val < P then m (B.forward.base+peer.val) else (H : Word w)
  else (H : Word w)

theorem read (r : Room w base H P B) (m : Memory w) (i : Fin H) (j : Fin 4)
    (liveIndex : i.val < (m B.count.base).val → i.val < B.inverse.size)
    (valid : i.val < (m B.count.base).val → (m (B.inverse.base+i.val)).val < P) :
    image base H P B m ((bank base H).base+(4*i.val+j.val)) =
      reported H P B m i.val j.val := by
  let n := 4*i.val+j.val
  have ni : n<4*H := by have := i.isLt; have := j.isLt; dsimp only [n]; omega
  have sz : 4*H ≤ span H := Nat.le_pow_clog (by decide) _
  have lower : span H<2^w := by have hh:=r.limit; unfold roof at hh; omega
  let src := mounted base H m
  let row : Word w := n
  have source (b : Bank) (fit : b.Fits w base) (a : ℕ) (ha : a<b.size) :
      src (b.base+a)=m (b.base+a) := by
    exact mounted_frame m _ (.inl ((Nat.add_lt_add_left ha _).trans_le fit.2.2))
  have hh : (hostExpr base H).eval src row=(i.val:Word w) := by
    refine (lookup_nat (host base H) src row .row n rfl (ni.trans_le sz) lower).trans ?_
    change mounted base H m (base+n)=_
    refine (DescentStaticWordColumn.frame _ _ _ _ _ (.inl (by omega))).trans ?_
    have h := DescentStaticWordColumn.read base (4*H) (fun t=>t/4) m ni
    have hv : n/4=i.val := by dsimp [n]; have := j.isLt; omega
    simpa only [hv] using h
  have sj : (Expr.lookup (slot base H) .row).eval src row=(j.val:Word w) := by
    refine (lookup_nat (slot base H) src row .row n rfl (ni.trans_le sz) lower).trans ?_
    have h := DescentStaticWordColumn.read (base+span H) (4*H) (fun t=>t%4)
      (DescentStaticWordColumn.image base (fun t=>t/4) m (4*H)) ni
    have hv : n%4=j.val := by dsimp [n]; have := j.isLt; omega
    change DescentStaticWordColumn.image (base+span H) (fun t=>t%4)
      (DescentStaticWordColumn.image base (fun t=>t/4) m (4*H)) (4*H)
      (base+span H+n)=(j.val : Word w)
    rw [←hv]
    exact h
  have countAt : (Expr.lookup B.count (.lit 0)).eval src row=m B.count.base := by
    have cap := r.count.1
    simpa only [Nat.add_zero] using (lookup_nat B.count src row (.lit 0) 0 rfl cap r.count.2.1).trans
      (source B.count r.count 0 cap)
  have outer : ((i.val:Word w) < m B.count.base) ↔ i.val < (m B.count.base).val := by
    change ((i.val : Word w)).val < _ ↔ _
    rw [Fin.val_cast_of_lt (by have hi:=i.isLt; omega)]
  refine (ProtocolRAMGeneratedWrite.read_image _ _ _ src (⟨n,ni⟩ : Fin (4*H))).trans ?_
  change (if decide ((hostExpr base H).eval src row < (Expr.lookup B.count (.lit 0)).eval src row) then
    (if decide ((peerExpr base H B).eval src row < (P:Word w)) then
      (Expr.lookup B.forward (peerExpr base H B)).eval src row else (H:Word w)) else (H:Word w))=_
  rw [hh,countAt]
  simp only [reported,decide_eq_true_eq,outer]
  by_cases live : i.val < (m B.count.base).val
  · simp only [ite_eq_left live]
    let old := (m (B.inverse.base+i.val)).val
    let a := 4*old+j.val
    let peer := m (B.current.base+a)
    have oldLt : old < P := valid live
    have aLt : a < B.current.size := by
      have all := r.currentSize
      have right := j.isLt
      dsimp only [a]; omega
    have inv : (Expr.lookup B.inverse (hostExpr base H)).eval src row=(old : Word w) := by
      let h := (lookup_nat B.inverse src row _ i.val hh (liveIndex live) r.inverse.2.1).trans
        (source B.inverse r.inverse _ (liveIndex live))
      exact h.trans (Fin.cast_val_eq_self _).symm
    have loc : (Expr.op .add (dbl (dbl (.lookup B.inverse (hostExpr base H))))
        (.lookup (slot base H) .row)).eval src row=(a : Word w) := by
      let t := (Expr.lookup B.inverse (hostExpr base H)).eval src row
      change (t+t)+(t+t)+(Expr.lookup (slot base H) .row).eval src row=(a:Word w)
      dsimp only [t,a]
      rw [inv,sj]
      push_cast
      ring
    have peerAt : (peerExpr base H B).eval src row=peer :=
      (lookup_nat B.current src row _ a loc aLt r.current.2.1).trans (source _ r.current _ aLt)
    rw [peerAt]
    have same : (peer < (P:Word w)) ↔ peer.val<P := by
      change _ < ((P:Word w)).val ↔ _
      rw [Fin.val_cast_of_lt (r.forwardSize.trans_lt r.forward.2.1)]
    rw [show (m (B.current.base+(4*(m (B.inverse.base+i.val)).val+j.val))) = peer from rfl]
    simp only [same]
    by_cases found : peer.val<P
    · simp only [ite_eq_left found]
      have hs := found.trans_le r.forwardSize
      exact (lookup_nat B.forward src row _ peer.val (peerAt.trans (Fin.cast_val_eq_self _).symm)
        hs r.forward.2.1).trans (source _ r.forward _ hs)
    · simp only [ite_eq_right found]
  · simp only [ite_eq_right live]

end Hierarchy.DescentRankPortRoster

end OAI
