import OAI.Hierarchy.DescentSortedRoster
import OAI.Hierarchy.DescentHaloWalkRAM
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Did a walk from a sorted donor return to this receiver? -/
namespace Hierarchy.DescentScalarVenueDirectory
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H P w : ℕ}
abbrev Row (H P : ℕ) := Fin H×Fin P

def number (x : Option (Fin H)) :=x.elim H Fin.val

def hit (walks : Fin H→Fin P→Option (Fin H)) (s : Fin P) (h : Fin H) (p : Fin P) : Bool :=
  match DescentSortedRoster.indexed walks h s with
  | some donor=>decide (walks donor p=some h)
  | none=>false

structure Chart where
  sorted : Bank
  ends : Bank
  host : Bank
  path : Bank
  offsets : Bank

def donor (C : Chart) (s : Fin P) : Expr:=.lookup C.sorted (.op .add (.lookup C.offsets (.lookup C.host .row)) (.lit s.val))

def expression (C : Chart) (H : ℕ) (s : Fin P) : Expr:=
  let h:=Expr.lookup C.host .row;let src:=donor C s
  .branch .eq src (.lit H) (.lit 0)
    (.branch .eq (.lookup C.ends (.op .add (.lookup C.offsets src) (.lookup C.path .row))) h (.lit 1) (.lit 0))

def origin (base H P s : ℕ) :=base+s*(H*P)
def passes (C : Chart) (base H P : ℕ) :=ProbeStage.Native.columns (H*P) base (List.ofFn (expression C H : Fin P→Expr))

structure Room (C : Chart) (base H P w : ℕ) : Prop where
  sorted : C.sorted.Fits w base
  ends : C.ends.Fits w base
  host : C.host.Fits w base
  path : C.path.Fits w base
  offset : C.offsets.Fits w base
  rankSize : H*P≤C.sorted.size
  endSize : H*P≤C.ends.size
  hostRows : H*P≤C.host.size
  pathRows : H*P≤C.path.size
  offsetRows : H≤C.offsets.size
  sentinel : H<2^w
  final : base+P*(H*P)<2^w

structure Read (C : Chart) (walks : Fin H→Fin P→Option (Fin H)) (m : Memory w) : Prop where
  sorted : ∀h s,m (C.sorted.base+(h.val*P+s.val))=(number (DescentSortedRoster.indexed walks h s):Word w)
  ends : ∀h p,m (C.ends.base+(h.val*P+p.val))=(number (walks h p):Word w)
  host : ∀(h:Fin H)(p:Fin P),m (C.host.base+(finProdFinEquiv (h,p)).val)=(h.val:Word w)
  path : ∀(h:Fin H)(p:Fin P),m (C.path.base+(finProdFinEquiv (h,p)).val)=(p.val:Word w)
  offsets : ∀h:Fin H,m (C.offsets.base+h.val)=((h.val*P:ℕ):Word w)

private theorem within (h : Fin H) (p : Fin P) : h.val*P+p.val<H*P :=(Nat.add_lt_add_left p.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)

theorem word (C : Chart) (base : ℕ) (s : Room C base H P w) (m : Memory w) (walks : Fin H→Fin P→Option (Fin H)) (r : Read C walks m)
    (u : Fin P) (h : Fin H) (p : Fin P) : (expression C H u).eval m ((finProdFinEquiv (h,p)).val:Word w)=((hit walks u h p).toNat:Word w) :=by
  let i:=finProdFinEquiv (h,p)
  have src : (donor C u).eval m (i.val:Word w)=(number (DescentSortedRoster.indexed walks h u):Word w):=by
    change C.sorted.read m (C.offsets.read m (C.host.read m (i.val:Word w))+(u.val:Word w))=_
    rw [bank_read _ _ (i.isLt.trans_le s.hostRows) s.host,r.host,bank_read _ _ (h.isLt.trans_le s.offsetRows) s.offset,r.offsets,
      ←Nat.cast_add,bank_read _ _ ((within h u).trans_le s.rankSize) s.sorted,r.sorted]
  have eq_ {a b : ℕ} (ra:a<2^w) (rb:b<2^w) : (a:Word w)=(b:Word w) ↔ a=b:=by rw [Fin.ext_iff,Fin.val_cast_of_lt ra,Fin.val_cast_of_lt rb]
  have host : C.host.read m (i.val : Word w) = (h.val : Word w) := by
    rw [bank_read _ _ (i.isLt.trans_le s.hostRows) s.host, r.host]
  have endpoint (x : Fin H) :
      C.ends.read m (C.offsets.read m (x.val : Word w) + C.path.read m (i.val : Word w)) =
        (number (walks x p) : Word w) := by
    rw [bank_read _ _ (x.isLt.trans_le s.offsetRows) s.offset, r.offsets,
      bank_read _ _ (i.isLt.trans_le s.pathRows) s.path, r.path, ←Nat.cast_add,
      bank_read _ _ ((within x p).trans_le s.endSize) s.ends, r.ends]
  let follow (a : Word w) := C.ends.read m (C.offsets.read m a + C.path.read m (i.val : Word w))
  let response (a b receiver : Word w) : Word w :=
    if (a == (H : Word w)) = true then 0 else if (b == receiver) = true then 1 else 0
  let d := (donor C u).eval m (i.val : Word w)
  change response d (follow d) (C.host.read m (i.val : Word w)) = _
  have source : d = (number (DescentSortedRoster.indexed walks h u) : Word w) := src
  rw [source, host]
  cases old : DescentSortedRoster.indexed walks h u with
  | none =>
    change response (H : Word w) (follow (H : Word w)) (h.val : Word w) = _
    simp [response, hit, old]
  | some x =>
    change response (x.val : Word w) (follow (x.val : Word w)) (h.val : Word w) = _
    have reached : follow (x.val : Word w) = (number (walks x p) : Word w) := endpoint x
    rw [reached]
    have live : (x.val : Word w) ≠ (H : Word w) :=
      fun same => x.isLt.ne ((eq_ (x.isLt.trans s.sentinel) s.sentinel).mp same)
    cases gone : walks x p with
    | none =>
      change response (x.val : Word w) (H : Word w) (h.val : Word w) = _
      have absent : (H : Word w) ≠ (h.val : Word w) :=
        fun same => h.isLt.ne' ((eq_ s.sentinel (h.isLt.trans s.sentinel)).mp same)
      simp [response, beq_iff_eq, live, absent, hit, old, gone]
    | some y =>
      change response (x.val : Word w) (y.val : Word w) (h.val : Word w) = _
      by_cases back : y = h
      · subst y
        simp [response, beq_iff_eq, live, hit, old, gone]
      · have different : (y.val : Word w) ≠ (h.val : Word w) :=
          fun same => back (Fin.ext ((eq_ (y.isLt.trans s.sentinel) (h.isLt.trans s.sentinel)).mp same))
        simp [response, beq_iff_eq, live, different, hit, old, gone, back]

theorem fitted (C : Chart) (base : ℕ) (s : Room C base H P w) (u : Fin P) : (expression C H u).Fits w base:=by
  simp [expression,donor,Expr.Fits,s.sorted,s.ends,s.offset,s.host,s.path]

theorem emit (C : Chart) (base : ℕ) (s : Room C base H P w) (m : Memory w) (walks : Fin H→Fin P→Option (Fin H)) (r : Read C walks m) :
    let ps:=passes C base H P;let o:=result ps m
    (program w ps).Exec m o (clock ps) ∧ (∀u h p,o (origin base H P u.val+(h.val*P+p.val))=((hit walks u h p).toNat:Word w)) ∧
    (∀a,a<base ∨ base+P*(H*P)≤a → o a=m a) ∧ CheapCode (program w ps) :=by
  intro ps o;let terms:=List.ofFn (expression C H : Fin P→Expr)
  have fit:∀e∈terms,e.Fits w base:=by intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact fitted C base s j
  refine ⟨ProbeStage.Native.columns_exec terms m (ProbeStage.Native.columns_safe terms le_rfl fit (by simpa [terms] using s.final)),?_,?_,@ProtocolRAM.program_cheap _ _⟩
  · intro u h p
    have stored:=ProbeStage.Native.columns_read terms m le_rfl fit u.val (by simp [terms]) (finProdFinEquiv (h,p))
    have eqn:(finProdFinEquiv (h,p)).val=h.val*P+p.val:=by simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
    simp only [terms, List.getElem_ofFn] at stored
    simpa only [o, ps, passes, origin, eqn] using stored.trans (word C base s m walks r u h p)
  · intro a outside;apply ProbeStage.Native.columns_frame;simpa [terms] using outside

end
end Hierarchy.DescentScalarVenueDirectory

end OAI
