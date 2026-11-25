import OAI.Hierarchy.DescentPeerRankFits
import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentResetTrunkIssue
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProtocolRAMRowChoiceFits

namespace OAI
/-! # Build the one trunk descriptor per original host from the written neighbor list -/
namespace Hierarchy.DescentResetTrunkScalar
open DescentPackedColony DescentFallbackLeafScan DescentSIMDLookup DescentResetFieldAssembler DescentSortedRoster DescentFallbackRankRAM
open DescentColonies.SplitRAM DescentResetSourceClassRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {b w H : ℕ}

def peers (r : Fin H→Fin 3→Option (Fin H)) (h : Fin H) : Fin 4→Option (Fin H):=Fin.cons (some h) (r h)
def full (src : Fin 3→Expr) : Fin 4→Expr:=Fin.cons .row src
def «omit» (src : Fin 3→Expr) : Expr:=unlessSeen .row (.lit 1) (List.ofFn src)

def integer (peer : Fin H→Fin 3→Option (Fin H)) (h : Fin H) (arg : Option (Fin H×Fin H×Bool)) : Meta:=
  match arg with
  | none=>.blank
  | some (left,right,core)=>⟨true,before (peers peer) h left,before (peers peer) h right,
      before (peers peer) h h,decide (h∉present peer h),core,0⟩

def shifted (b : ℕ) (j : Fin 7) (e : Expr) : Expr:=
  chooseField 5 0 (fun k=>.lit (k.val*(2^b)^j.val)) e

def values (src : Fin 3→Expr) (left right core : Expr) : Fin 7→Expr:=
  ![.lit 1,calculate (full src) left,calculate (full src) right,calculate (full src) .row,«omit» src,core,.lit 0]
def header (b H : ℕ) (src : Fin 3→Expr) (left right core : Expr) : Expr:=
  .branch .lt left (.lit H)
    (total (fun j=>shifted b j (values src left right core j)) (List.finRange 7)) (.lit 0)

theorem present_peers (peer : Fin H→Fin 3→Option (Fin H)) (h : Fin H) :
    present (peers peer) h=insert h (present peer h):= by
  ext z
  simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨j,field⟩
    cases j using Fin.cases with
    | zero=>exact Or.inl (Option.some.inj field).symm
    | succ j=>exact Or.inr ⟨j,field⟩
  · rintro (rfl|⟨j,hit⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨j.succ,hit⟩

theorem score_bound (peer : Fin H→Fin 3→Option (Fin H)) (h z : Fin H) :
    before (peers peer) h z<5:=by
  rw [←order_count]
  have b:=Finset.card_le_univ (Finset.univ.filter (fun i : Fin 4=>keep (peers peer) h z i=true))
  simpa only [Fintype.card_fin] using Nat.lt_succ_of_le b

theorem omitted (peer : Fin H→Fin 3→Option (Fin H)) (h : Fin H) (src : Fin 3→Expr) (m : Memory w)
    (small : H<2^w) (old : ∀i,(src i).eval m (h.val:Word w)=(target (peer h i):Word w)) :
    («omit» src).eval m (h.val:Word w)=((decide (h∉present peer h)).toNat:Word w):=by
  have eqn (j : Fin 3) : (src j).eval m (h.val:Word w)=(h.val:Word w) ↔ peer h j=some h:=by
    rw [old j]
    cases opt : peer h j with
    | none=>
      change ((H:Word w)=(h.val:Word w)) ↔ none=some h
      rw [show (none:Option (Fin H))=some h ↔ False by simp]
      simpa only [Fin.ext_iff,Fin.val_cast_of_lt small,Fin.val_cast_of_lt (h.isLt.trans small),iff_false]
        using (show H≠h.val from (Nat.ne_of_gt h.isLt))
    | some z=>
      change ((z.val:Word w)=(h.val:Word w)) ↔ some z=some h
      simp [Fin.ext_iff,Fin.val_cast_of_lt (z.isLt.trans small),Fin.val_cast_of_lt (h.isLt.trans small)]
  rw [«omit»,unlessSeen_eval]
  have equivalence : (∃x∈List.ofFn src,x.eval m (h.val:Word w)=(.row : Expr).eval m (h.val:Word w)) ↔
      h∈present peer h:=by
    simp only [List.mem_ofFn,present,Finset.mem_filter,Finset.mem_univ,true_and,Expr.eval]
    constructor
    · rintro ⟨x,⟨j,rfl⟩,hit⟩;exact ⟨j,(eqn j).1 hit⟩
    · rintro ⟨j,hit⟩;exact ⟨_,⟨j,rfl⟩,(eqn j).2 hit⟩
  by_cases hit : h∈present peer h
  · rw [ite_eq_left (equivalence.mpr hit)]
    simp [hit]
  · rw [ite_eq_right (fun seen => hit (equivalence.mp seen))]
    simp [hit,Expr.eval]

theorem read (b : ℕ) (peer : Fin H→Fin 3→Option (Fin H)) (arg : Fin H→Option (Fin H×Fin H×Bool))
    (h : Fin H) (src : Fin 3→Expr) (left right core : Expr) (m : Memory w)
    (small : H<2^w) (wide : 5≤2^w) (fit : 5≤2^b)
    (old : ∀j,(src j).eval m (h.val:Word w)=(target (peer h j):Word w))
    (first : left.eval m (h.val:Word w)=((arg h).elim H (fun p=>p.1.val):Word w))
    (last : right.eval m (h.val:Word w)=((arg h).elim H (fun p=>p.2.1.val):Word w))
    (mark : core.eval m (h.val:Word w)=((arg h).elim 0 (fun p=>p.2.2.toNat):Word w)) :
    (header b H src left right core).eval m (h.val:Word w)=((raw b (integer peer h (arg h))).val:Word w) := by
  cases argAt : arg h with
  | none=>
    rw [argAt] at first
    simp [header,Expr.eval,Comparison.test,first,integer,DescentResetTrunkIssue.zero_raw]
  | some p=>
    obtain ⟨l,r,c⟩:=p
    rw [argAt] at first last mark
    have hit : left.eval m (h.val:Word w)<(H:Word w):=by rw [first]; simp [Fin.lt_def,Fin.val_cast_of_lt small,Fin.val_cast_of_lt (l.isLt.trans small)]
    have fs (j : Fin 4) : (full src j).eval m (h.val:Word w)=(target (peers peer h j):Word w):=by
      cases j using Fin.cases with
      | zero=>rfl
      | succ j=>exact old j
    let A:=integer peer h (some (l,r,c))
    have law (j : Fin 7) : (values src left right core j).eval m (h.val:Word w)=(digits A j:Word w):=by
      have fourth:=omitted peer h src m small old
      have ranked (op : Expr) (z : Fin H) (read : op.eval m (h.val:Word w)=(z.val:Word w)) :=
        rank_read (peers peer) m (h.val:Word w) (full src) h small fs op z
          (by rw [read,Fin.val_cast_of_lt (z.isLt.trans small)])
      fin_cases j <;> first | rfl | exact ranked _ _ first | exact ranked _ _ last | exact ranked _ h rfl | exact fourth | exact mark
    have little (j : Fin 7) : digits A j<5:=by
      have bit (x : Bool) : x.toNat < 5 := by cases x <;> decide
      fin_cases j
      · change 1 < 5
        decide
      · exact score_bound peer h l
      · exact score_bound peer h r
      · exact score_bound peer h h
      · exact bit (decide (h∉present peer h))
      · exact bit c
      · change 0 < 5
        decide
    have limb (j : Fin 7) : (shifted b j (values src left right core j)).eval m (h.val:Word w)=
        (digits A j*(2^b)^j.val:ℕ) := by
      have whereAt : ((values src left right core j).eval m (h.val:Word w)).val=0+digits A j:=by rw [law,Fin.val_cast_of_lt ((little j).trans_le wide),Nat.zero_add]
      exact eval_chooseField _ _ _ _ m _ ⟨_,little j⟩ wide whereAt
    change (if Comparison.lt.test (left.eval m _) (H:Word w) then _ else _)=_
    rw [ite_eq_left (show Comparison.lt.test (left.eval m (h.val:Word w)) (H:Word w)=true by
      simpa [Comparison.test] using hit)]
    have all := DescentPackedSumWords.eval_sum
      (fun j : Fin 7 => shifted b j (values src left right core j))
      (fun j : Fin 7 => digits A j*(2^b)^j.val) m (h.val:Word w) limb (List.finRange 7)
    rw [←List.ofFn_eq_map,List.sum_ofFn] at all
    refine all.trans (congrArg (fun n : ℕ => (n : Word w)) ?_)
    change _=(finFunctionFinEquiv (fun j : Fin 7=>(digits A j:Cell b))).val
    rw [finFunctionFinEquiv_apply]
    exact Finset.sum_congr rfl (fun j _=>by rw [Fin.val_cast_of_lt ((little j).trans_le fit)])

theorem fits {H out : ℕ} (src : Fin 3→Expr) (left right core : Expr)
    (srcFit : ∀j,(src j).Fits w out) (a : left.Fits w out) (b₀ : right.Fits w out) (c : core.Fits w out) :
    (header b H src left right core).Fits w out:=by
  have all (j : Fin 4) : (full src j).Fits w out:=by
    cases j using Fin.cases with
    | zero=>trivial
    | succ j=>exact srcFit j
  have skipFit : («omit» src).Fits w out:=⟨srcFit 0,trivial,trivial,srcFit 1,trivial,trivial,srcFit 2,trivial,trivial,trivial⟩
  have each (j : Fin 7) : (values src left right core j).Fits w out:=by
    fin_cases j <;> first | trivial | exact DescentResetSourceClassRAM.rank_fits (full src) _ all a |
      exact DescentResetSourceClassRAM.rank_fits (full src) _ all b₀ | exact DescentResetSourceClassRAM.rank_fits (full src) _ all trivial
  have shiftedFit (j : Fin 7) : (shifted b j (values src left right core j)).Fits w out :=
    BoughtSockets.choose_fits_bound 5 0 (fun k => .lit (k.val*(2^b)^j.val))
      (values src left right core j) (fun _ => trivial) (each j)
  exact ⟨a,trivial,fits_total _ shiftedFit _,trivial⟩

theorem run (b base : ℕ) (peer : Fin H→Fin 3→Option (Fin H)) (arg : Fin H→Option (Fin H×Fin H×Bool))
    (src : Fin 3→Expr) (left right core : Expr) (m : Memory w) (small : H<2^w) (wide : 5≤2^w) (fit : 5≤2^b)
    (srcFit : ∀j,(src j).Fits w base) (a : left.Fits w base) (b₀ : right.Fits w base) (c : core.Fits w base)
    (old : ∀h : Fin H,∀j,(src j).eval m (h.val:Word w)=(target (peer h j):Word w))
    (first : ∀h : Fin H,left.eval m (h.val:Word w)=((arg h).elim H (fun p=>p.1.val):Word w))
    (last : ∀h : Fin H,right.eval m (h.val:Word w)=((arg h).elim H (fun p=>p.2.1.val):Word w))
    (mark : ∀h : Fin H,core.eval m (h.val:Word w)=((arg h).elim 0 (fun p=>p.2.2.toNat):Word w))
    (room : base+H<2^w) :
    let e:=header b H src left right core
    let p:=scan w base H e
    let done:=ProtocolRAM.image base H e m
    p.Exec m done (4+H*(2*e.work+4)) ∧
      (∀h : Fin H,done (base+h.val)=((raw b (integer peer h (arg h))).val:Word w)) ∧
      (∀x,x<base ∨ base+H≤x→done x=m x) ∧ DescentStaticWordColumn.names p=11+4*e.work ∧ CheapCode p:=by
  intro e p done
  refine ⟨scan_exec _ _ _ _ (fits _ _ _ _ srcFit a b₀ c) room,?_,
    ProtocolRAMGeneratedWrite.frame_image base H e m,DescentStaticWordColumn.names_scan ..,?_⟩
  · intro h;exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ h).trans (read b peer arg h src left right core m small wide fit (old h) (first h) (last h) (mark h))
  · apply scan_cheap

end
end Hierarchy.DescentResetTrunkScalar

end OAI
