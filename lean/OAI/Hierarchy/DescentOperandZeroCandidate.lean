import OAI.Hierarchy.DescentOperandFieldJoin

namespace OAI
/-! # A zero candidate contributes nothing for any signed query word -/
namespace Hierarchy.DescentOperandFieldJoin
open DescentSIMDLookup DescentPackedZip DescentOperandCandidateLookup
open DescentOrdinaryAtomFieldRAM.ROM DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {n a b c H G M w : ℕ}

private theorem packed_zero (t L : ℕ) : encode t L (fun _=>0)=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin L=>(0:Cell t))).val=0
  simp []

/-- The shift bank masks the query to its own width. The right half of the
resulting table address is still zero for every possible physical query. -/
theorem read_zero (T : Tables) (q : Expr) (i : Fin n) (out : ℕ)
    (fit : DescentPackedZip.Fits T q (.lit 0) a b M out w)
    (m : Memory w) (fixed : Static T (take (a:=a) (b:=b) (c:=c) i) M m) (r : Word w) :
    (T.read q (.lit 0)).eval m r=0 := by
  let x : Cell (a*M):=⟨(q.eval m r).val%2^(a*M),Nat.mod_lt _ (by positivity)⟩
  let z:=key a b M (x,0)
  have shift : T.shift.read m (q.eval m r)=((2^(b*M)*x.val:ℕ):Word w) := by
    simpa only [Bank.read,Bank.size,fit.shiftBits,x] using fixed.1 x
  have inside : z.val<T.apply.size:=by simpa only [Bank.size,fit.applyBits] using z.isLt
  have decode : (encode b M).symm 0=(fun _=>0) :=
    (encode b M).symm_apply_eq.mpr (packed_zero b M).symm
  have empty : DescentPackedZip.table (take (a:=a) (b:=b) (c:=c) i) z=0:=by
    simp only [z,DescentPackedZip.table,Equiv.symm_apply_apply,decode]
    calc
      _ = encode c M (fun _=>0) := by
        apply congrArg (encode c M)
        funext j
        unfold take
        split <;> rfl
      _ = 0 := packed_zero c M
  change T.apply.read m ((0:Word w)+T.shift.read m (q.eval m r))=0
  rw [zero_add,shift]
  have addr : z.val=2^(b*M)*x.val:=by simp [z,key_val]
  rw [←addr,DescentPackedZip.bank_read T.apply m inside fit.apply,fixed.2 z]
  simpa only [Fin.val_zero,Nat.cast_zero] using
    congrArg (fun v : Cell (c*M)=>(v.val : Word w)) empty

theorem stored_blank {base out : ℕ} (q kept : Expr) (m : Memory w)
    (saved : Fin H→Fin G→Cell c) (early : q.Fits w base) (hold : kept.Fits w base)
    (src : Source kept saved M m) (sep : dictionaryEnd n a b M base≤out) (top : out<2^w) :
    Source (merge base a b c M q kept (fun _ : Fin n=>.lit 0)) saved M
      (after (pages n a b c M) (bits a b M) base m) := by
  let book:=pages n a b c M
  let span:=bits a b M
  let dst:=after book span base m
  have low : base≤out:=(Nat.le_add_right ..).trans sep
  have seen : Source kept saved M dst:=fun p=>(eval_below kept _ m dst hold
    (fun z hz=>frame book span base m z (.inl hz))).trans (src p)
  intro p
  let r : Word w:=(row H G M p).val
  have zero (i : Fin n) : ((tab base a b c M i).read q (.lit 0)).eval dst r=0 := by
    apply read_zero (tab base a b c M i) q i out
    · exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ low early,trivial,
        bank_room book span base out _ (pages_fit (index i 0)) sep top,
        bank_room book span base out _ (pages_fit (index i 1)) sep top,
        congrArg Page.bits (layout (a:=a) (b:=b) (c:=c) (M:=M) i 0),
        congrArg Page.bits (layout (a:=a) (b:=b) (c:=c) (M:=M) i 1)⟩
    · exact binary_mounted (take (a:=a) (b:=b) (c:=c) i) M book span base m pages_fit (index i) (layout i)
  have totalZero (xs : List (Fin n)) : (total (fun i=>(tab base a b c M i).read q (.lit 0)) xs).eval dst r=0 := by
    induction xs with
    | nil=>rfl
    | cons i xs ih=>
      change ((tab base a b c M i).read q (.lit 0)).eval dst r +
        (total (fun j=>(tab base a b c M j).read q (.lit 0)) xs).eval dst r = 0
      rw [zero i,ih,add_zero]
  change kept.eval dst r+(total (fun i=>(tab base a b c M i).read q (.lit 0)) (List.finRange n)).eval dst r=_
  rw [totalZero,add_zero]
  exact seen p

end
end Hierarchy.DescentOperandFieldJoin

end OAI
