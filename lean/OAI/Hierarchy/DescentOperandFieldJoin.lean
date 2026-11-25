import OAI.Hierarchy.DescentOperandCandidateLookup

namespace OAI
/-! # A reached signed candidate and a retained operand may use different digit widths -/
namespace Hierarchy.DescentOperandFieldJoin
open DescentSIMDLookup DescentPackedZip DescentOperandCandidateLookup
open DescentOrdinaryAtomFieldRAM.ROM DescentColonies.SplitRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {n a b c H G M w : ℕ}

def take (i : Fin n) (q : Cell a) (x : Cell b) : Cell c :=
  if q.val=i.val+1 then (x.val:Cell c) else 0

theorem absent (i : Fin n) : take (a:=a) (b:=b) (c:=c) i 0 0=0 := by simp [take]

theorem found (hr : n<2^a) (i : Fin n) (q : Option (Fin n)) (x : Cell b) :
    take (c:=c) i (code hr q) x = if q=some i then (x.val:Cell c) else 0 := by
  cases q with
  | none=>simp [take,DescentOperandCandidateLookup.code]
  | some j=>
    by_cases eqn:j=i
    · subst j;simp [take,DescentOperandCandidateLookup.code]
    · have ne : j.val≠i.val:= fun h=>eqn (Fin.ext h)
      simp [take,DescentOperandCandidateLookup.code,ne,eqn]

def pages (n a b c M : ℕ) (j : Fin (n*2)) : Page :=
  let pair:=finProdFinEquiv.symm j
  binary (take (a:=a) (b:=b) (c:=c) pair.1) M pair.2

theorem layout (i : Fin n) (s : Fin 2) :
    pages n a b c M (index i s)=binary (take (a:=a) (b:=b) (c:=c) i) M s := by simp [pages,index]

theorem pages_fit (i : Fin (n*2)) : (pages n a b c M i).bits≤bits a b M := by
  obtain ⟨⟨j,z⟩,rfl⟩:=finProdFinEquiv.surjective i
  rw [show pages n a b c M (finProdFinEquiv (j,z))=_ from layout j z]
  fin_cases z
  · exact Nat.mul_le_mul_right M (Nat.le_add_right ..)
  · exact le_rfl

def tab (base a b c M : ℕ) (i : Fin n) :=joined (pages n a b c M) (bits a b M) base (index i)
def merge (base a b c M : ℕ) (q kept : Expr) (v : Fin n→Expr) : Expr :=
  .op .add kept (total (fun i=>(tab base a b c M i).read q (v i)) (List.finRange n))

theorem safe {base out : ℕ} (q kept : Expr) (v : Fin n→Expr)
    (early : q.Fits w base) (hold : kept.Fits w base) (values : ∀i,(v i).Fits w base)
    (sep : dictionaryEnd n a b M base≤out) (room : out<2^w) :
    (merge base a b c M q kept v).Fits w out := by
  have prior : base≤out:=(Nat.le_add_right ..).trans sep
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ prior hold,fits_total _ (fun i=>?_) _⟩
  constructor
  · exact bank_room (pages n a b c M) (bits a b M) base out _ (pages_fit (index i 1)) sep room
  · exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ prior (values i),
      ⟨bank_room (pages n a b c M) (bits a b M) base out _ (pages_fit (index i 0)) sep room,
        ProtocolRAMGeneratedWrite.fits_mono _ prior early⟩⟩

theorem packed_add (x y z : Fin H→Fin G→Cell c) (values : ∀h g, (x h g).val+(y h g).val=(z h g).val)
    (p : Row H G M) : (data x p).val+(data y p).val=(data z p).val := by
  simp only [DescentPackedSumWords.lanes_val]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split
  · rw [←Nat.add_mul,values]
  · simp

/-- The local source retains the original copy/alias/range digits. The signed
candidate contributes the reached neighbor and first parallel ordinal. The
lookup widens that operand to the result digit directly inside its native ROM. -/
theorem stored {base out : ℕ} (q kept : Expr) (v : Fin n→Expr) (m : Memory w) (hr : n<2^a)
    (ticket : Fin H→Fin G→Option (Fin n)) (val : Fin n→Fin H→Fin G→Cell b)
    (saved actual : Fin H→Fin G→Cell c)
    (early : q.Fits w base) (hold : kept.Fits w base) (values : ∀i,(v i).Fits w base)
    (qs : Source q (fun h g=>code hr (ticket h g)) M m) (vs : ∀i,Source (v i) (val i) M m)
    (ks : Source kept saved M m)
    (joint : ∀h g,(saved h g).val+
      (selected ticket (fun i h g=>((val i h g).val:Cell c)) h g).val=(actual h g).val)
    (sep : dictionaryEnd n a b M base≤out) (top : out<2^w) :
    Source (merge base a b c M q kept v) actual M (after (pages n a b c M) (bits a b M) base m) := by
  let book:=pages n a b c M
  let span:=bits a b M
  let dst:=after book span base m
  have lower : base≤out:=(Nat.le_add_right ..).trans sep
  have read {t : ℕ} (e : Expr) (x : Fin H→Fin G→Cell t) (fit : e.Fits w base) (src : Source e x M m) :
      Source e x M dst := fun p=>(eval_below e _ m dst fit (fun z hz=>frame book span base m z (.inl hz))).trans (src p)
  have limits (i : Fin n) : DescentPackedZip.Fits (tab base a b c M i) q (v i) a b M out w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ lower early,ProtocolRAMGeneratedWrite.fits_mono _ lower (values i),
      bank_room book span base out _ (pages_fit (index i 0)) sep top,bank_room book span base out _ (pages_fit (index i 1)) sep top,
      congrArg Page.bits (layout (a:=a) (b:=b) (c:=c) (M:=M) i 0),
      congrArg Page.bits (layout (a:=a) (b:=b) (c:=c) (M:=M) i 1)⟩
  intro p
  have piece (i : Fin n):=read_data (tab base a b c M i) q (v i) out (limits i) (take (c:=c) i) (absent i) dst
    (binary_mounted (take (c:=c) i) M book span base m pages_fit (index i) (layout i)) _ _
    (read q _ early qs) (read (v i) _ (values i) (vs i)) p
  simp only [found] at piece
  have add:= DescentPackedSumWords.eval_sum _ _ dst _ piece (List.finRange n)
  rw [←List.ofFn_eq_map,List.sum_ofFn,packed_select ticket (fun i h g=>((val i h g).val:Cell c)) p] at add
  change (kept.eval dst _)+(total (fun i=>(tab base a b c M i).read q (v i)) (List.finRange n)).eval dst _=_
  rw [read kept _ hold ks p,add,←Nat.cast_add,packed_add saved _ actual joint p]

theorem work (q kept : Expr) (v : Fin n→Expr) (base a b c M lim : ℕ)
    (bound : ∀i,q.work+(v i).work+11≤lim) :
    (merge base a b c M q kept v).work≤kept.work+(1+n*(lim+1))+1 := by
  have piece (i : Fin n) : ((tab base a b c M i).read q (v i)).work≤lim := by simpa only [DescentPackedZip.work] using bound i
  have sum:=work_total _ lim piece (List.finRange n)
  simp only [List.length_finRange] at sum
  exact Nat.add_le_add_right (Nat.add_le_add_left sum _) _

end
end Hierarchy.DescentOperandFieldJoin

end OAI
