import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentParallelBaseLUT
import OAI.Hierarchy.DescentHaloPackedGather

namespace OAI
/-! # Streaming SIMD rank of actual incident parent starts, using two short records per lookup -/
namespace Hierarchy.DescentParallelBase.Stream
open DescentSharedCableNames DescentSIMDLookup DescentPackedColony PackedBase DescentColonies.SplitRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D K L H G M w c : ℕ}
local notation "wd" => width D K L
local notation "bw" => Packed.bits L

def qty (q a : Option (Entry D K L)) :=q.elim 0 (fun entry=>counted entry a)

theorem qty_le (q a : Option (Entry D K L)) : qty q a≤L :=by
  cases q with
  | none=>simp [qty]
  | some q=>cases a with | none=>simp [qty,counted] | some a=>simp only [qty,Option.elim_some,counted];split <;> first | exact Nat.le_of_lt_succ a.weight.isLt | omega

def weight (q a : Option (Entry D K L)) : Cell bw :=⟨qty q a,lt_of_lt_of_le (Nat.lt_succ_of_le (qty_le q a)) (Nat.le_pow_clog (by decide) _)⟩

def compareWord (D K L : ℕ) (q a : Cell (width D K L)) :=weight (decode D K L q) (decode D K L a)

theorem word_zero : decode D K L 0=none:=by
  have z : word (none:Option (Entry D K L))=0:=by apply Fin.ext;rfl
  rw [←z,back]

theorem empty : compareWord D K L 0 0=0:=by apply Fin.ext;simp [compareWord,word_zero,weight,qty]

theorem read_compare (T : DescentPackedZip.Tables) (q a : Expr) (out : ℕ)
    (fit : DescentPackedZip.Fits T q a wd wd M out w) (m : Memory w)
    (pins : DescentPackedZip.Static T (compareWord D K L) M m) (target item : Fin H→Fin G→Option (Entry D K L))
    (query : DescentPackedZip.Source q (fun v g=>word (target v g)) M m) (old : DescentPackedZip.Source a (fun v g=>word (item v g)) M m) :
    DescentPackedZip.Source (T.read q a) (fun v g=>weight (target v g) (item v g)) M m :=by
  simpa only [compareWord,back] using DescentPackedZip.read_data T q a out fit (compareWord D K L) empty m pins _ _ query old

def totalWord (target : Fin H→Fin G→Option (Entry D K L)) (item : Fin c→Fin H→Fin G→Option (Entry D K L))
    (bounded : ∀v g,(∑i,qty (target v g) (item i v g))<2^bw) (v : Fin H) (g : Fin G) : Cell bw := ⟨_,bounded v g⟩

private theorem lanes_val {b : ℕ} (x : Fin H→Fin G→Cell b) (p : Row H G M) : (data x p).val=
    ∑j:Fin M,(if live:p.2.val*M+j.val<G then (x p.1 ⟨_,live⟩).val else 0)*(2^b)^j.val :=DescentPackedSumWords.lanes_val x p

theorem packed_sum (target : Fin H→Fin G→Option (Entry D K L)) (item : Fin c→Fin H→Fin G→Option (Entry D K L))
    (bounded : ∀v g,(∑i,qty (target v g) (item i v g))<2^bw) (p : Row H G M) :
    (∑i,(data (fun v g=>weight (target v g) (item i v g)) p).val)=(data (totalWord target item bounded) p).val :=by
  simp_rw [lanes_val];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro j hj
  by_cases inside:p.2.val*M+j.val<G
  · simp only [dite_eq_left inside,weight,totalWord,Finset.sum_mul]
  · simp [inside]

def instruction (T : DescentPackedZip.Tables) (q : Expr) (a : Fin c→Expr) := total (fun i=>T.read q (a i)) (List.finRange c)

private theorem eval_sum {α : Type} (f : α→Expr) (a : α→ℕ) (m : Memory w) (r : Word w)
    (ok : ∀i,(f i).eval m r=(a i:Word w)) (xs : List α) :
    (total f xs).eval m r=((xs.map a).sum:Word w) :=DescentPackedSumWords.eval_sum f a m r ok xs

/-- One generated row loads the true query, ranges over a fixed number of
candidate fields and adds short per-lane weights without carrying across
lanes. ROM address width is two short entries regardless of candidate count. -/
theorem run (T : DescentPackedZip.Tables) (q : Expr) (a : Fin c→Expr) (out : Bank) (m : Memory w)
    (fit : ∀i,DescentPackedZip.Fits T q (a i) wd wd M out.base w)
    (target : Fin H→Fin G→Option (Entry D K L)) (item : Fin c→Fin H→Fin G→Option (Entry D K L))
    (bounded : ∀v g,(∑i,qty (target v g) (item i v g))<2^bw) (static : DescentPackedZip.Static T (compareWord D K L) M m)
    (query : DescentPackedZip.Source q (fun v g=>word (target v g)) M m) (reads : ∀i,DescentPackedZip.Source (a i) (fun v g=>word (item i v g)) M m)
    (room : out.base+H*chunks G M<2^w) :
    let op:=instruction T q a
    let result:=image out.base (H*chunks G M) op m
    (scan w out.base (H*chunks G M) op).Exec m result (4+H*chunks G M*(2*op.work+4)) ∧
    DescentPackedColony.Reads out (totalWord target item bounded) M result ∧ CheapCode (scan w out.base (H*chunks G M) op) :=by
  intro op result
  have terms i : (T.read q (a i)).Fits w out.base:=by simp [DescentPackedZip.Tables.read,Expr.Fits,(fit i).left,(fit i).right,(fit i).apply,(fit i).shift]
  refine ⟨scan_exec _ _ _ _ (fits_total _ terms _) room,?_,by apply scan_cheap⟩
  intro p
  refine (ProtocolRAMGeneratedWrite.read_image out.base (H*chunks G M) op m (row H G M p)).trans ?_
  have each (i : Fin c):=(read_compare T q (a i) out.base (fit i) m static target (item i) query (reads i)) p
  have sum:=eval_sum (fun i=>T.read q (a i))
    (fun i=>(data (fun v g=>weight (target v g) (item i v g)) p).val) m
    ((row H G M p).val:Word w) each (List.finRange c)
  rw [←List.ofFn_eq_map,List.sum_ofFn,packed_sum target item bounded] at sum;exact sum

theorem work (T : DescentPackedZip.Tables) (q : Expr) (a : Fin c→Expr) (limit : ℕ) (rooms : ∀i,(a i).work≤limit) :
    (instruction T q a).work≤1+c*(q.work+limit+12):=by
  have bound:=work_total (fun i=>T.read q (a i)) (q.work+limit+11) (fun i=>by rw [DescentPackedZip.work];have:=rooms i;omega) (List.finRange c)
  simpa [instruction,Nat.add_assoc] using bound

/-- Real serial bound used by `run`, including empty query lanes. -/
theorem capacity {E U : Type} [Fintype E] [DecidableEq U] {n : ℕ} {B : Ends U n} (C : Blocks B E) (h : U)
    (address : Local C h↪Fin c) (row : Local C h→Entry D K L)
    (peer : ∀e f,(row e).peer=(row f).peer ↔ other C h e=other C h f)
    (order : ∀e f,other C h e=other C h f→(priority (row e)<priority (row f) ↔ C.first e.val<C.first f.val))
    (count : ∀e,(row e).weight.val=C.count e.val) (p : Fin c) (occupied : ∀u,(B.incident u).card≤L) :
    (∑i,qty (place address row p) (place address row i))<2^bw :=by
  by_cases found:∃e,address e=p
  · obtain ⟨e,rfl⟩:=found;rw [place_at];change base (place address row) (row e)<_
    rw [authentic C h address row peer order count e]
    have fits : L ≤ 2 ^ Packed.bits L :=
      (Nat.le_succ L).trans (Nat.le_pow_clog (by decide : 1 < 2) (L+1))
    apply (B.serial_lt occupied _ _ _ ?_).trans_le fits
    simp [Ends.parallel,C.atSource,C.atTarget]
  · simp [place_empty address row p (not_exists.mp found),qty]

end
end Hierarchy.DescentParallelBase.Stream

end OAI
