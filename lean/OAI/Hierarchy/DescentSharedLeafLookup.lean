import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Looking up a host-shared leaf rank in every local packed group -/
namespace Hierarchy.DescentSharedLeafLookup
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local.Gather DescentIssuedTerminalId
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {d k N H G M w : ℕ}
structure Header where
  ranks : Bank
  start : Bank
  cut : Bank
  broadcast : Bank

def repeated (i : Fin (M+1)) (x : Cell d) : Cell (d*M) :=
  encode d M (fun j=>if j.val < i.val then x else 0)

def repeatAddr (i : Fin (M+1)) (x : Cell d) := i.val*2^d+x.val

def usedRow (p : Row H G M) : Fin (M+1) := ⟨used G M p.2.val,Nat.lt_succ_of_le (min_le_left _ _)⟩

theorem repeater (x : Fin H→Cell d) (p : Row H G M) :
    repeated (usedRow p) (x p.1)=data (fun h (_ : Fin G)=>x h) p := by
  apply congrArg (encode d M)
  funext i
  by_cases alive : p.2.val*M+i.val<G
  · have within : i.val<(usedRow p).val := active i alive
    simp [within,alive]
  · have no : ¬i.val<(usedRow p).val := by
      intro h
      have bound:=(lt_of_lt_of_le h (min_le_right M (G-p.2.val*M)))
      omega
    simp [no,alive]

def address (B : Header) (j : Fin N) :=
  Expr.lookup B.ranks (.op .add (.lookup B.start .row) (.lit j.val))
def source (B : Header) (j : Fin N) :=
  Expr.lookup B.broadcast (.op .add (.lookup B.cut .row) (address B j))

structure Readable (B : Header) (N H G M d w out : ℕ) : Prop where
  fit : ∀b∈[B.ranks,B.start,B.cut,B.broadcast],b.Fits w out
  ranks : H*N≤B.ranks.size
  starts : H*chunks G M≤B.start.size
  cuts : H*chunks G M≤B.cut.size
  repeats : (M+1)*2^d≤B.broadcast.size

structure Fixed (B : Header) (N H G M d : ℕ) (m : Memory w) : Prop where
  start : ∀p : Row H G M,m (B.start.base+(row H G M p).val)=((p.1.val*N:ℕ):Word w)
  cut : ∀p : Row H G M,m (B.cut.base+(row H G M p).val)=(((usedRow p).val*2^d:ℕ):Word w)
  broadcast : ∀i : Fin (M+1),∀x : Cell d,m (B.broadcast.base+repeatAddr i x)=((repeated i x).val:Word w)

theorem repeated_source (B : Header) (out : ℕ) (m : Memory w) (room : Readable B N H G M d w out)
    (fixed : Fixed B N H G M d m) (rank : Fin H→Fin N→Cell d)
    (stored : ∀h j,m (B.ranks.base+(h.val*N+j.val))=((rank h j).val:Word w)) (j : Fin N) :
    Source (source B j) (fun h (_ : Fin G)=>rank h j) M m := by
  intro p
  let rowNo:=(row H G M p).val
  let x : Word w:=(rowNo:Word w)
  have bfit (b) (member : b∈[B.ranks,B.start,B.cut,B.broadcast]) : b.size<2^w := (room.fit b member).2.1
  have st:=(lookup_nat _ m x .row _ rfl ((row H G M p).isLt.trans_le room.starts) (bfit _ (by simp))).trans (fixed.start p)
  have cu:=(lookup_nat _ m x .row _ rfl ((row H G M p).isLt.trans_le room.cuts) (bfit _ (by simp))).trans (fixed.cut p)
  have xy (f : ℕ) (a : Fin f) (l : ℕ) (b : Fin l) : a.val*l+b.val<f*l :=
    (Nat.add_lt_add_left b.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ a.isLt)
  have rankRead : (address B j).eval m x=((rank p.1 j).val:Word w) := by
    apply (lookup_nat _ m x _ _ _ ((xy _ p.1 _ j).trans_le room.ranks) (bfit _ (by simp))).trans (stored p.1 j)
    change (Expr.lookup B.start .row).eval m x+(j.val:Word w)=_
    rw [st,Nat.cast_add]
  have targetRead := fixed.broadcast (usedRow p) (rank p.1 j)
  rw [repeater (fun h=>rank h j)] at targetRead
  apply (lookup_nat _ m x _ _ _ ((xy _ (usedRow p) _ (rank p.1 j)).trans_le room.repeats) (bfit _ (by simp))).trans targetRead
  change (Expr.lookup B.cut .row).eval m x+(address B j).eval m x=_
  rw [cu,rankRead,Nat.cast_add]

def choose (n : ℕ) (ix : Cell k) (scores : Cell (d*n)) : Cell d :=
  if ok : 0 < ix.val ∧ ix.val≤n then (encode d n).symm scores ⟨ix.val-1,by omega⟩ else 0

def lookup (B : Header) (T : Fin N→Tables) (final : Tables) (key : Expr) :=
  final.read key (collect T (source B) (List.finRange N))

theorem lookup_source (B : Header) (T : Fin N→Tables) (final : Tables) (key : Expr)
    (out : ℕ) (m : Memory w) (room : Readable B N H G M d w out) (fixed : Fixed B N H G M d m)
    (rank : Fin H→Fin N→Cell d) (nums : ∀h j,m (B.ranks.base+(h.val*N+j.val))=((rank h j).val:Word w))
    (bounds : Bounds (w:=w) (d:=d) (M:=M) T (source B) out)
    (rom : ∀i,Static (T i) (setField (d:=d) i) M m)
    (shared : Fits final key (collect T (source B) (List.finRange N)) k (d*N) M out w)
    (selectROM : Static final (choose (k:=k) (d:=d) N) M m)
    (ticket : Fin H→Fin G→Cell k) (selected : Source key ticket M m) :
    Source (lookup B T final key) (fun h g=>choose N (ticket h g) (encode d N (rank h))) M m := by
  have corpus:=collected T (source B) out bounds m rom (fun h (_ : Fin G) j=>rank h j)
    (repeated_source B out m room fixed rank nums) (List.finRange N)
  simp only [List.mem_finRange,ite_true] at corpus
  exact read_data final key _ out shared (choose N) (by simp [choose]) m selectROM ticket _ selected corpus

theorem lookup_issued (B : Header) (T : Fin N→Tables) (final : Tables) (key : Expr)
    (out : ℕ) (m : Memory w) (fit : (lookup B T final key).Fits w out) (space : out+H*chunks G M<2^w)
    (values : Fin H→Fin G→Cell d) (computed : Source (lookup B T final key) values M m) :
    let e:=lookup B T final key
    (scan w out (H*chunks G M) e).Exec m (image out (H*chunks G M) e m)
      (4+(H*chunks G M)*(2*e.work+4)) ∧ ∀p : Row H G M,
      image out (H*chunks G M) e m (out+(row H G M p).val)=((data values p).val:Word w) :=
  ⟨scan_exec _ _ _ m fit space,fun p=>(ProtocolRAMGeneratedWrite.read_image _ _ _ m _).trans (computed p)⟩

end
end Hierarchy.DescentSharedLeafLookup

end OAI
