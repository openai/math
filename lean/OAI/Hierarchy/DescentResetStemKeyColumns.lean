import OAI.Hierarchy.DescentResetStemKeyRAM
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Materialize the old physical actor's key once, before new-host reindexing -/
namespace Hierarchy.DescentResetStemKey.Columns
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D f Q H G M w : ℕ} (parse : Decoder D f) (side : Fin Q→Bool) (src : Fin Q→Fin (D+2)→Expr)

def start (base D f M : ℕ) := base+words D f M
def bank (base D f M H G q : ℕ) : Bank :=
  ⟨start base D f M+q*(H*chunks G M), Nat.clog 2 (H*chunks G M)⟩
def stop (base D f M H G Q : ℕ) :=
  start base D f M+Q*(H*chunks G M)+span (H*chunks G M)
def terms (base M : ℕ) := List.ofFn (fun q=>expr parse M base (side q) (src q))
def passes (base M H G : ℕ) :=
  ProbeStage.Native.columns (H*chunks G M) (start base D f M) (terms parse side src base M)
def code (base M H G w : ℕ) :=
  (DescentResetStemKey.program parse M w base).seq (ProtocolRAM.program w (passes parse side src base M H G))
def ticks (base M H G : ℕ) := (4+10*words D f M)+clock (passes parse side src base M H G)
def output (base M H G : ℕ) (m : Memory w) :=
  result (passes parse side src base M H G) (memory parse M base m)

theorem bank_fits (base D f M H G Q w : ℕ) (q : Fin Q) (room : stop base D f M H G Q<2^w) :
    (bank base D f M H G q.val).Fits w (stop base D f M H G Q) ∧
      H*chunks G M≤(bank base D f M H G q.val).size := by
  let N:=H*chunks G M
  have hi : q.val*N≤Q*N:=Nat.mul_le_mul_right _ q.isLt.le
  change (0< span N ∧ span N<2^w ∧ start base D f M+q.val*N+span N≤ stop base D f M H G Q) ∧ N≤ span N
  change start base D f M+Q*N+span N<2^w at room
  exact ⟨⟨span_pos _,by omega,by unfold stop; dsimp [N] at *; omega⟩,span_ge _⟩

theorem any_full (base : ℕ) (m : Memory w) (safe : ∀q i,(src q i).Fits w base)
    (room : stop base D f M H G Q<2^w) :
    (code parse side src base M H G w).Exec m (output parse side src base M H G m)
      (ticks parse side src base M H G) ∧
      (∀ a, a < base ∨ stop base D f M H G Q ≤ a → output parse side src base M H G m a=m a) ∧
      CheapCode (code parse side src base M H G w) := by
  let es:=terms parse side src base M
  let top:=start base D f M
  have len : es.length=Q:=List.length_ofFn
  have bound : top+Q*(H*chunks G M)<2^w:=(Nat.le_add_right _ _).trans_lt room
  have fit : top<2^w:=(Nat.le_add_right ..).trans_lt bound
  have uses : ∀e∈es,e.Fits w top:=by
    intro e present
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp present
    exact expr_fits parse (side q) M base (src q) (safe q) fit
  let scans:=ProbeStage.Native.columns (H*chunks G M) top es
  have scan : (ProtocolRAM.program w scans).Exec (memory parse M base m)
      (result scans (memory parse M base m)) (clock scans) := ProbeStage.Native.columns_exec es (memory parse M base m)
    (ProbeStage.Native.columns_safe (n:=H*chunks G M) es (le_refl top) uses (by rw [len];exact bound))
  have installed := mounted parse M base m fit
  refine ⟨?_,?_,cheap_seq installed.2.2.2.2 (@ProtocolRAM.program_cheap w (passes parse side src base M H G))⟩
  · intro P R K machine pc reg pub exit rom advice cfg mem enter same
    exact Procedure.Exec.then installed.1 scan machine pc reg pub exit rom advice cfg mem enter same
  intro a away
  have first : base ≤ top := Nat.le_add_right ..
  rcases away with lower|upper
  · exact (ProbeStage.Native.columns_frame (n:=H*chunks G M) (base:=top) es (memory parse M base m)
      (.inl (lower.trans_le first))).trans (installed.2.2.2.1 a (.inl lower))
  · have hi : top+es.length*(H*chunks G M) ≤ a := by
      rw [len]
      exact (Nat.le_add_right _ _).trans upper
    exact (ProbeStage.Native.columns_frame es (memory parse M base m) (.inr hi)).trans
      (installed.2.2.2.1 a (.inr ((Nat.le_add_right ..).trans hi)))

theorem any (base : ℕ) (m : Memory w) (safe : ∀q i,(src q i).Fits w base)
    (room : stop base D f M H G Q<2^w) :
    (code parse side src base M H G w).Exec m (output parse side src base M H G m)
      (ticks parse side src base M H G) :=
  (any_full parse side src base m safe room).1

theorem run (base : ℕ) (m : Memory w) (dead : parse 0=none) (x : Fin Q→Fin H→Fin G→Fin (D+2)→Cell f)
    (safe : ∀q i,(src q i).Fits w base) (read : ∀q i,Source (src q i) (fun h g=>x q h g i) M m)
    (room : stop base D f M H G Q<2^w) :
    let last:=output parse side src base M H G m
    (code parse side src base M H G w).Exec m last (ticks parse side src base M H G) ∧
    (∀q,Reads (bank base D f M H G q.val) (fun h g=>word parse (side q) (x q h g)) M last) ∧
    (∀a,a< base ∨ stop base D f M H G Q≤ a→last a=m a) ∧ CheapCode (code parse side src base M H G w) := by
  let es:=terms parse side src base M
  let top:=start base D f M
  let mid:=memory parse M base m
  have len : es.length=Q:=List.length_ofFn
  have limit : top+Q*(H*chunks G M)≤ stop base D f M H G Q:=Nat.le_add_right ..
  have bound : top<2^w:=(Nat.le_add_right ..).trans_lt (limit.trans_lt room)
  have view (q : Fin Q):=issued parse dead (side q) base (src q) m (x q) (safe q) (read q) bound
  have fits : ∀e∈es,e.Fits w top := by
    intro e hd
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp hd
    exact (view q).1
  have full:=any_full (H:=H) (G:=G) (M:=M) parse side src base m safe room
  refine ⟨full.1,?_,full.2.1,full.2.2⟩
  intro q p
  have placed:=ProbeStage.Native.columns_read es mid (le_refl top) fits q.val
    (q.isLt.trans_eq len.symm) (row H G M p)
  exact placed.trans (by simpa only [es,terms,List.getElem_ofFn] using (view q).2 p)

theorem clock_bound (base M H G T : ℕ) (room : ∀q i,(src q i).work≤T) :
    ticks parse side src base M H G ≤ (4+10*words D f M)+
      (4+Q*(4+(H*chunks G M)*(2*(14+(D+2)*(T+11))+4))) := by
  have cap : ∀e∈terms parse side src base M,e.work≤14+(D+2)*(T+11) := by
    intro e he
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp he
    exact expr_work parse M base (side q) (src q) T (room q)
  have pay:=ProbeStage.Native.columns_clock (H*chunks G M) (start base D f M) _ _ cap
  simpa only [ticks,passes,terms,List.length_ofFn] using Nat.add_le_add_left pay (4+10*words D f M)

end
end Hierarchy.DescentResetStemKey.Columns

end OAI
