import OAI.Hierarchy.DescentTerminalPositionPages
import OAI.Hierarchy.DescentTerminalSpanRead

namespace OAI
/-! # Native common-position address generation for the immutable site-book decoder -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentTerminalRowBooks DescentTerminalDenseWindow DescentTerminalChronologicalBooks DescentTerminalRecipeRows
open DescentTerminalSpanBook Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V W B bits pool S : ℕ}
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

structure Directory where
  span : Cursors
  ports : Bank
  count : Bank
  firstWord : Bank
  skip : Bank
  texture : Bank
  countShift : Bank
  modeShift : Bank
  skipShift : Bank
  wordShift : Bank

def rowMode (L : Directory) : Expr :=
  let site:=Expr.lookup L.span.owner .row
  let localRow:=Expr.lookup L.span.localRow .row
  let port:=Expr.lookup L.ports site
  .branch .lt localRow port (.lit 0) (.op .add (.op .sub localRow port) (.lit 1))

def gather (L : Directory) : Expr :=
  let site:=Expr.lookup L.span.owner .row
  let addr:=Expr.lookup L.firstWord site
  let lo:=Expr.lookup L.texture addr
  let hi:=Expr.lookup L.texture (.op .add addr (.lit 1))
  .branch .eq (.lookup L.span.active .row) (.lit 0) (.lit 0)
    (.op .add (.lookup L.countShift (.lookup L.count site))
      (.op .add (.lookup L.modeShift (rowMode L)) (.op .add (.lookup L.skipShift (.lookup L.skip site))
        (.op .add (.lookup L.wordShift lo) hi))))

def modeAt (ports : ℕ) (u : Fin W) : Fin (W+1) :=
  if h : u.val<ports then 0 else ⟨u.val-ports+1,by have:=u.isLt;omega⟩

structure Reached (L : Directory) (m : Memory bits) (sites : Fin S→Site) (fit : ∀i,(sites i).rows q≤W)
    (z : Fin S→Raw) (start : Fin S→ℕ) (stream : ℕ→Bool) (bp : 0<B) : Prop where
  span : ∀i : Fin pool,L.span.Facts sites i fit m
  ports : ∀i,L.ports.read m (i.val:Word bits)=((sites i).portRows q:Word bits)
  count : ∀i,L.count.read m (i.val:Word bits)=((z i).1.val:Word bits)
  first : ∀i,L.firstWord.read m (i.val:Word bits)=((start i/B:ℕ):Word bits)
  skip : ∀i,L.skip.read m (i.val:Word bits)=((start i%B:ℕ):Word bits)
  low : ∀i,L.texture.read m ((start i/B:ℕ):Word bits)=((dense B stream (start i/B)).val:Word bits)
  high : ∀i,L.texture.read m ((start i/B+1:ℕ):Word bits)=((dense B stream (start i/B+1)).val:Word bits)
  countROM : ∀j : Fin (V+1),L.countShift.read m (j.val:Word bits)=((j.val*((W+1)*(B*(2^B*2^B))):ℕ):Word bits)
  modeROM : ∀j : Fin (W+1),L.modeShift.read m (j.val:Word bits)=((j.val*(B*(2^B*2^B)):ℕ):Word bits)
  skipROM : ∀j : Fin B,L.skipShift.read m (j.val:Word bits)=((j.val*(2^B*2^B):ℕ):Word bits)
  wordROM : ∀j : Word B,L.wordShift.read m (j.val:Word bits)=((j.val*2^B:ℕ):Word bits)

def chosen (sites : Fin S → Site) (fit : ∀ i, (sites i).rows q ≤ W) (z : Fin S → Raw)
    (start : Fin S → ℕ) (stream : ℕ → Bool) (bp : 0 < B) (i : Fin pool) : Fin (alphabet V W B) :=
  (DescentTerminalSpanBook.resolve sites fit i.val).elim
    (index (0 : Fin (V+1)) (0 : Fin (W+1)) (⟨0,bp⟩ : Fin B) (0 : Word B) (0 : Word B))
    (fun p : Fin S × Fin W =>
      index (z p.1).1 (modeAt ((sites p.1).portRows q) p.2) (⟨start p.1%B,Nat.mod_lt _ bp⟩ : Fin B)
        (dense B stream (start p.1/B)) (dense B stream (start p.1/B+1)))

theorem issue (sites : Fin S → Site) (fit : ∀ i, (sites i).rows q ≤ W)
    (z : Fin S → Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V))
    (start : Fin S → ℕ) (stream : ℕ → Bool) (bp : 0 < B) (L : Directory) (m : Memory bits)
    (receipt : Reached (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W)
      (B:=B) (bits:=bits) (pool:=pool) (S:=S) L m sites fit z start stream bp)
    (room : W < 2^bits) (pos : 0 < bits) (i : Fin pool) :
    ProtocolRAM.Expr.eval m (i.val : Word bits) (gather L) =
      ((chosen (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W) (B:=B)
        (pool:=pool) (S:=S) sites fit z start stream bp i).val : Word bits) := by
  have facts:=receipt.span i
  change _ ∧ _ at facts
  cases eqn:resolve sites fit i.val with
  | none=>
    have active:L.span.active.read m (i.val:Word bits)=0:=by simpa [eqn] using facts.1
    have nilAddress : (index (0 : Fin (V+1)) (0 : Fin (W+1)) (⟨0,bp⟩ : Fin B) (0 : Word B) 0).val = 0 := by
      simp [index,finProdFinEquiv_apply_val]
    simp [gather,Expr.eval,Comparison.test,active,chosen,eqn,Option.elim_none,nilAddress]
  | some pair=>
    rcases pair with ⟨k,u⟩
    have active : L.span.active.read m (i.val:Word bits)=1:=by simpa [eqn] using facts.1
    obtain ⟨owner,localRow⟩:=facts.2 k u eqn
    have ports : (sites k).portRows q ≤ W:=by
      have hf:=fit k;unfold Site.rows at hf;omega
    have compare : (rowMode L).eval m (i.val:Word bits)=((modeAt ((sites k).portRows q) u).val:Word bits):=by
      have less : (u.val : Word bits) < ((sites k).portRows q : Word bits) ↔ u.val < (sites k).portRows q := by
        change (u.val : Word bits).val < ((sites k).portRows q : Word bits).val ↔ _
        rw [Fin.val_cast_of_lt (u.isLt.trans room),Fin.val_cast_of_lt (ports.trans_lt room)]
      simp only [rowMode,Expr.eval,Comparison.test,localRow,owner,receipt.ports k,less,decide_eq_true_eq]
      by_cases isPort : u.val<(sites k).portRows q
      · simp [isPort,modeAt]
      · simp [isPort,modeAt,RowOp.opcode,BinaryOp.eval,Nat.cast_sub (Nat.le_of_not_gt isPort)]
    have one : (1:Word bits)≠0:=by
      have cap : 1 < 2^bits := Nat.one_lt_pow pos.ne' (by decide)
      intro h
      have hh := congrArg Fin.val h
      change 1 % 2^bits = 0 at hh
      exact Nat.one_ne_zero (by simpa only [Nat.mod_eq_of_lt cap] using hh)
    have live : Comparison.eq.test (1 : Word bits) ((0:ℕ):Word bits) = false := by
      simp [Comparison.test,one]
    have countROM := receipt.countROM (z k).1
    have modeROM := receipt.modeROM (modeAt ((sites k).portRows q) u)
    have skipROM := receipt.skipROM (⟨start k%B,Nat.mod_lt _ bp⟩ : Fin B)
    have wordROM := receipt.wordROM (dense B stream (start k/B))
    have highWord : L.texture.read m (((start k/B : ℕ) : Word bits) + ((1 : ℕ) : Word bits)) =
        ((dense B stream (start k/B+1)).val : Word bits) := by
      rw [←Nat.cast_add]
      exact receipt.high k
    simp only [gather,Expr.eval,active,live,Bool.false_eq_true,ite_false,owner,receipt.count k,
      countROM,compare,modeROM,receipt.skip k,skipROM,receipt.first k,RowOp.opcode,BinaryOp.eval,
      receipt.low k,highWord,wordROM,chosen,eqn,Option.elim_some]
    simp only [←Nat.cast_add]
    apply congrArg (fun n:ℕ=>(n:Word bits))
    simp only [index,finProdFinEquiv_apply_val]
    ring

theorem run (L : Directory) (m : Memory bits) (out : ℕ) (f : (gather L).Fits bits out) (endAt : out+pool<2^bits) :
    (scan bits out pool (gather L)).Exec m (image out pool (gather L) m) (4+(pool*(2*(gather L).work+4))) ∧ CheapCode (scan bits out pool (gather L)) :=
  ⟨@scan_exec bits out pool (gather L) m f endAt,@scan_cheap bits out pool (gather L)⟩

end
end Hierarchy.DescentTerminalSiteShelves

end OAI
