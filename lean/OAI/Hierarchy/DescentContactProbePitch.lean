import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentDyadicSpan
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Reusing old host measurements at every compact reset shape -/
namespace Hierarchy.DescentContactProbePitch
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentDyadicSpan DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H S G M a b w : ℕ}

def owner (v : Fin (H*S)) : Fin H := v.divNat
def shape (v : Fin (H*S)) : Fin S := v.modNat
def oldRow (p : Row (H*S) G M) : Row H G M := (owner p.1,p.2)
def lift (x : Fin H→Fin G→Cell a) (v : Fin (H*S)) (g : Fin G) := x (owner v) g
def shapeField (b : ℕ) (v : Fin (H*S)) (_ : Fin G) : Cell b := (shape v).val

theorem shape_val (safe : S≤2^b) (v : Fin (H*S)) (g : Fin G) :
    (shapeField b v g).val=v.val%S := by
  change (((shape v).val:Cell b)).val=_
  exact Fin.val_cast_of_lt ((shape v).isLt.trans_le safe)

theorem rows_read (x : Fin H→Fin G→Cell a) (p : Row (H*S) G M) :
    data (lift x) p=data x (oldRow p) := rfl

def count (H S G M : ℕ) := max (H*S) ((H*S)*chunks G M)
def bits (H S G M : ℕ) := Nat.clog 2 (count H S G M)
def extent (H S G M : ℕ) := 5*span (count H S G M)

/-- Old packed row, packed shape with genuine padding, raw shape host, then raw old host.
The last column is the packed start of a raw receiver. All five columns are shared by every socket, gate and input sheet. -/
def number (H S G M b : ℕ) (p : Fin 5) (i : ℕ) : ℕ :=
  let q:=chunks G M
  let packedShape:=if inside : i<(H*S)*q then
    (data (shapeField (H:=H) (S:=S) (G:=G) b) ((row (H*S) G M).symm ⟨i,inside⟩)).val else 0
  ![i/q/S*q+i%q,packedShape,i/q,i/S,i*q] p

def pages (H S G M b : ℕ) (p : Fin 5) : Page :=
  ⟨bits H S G M,fun i=>number H S G M b p i.val⟩

def table (H S G M b base : ℕ) (p : Fin 5) : Bank :=
  bank (pages H S G M b) (bits H S G M) base p

def value (H S G M b base : ℕ) (p : Fin 5) : Expr :=
  .lookup (table H S G M b base p) .row

def pull (H S G M b base : ℕ) (x : Expr) := x.atRow (value H S G M b base 0)
def sourceShape (H S G M b base : ℕ) := value H S G M b base 1
def rawAt (H S G M b base : ℕ) (x : Expr) := x.atRow (value H S G M b base 2)
def oldScalar (H S G M b base : ℕ) (x : Expr) := x.atRow (value H S G M b base 3)

def code (H S G M b base w : ℕ) :=mount (pages H S G M b) (bits H S G M) w base
def result (H S G M b base : ℕ) (m : Memory w) :=after (pages H S G M b) (bits H S G M) base m

theorem installed (H S G M b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w) :
    (code H S G M b base w).Exec m (result H S G M b base m) (4+10*extent H S G M) ∧
    CheapCode (code H S G M b base w) ∧
    (∀i,i<base ∨ base+extent H S G M≤ i → result H S G M b base m i=m i) ∧
    extent H S G M≤5*(2*count H S G M+1) := by
  exact ⟨(DescentOrdinaryAtomFieldRAM.ROM.run _ _ _ _ room).1,DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _,
    (fun i away => DescentOrdinaryAtomFieldRAM.ROM.frame (pages H S G M b) (bits H S G M) base m i away),
    Nat.mul_le_mul_left 5 (span_le _)⟩

theorem table_fits (H S G M b base : ℕ) (room : base+extent H S G M<2^w) (t : Fin 5) :
    (table H S G M b base t).Fits w (base+extent H S G M) :=
  bank_room _ _ _ _ t le_rfl le_rfl room

theorem fits_pull (H S G M b base : ℕ) (x : Expr) (held : x.Fits w base)
    (room : base+extent H S G M<2^w) :
    (pull H S G M b base x).Fits w (base+extent H S G M) :=
  ProtocolRAM.Calendar.CatalogueRows.fits_atRow x _
    (ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) held) ⟨table_fits _ _ _ _ _ _ room 0,trivial⟩

private theorem get (H S G M b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w)
    (t : Fin 5) (i : ℕ) (hi : i<count H S G M) :
    (value H S G M b base t).eval (result H S G M b base m) (i:Word w)=(number H S G M b t i:Word w) := by
  have small : i<2^(bits H S G M):=hi.trans_le (span_ge _)
  exact (bank_read _ _ small (table_fits _ _ _ _ _ _ room t)).trans
    (DescentOrdinaryAtomFieldRAM.ROM.read (pages H S G M b) (bits H S G M) _ m t le_rfl ⟨i,small⟩)

private theorem coordinates (p : Row (H*S) G M) :
    let i:=(row (H*S) G M p).val
    let q:=chunks G M
    i/q=p.1.val ∧ i%q=p.2.val := by
  have eqn:=Equiv.symm_apply_apply (row (H*S) G M) p
  exact ⟨congrArg (fun u : Row (H*S) G M=>u.1.val) eqn,congrArg (fun u : Row (H*S) G M=>u.2.val) eqn⟩

/-- The exact row transform on a current raw host and coarse group chunk. -/
theorem map_read (b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w) (p : Row (H*S) G M) :
    (value H S G M b base 0).eval (result H S G M b base m) ((row (H*S) G M p).val:Word w)=
      ((row H G M (oldRow p)).val:Word w) := by
  obtain ⟨host,part⟩:=coordinates p
  rw [get _ _ _ _ _ _ m room 0 _ ((row (H*S) G M p).isLt.trans_le (le_max_right ..))]
  apply congrArg (fun n : ℕ=>(n:Word w))
  change (row (H*S) G M p).val/chunks G M/S*chunks G M+(row (H*S) G M p).val%chunks G M=_
  rw [host,part]
  change p.1.val/S*chunks G M+p.2.val=p.2.val+chunks G M*(p.1.val/S)
  ac_rfl

/-- Old packed expressions may contain prior indirect lookups. All their addresses are evaluated
at the authentic original row, preserving the original incomplete-group padding. -/
theorem source_pull (b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w)
    (x : Expr) (values : Fin H→Fin G→Cell a) (held : x.Fits w base) (measured : Source x values M m) :
    Source (pull H S G M b base x) (lift (S:=S) values) M (result H S G M b base m) := by
  intro p
  rw [pull,eval_atRow,map_read b base m room p]
  exact (eval_below _ _ m _ held (fun i hi=>(installed H S G M b base m room).2.2.1 i (.inl hi))).trans (measured (oldRow p))

theorem old_reads (b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w)
    (old : Bank) (values : Fin H→Fin G→Cell a) (held : old.Fits w base)
    (space : H*chunks G M≤old.size) (measured : Reads old values M m) :
    Source (pull H S G M b base (.lookup old .row)) (lift (S:=S) values) M (result H S G M b base m) :=
  source_pull b base m room _ _ ⟨held,trivial⟩ (source_column old base held m _ space measured)

theorem shape_source (b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w) :
    Source (sourceShape H S G M b base) (shapeField (H:=H) (S:=S) (G:=G) b) M (result H S G M b base m) := by
  intro p
  have actual:=(row (H*S) G M p).isLt
  rw [sourceShape,get _ _ _ _ _ _ m room 1 _ (actual.trans_le (le_max_right ..))]
  simp [number,actual]

/-- Address of the raw receiver, useful for its scalar roster or geometry column. -/
theorem raw_eval (b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w)
    (x : Expr) (held : x.Fits w base) (p : Row (H*S) G M) :
    (rawAt H S G M b base x).eval (result H S G M b base m) ((row (H*S) G M p).val:Word w)=x.eval m (p.1.val:Word w) := by
  have actual:=(row (H*S) G M p).isLt
  rw [rawAt,eval_atRow,get _ _ _ _ _ _ m room 2 _ (actual.trans_le (le_max_right ..))]
  change x.eval _ (((row (H*S) G M p).val/chunks G M:ℕ):Word w)=_
  rw [(coordinates p).1]
  exact eval_below _ _ _ _ held (fun i hi=>(installed H S G M b base m room).2.2.1 i (.inl hi))

/-- The bare raw-host address can also read a true old scalar operand without an intervening
replicated scalar bank. -/
theorem old_scalar (G M b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w)
    (x : Expr) (held : x.Fits w base) (v : Fin (H*S)) :
    (oldScalar H S G M b base x).eval (result H S G M b base m) (v.val:Word w)=x.eval m ((owner v).val:Word w) := by
  rw [oldScalar,eval_atRow,get _ _ _ _ _ _ m room 3 _ (v.isLt.trans_le (le_max_left ..))]
  exact eval_below _ _ _ _ held (fun i hi=>(installed H S G M b base m room).2.2.1 i (.inl hi))

/-- The probe may be evaluated later, after publishing more dynamic source banks. Only the
fixed page addresses must have retained their values on the current date's memory. -/
def Retained (H S G M b base : ℕ) (before now : Memory w) : Prop :=
  ∀addr,base≤addr→addr<base+extent H S G M→now addr=(result H S G M b base before) addr

private theorem retained_value (t : Fin 5) (b base : ℕ) (old now : Memory w)
    (room : base+extent H S G M<2^w) (kept : Retained H S G M b base old now)
    (idx : ℕ) (inside : idx<count H S G M) :
    (value H S G M b base t).eval now (idx:Word w)=(value H S G M b base t).eval (result H S G M b base old) (idx:Word w) := by
  have ok:=table_fits H S G M b base room t
  have small : idx<(table H S G M b base t).size:=inside.trans_le (span_ge _)
  change (table H S G M b base t).read now (idx:Word w) =
    (table H S G M b base t).read (result H S G M b base old) (idx:Word w)
  rw [bank_read _ now small ok,bank_read _ _ small ok]
  exact kept _ ((Nat.le_add_right base _).trans (Nat.le_add_right ..))
    ((Nat.add_lt_add_left small _).trans_le ok.2.2)

theorem pull_retained (b base : ℕ) (before now : Memory w) (room : base+extent H S G M<2^w)
    (kept : Retained H S G M b base before now) (x : Expr) (values : Fin H→Fin G→Cell a)
    (measured : Source x values M now) :
    Source (pull H S G M b base x) (lift (S:=S) values) M now := by
  intro p
  rw [pull,eval_atRow,retained_value 0 b base before now room kept _ ((row (H*S) G M p).isLt.trans_le
    (le_max_right ..)),map_read b base before room p]
  exact measured (oldRow p)

theorem shape_retained (b base : ℕ) (before now : Memory w) (room : base+extent H S G M<2^w)
    (kept : Retained H S G M b base before now) :
    Source (sourceShape H S G M b base) (shapeField (H:=H) (S:=S) (G:=G) b) M now := by
  intro p
  exact (retained_value 1 b base before now room kept _
    ((row (H*S) G M p).isLt.trans_le (le_max_right ..))).trans (shape_source b base before room p)

/-- Reading a measured marker at a fixed common chunk from a scalar receiver-ordinal scan.
Only the leading packed offset depends on the raw receiver. -/
def atChunk (H S G M b base : ℕ) (c : Fin (chunks G M)) (x : Expr) :=
  x.atRow (.op .add (value H S G M b base 4) (.lit c.val))

theorem starts_mounted (b base : ℕ) (m : Memory w) (room : base+extent H S G M<2^w)
    (v : Fin (H*S)) :
    (result H S G M b base m) ((table H S G M b base 4).base+v.val)=((v.val*chunks G M:ℕ):Word w) := by
  have inside : v.val<count H S G M:=v.isLt.trans_le (le_max_left ..)
  have entry:=get H S G M b base m room 4 v.val inside
  change (table H S G M b base 4).read _ (v.val:Word w)=_ at entry
  rwa [bank_read _ _ (inside.trans_le (span_ge _)) (table_fits _ _ _ _ _ _ room 4)] at entry

/-- The chart can be reused after every dynamic contact sheet has been materialized. -/
theorem atChunk_eval (b base bound : ℕ) (mem : Memory w) (bankOK : (table H S G M b base 4).Fits w bound)
    (stored : ∀v : Fin (H*S),mem ((table H S G M b base 4).base+v.val)=((v.val*chunks G M:ℕ):Word w))
    (x : Expr) (c : Fin (chunks G M)) (v : Fin (H*S)) :
    (atChunk H S G M b base c x).eval mem (v.val:Word w)=
      x.eval mem ((row (H*S) G M (v,c)).val:Word w) := by
  have small : v.val<span (count H S G M):=v.isLt.trans_le ((le_max_left ..).trans (span_ge _))
  rw [atChunk,eval_atRow]
  apply congrArg (x.eval mem)
  change (table H S G M b base 4).read mem (v.val:Word w)+(c.val:Word w)=_
  rw [bank_read _ _ small bankOK,stored,←Nat.cast_add]
  exact congrArg (fun n : ℕ=>(n:Word w)) (by
    change v.val*chunks G M+c.val=c.val+chunks G M*v.val
    ac_rfl)

theorem atChunk_fits (b base bound : ℕ) (bankOK : (table H S G M b base 4).Fits w bound)
    (x : Expr) (ok : x.Fits w bound) (c : Fin (chunks G M)) :
    (atChunk H S G M b base c x).Fits w bound :=
  ProtocolRAM.Calendar.CatalogueRows.fits_atRow x _ ok ⟨⟨bankOK,trivial⟩,trivial⟩

theorem atChunk_work (b base : ℕ) (x : Expr) (c : Fin (chunks G M)) :
    (atChunk H S G M b base c x).work≤x.work*10 := by
  exact ProtocolRAM.Calendar.CatalogueRows.substitute_work x _

end
end Hierarchy.DescentContactProbePitch

end OAI
