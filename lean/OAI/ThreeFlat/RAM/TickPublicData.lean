import OAI.ThreeFlat.RAM.TickPrefix
import OAI.ThreeFlat.RAM.TickStageSpec

namespace OAI
/-! # Public operand allocation for the four linked procedures -/

namespace ThreeFlat.RAM.TickPublicData
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink TickStageSpec
open scoped Fin.CommRing
variable {w n m sz nr k : ℕ}

def count (n m : ℕ) := 4+(7+(n+m))
def control (n m : ℕ) (i : Fin 4) : Fin (count n m) := i.castAdd (7+(n+m))
def evaluator (n m : ℕ) (i : Fin 7) : Fin (count n m) := Fin.natAdd 4 (i.castAdd (n+m))
def navigator (n m : ℕ) (i : Fin n) : Fin (count n m) := Fin.natAdd 4 (Fin.natAdd 7 (i.castAdd m))
def preparer (n m : ℕ) (i : Fin m) : Fin (count n m) := Fin.natAdd 4 (Fin.natAdd 7 (Fin.natAdd n i))

def keys (n m : ℕ) : TickPrefix.Keys (count n m) :=
  ⟨control n m 0,control n m 1,control n m 2,control n m 3⟩

def data (q nt ns : ℕ) (ev : Fin 7 → Word w) (nav : Fin n → Word w) (prep : Fin m → Word w) :
    Fin (count n m) → Word w :=
  Fin.append ![(2+q : ℕ),(nt : Word w),(2+q+nt : ℕ),(ns : Word w)]
    (Fin.append ev (Fin.append nav prep))

theorem decode_params (q nt ns : ℕ) (ev : Fin 7 → Word w) (nav : Fin n → Word w) (prep : Fin m → Word w)
    (tb : 2+q+nt < 2^w) (ts : ns < 2^w) :
    let bank := data q nt ns ev nav prep
    let idx := keys n m
    (bank idx.teamBase).val=2+q ∧ (bank idx.teamWidth).val=nt ∧
      (bank idx.stepBase).val=2+q+nt ∧ (bank idx.stepWidth).val=ns := by
  dsimp only
  simp only [keys,control,data,Fin.append_left]
  change ((2+q : ℕ) : Word w).val = 2+q ∧ (nt : Word w).val = nt ∧
    ((2+q+nt : ℕ) : Word w).val = 2+q+nt ∧ (ns : Word w).val = ns
  simp only [Fin.val_cast_of_lt (show 2+q < 2^w by omega),Fin.val_cast_of_lt (show nt < 2^w by omega),
    Fin.val_cast_of_lt tb,Fin.val_cast_of_lt ts,and_self]

@[simp] theorem eval_read (q nt ns : ℕ) (ev : Fin 7 → Word w) (nav : Fin n → Word w)
    (prep : Fin m → Word w) (i : Fin 7) : data q nt ns ev nav prep (evaluator n m i)=ev i := by
  simp only [evaluator,data,Fin.append_right,Fin.append_left]

@[simp] theorem nav_read (q nt ns : ℕ) (ev : Fin 7 → Word w) (nav : Fin n → Word w)
    (prep : Fin m → Word w) (i : Fin n) : data q nt ns ev nav prep (navigator n m i)=nav i := by
  simp only [navigator,data,Fin.append_right,Fin.append_left]

@[simp] theorem prep_read (q nt ns : ℕ) (ev : Fin 7 → Word w) (nav : Fin n → Word w)
    (prep : Fin m → Word w) (i : Fin m) : data q nt ns ev nav prep (preparer n m i)=prep i := by
  simp only [preparer,data,Fin.append_right]

theorem admission_port {F : Type*} [Semiring F] (field : FieldCode F w) (b : Block w sz nr n)
    (small : Fin n → Word w) (full : Fin k → Word w) (select : Fin n → Fin k)
    (agree : ∀ j, full (select j)=small j) {pre ok : Memory w → Prop} {post : Memory w → Memory w → Prop}
    {time : ℕ} (run : Admission field b small pre ok post time) :
    Admission field (b.reindex (Function.Embedding.refl _) select) full pre ok post time := by
  intro pc r K M P R pub exit rom table c mem here init
  exact run M P ((Function.Embedding.refl _).trans R) (pub ∘ select) exit rom
    (fun j => (table (select j)).trans (agree j)) c mem here init

theorem prepare_port (b : Block w sz nr n) (small : Fin n → Word w) (full : Fin k → Word w)
    (select : Fin n → Fin k) (agree : ∀ j, full (select j)=small j) {pre : Memory w → Prop}
    {post : Memory w → Memory w → Prop} {time : ℕ} (run : Prepare b small pre post time) :
    Prepare (b.reindex (Function.Embedding.refl _) select) full pre post time := by
  intro pc r K M P R pub exit rom table c mem here init
  exact run M P ((Function.Embedding.refl _).trans R) (pub ∘ select) exit rom
    (fun j => (table (select j)).trans (agree j)) c mem here init

end ThreeFlat.RAM.TickPublicData

end OAI
