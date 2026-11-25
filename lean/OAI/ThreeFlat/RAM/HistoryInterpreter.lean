import OAI.ThreeFlat.RAM.HistoryFactors
import OAI.ThreeFlat.RAM.ExpressionContraction
import OAI.ThreeFlat.BlankNetwork

namespace OAI
/-! # Native contraction of the selected compact history factors -/

namespace ThreeFlat.RAM.HistoryFactors

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM BitLayout Contraction DescriptorScan
  DescriptorExpr GeneratedContraction HistoryFactorScan Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}

omit [Fintype F] [Field F] in
/-- The read-only compact tables can occupy any two bounded regions beyond
the cell-generation interval. -/
private theorem Stores.stable {N : BitNetwork F p} {L : Library N} {code : FieldCode F w}
    {metadata lut : ℕ} {m input : Memory w} (s : Stores N L code metadata lut input)
    (hm : mulBase p N.internal N.cells ≤ metadata) (hl : mulBase p N.internal N.cells ≤ lut)
    (a : agreesOutside (cellsBase p N.internal) (mulBase p N.internal N.cells) m input) :
    Stores N L code metadata lut m := by
  constructor
  · intro i j
    exact (a _ (Or.inr (by omega))).trans (s.source i j)
  · intro i
    exact (a _ (Or.inr (by omega))).trans (s.tag i)
  · intro t j
    exact (a _ (Or.inr (by omega))).trans (s.coefficient t j)

def reader (p hidden metadata lut : ℕ) : Term w (2+(5+0)) 1 :=
  readCellWord (cellsBase p hidden : Word w) (metadata : Word w) (lut : Word w)

/-- Transport just the finite sizes of the machine, preserving its instructions. -/
def resize {a b A B k : ℕ} (M : Machine w a b k) (ha : a=A) (hb : b=B) :
    Machine w A B k := ha ▸ hb ▸ M

private theorem value_resize {G : Type*} [Semiring G] {a b A B k : ℕ}
    (M : Machine w a b k) (ha : a=A) (hb : b=B) (code : FieldCode G w)
    (fuel : ℕ) (s : Word w) (m : Memory w) :
    value code (resize M ha hb) fuel s m = value code M fuel s m := by
  subst A B
  rfl

private theorem reader_binds (p h metadata lut : ℕ) :
    (reader (w:=w) p h metadata lut).binds = 22 := binds_readCellWord _ _ _

/-- The instruction table and public constants depend on the capacities and bases
only. The selected factors, source addresses and coefficient values are memory data. -/
noncomputable def interpreter (p hidden cells metadata lut : ℕ)
    (fit : Fits (BitNetwork.blankNetwork (F := F) p hidden cells) w) : Machine w 108 36 7 :=
  let e := reader (w:=w) p hidden metadata lut
  let M := GeneratedContraction.machine (BitNetwork.blankNetwork (F := F) p hidden cells) fit
    e.first (expressionRows e) (Fin.elim0 : Fin 0 → Word w)
  have n : e.binds = 22 := reader_binds p hidden metadata lut
  resize M (show e.labels+(6+35) = 108 by rw [Term.labels_eq,n])
    (show 4+(10+e.binds) = 36 by rw [n])

/-- The shared finite instruction table sums one native branch per assignment of
private bits. Its work is linear in the fixed hidden-bit and factor capacities. -/
theorem value_interpreter (N : BitNetwork F p) (fit : Fits N w) (L : Library N)
    (metadata lut : ℕ) (hm : mulBase p N.internal N.cells ≤ metadata)
    (hl : mulBase p N.internal N.cells ≤ lut)
    (bm : metadata+4*N.cells ≤ 2^w) (bl : lut+8*L.count ≤ 2^w)
    (input : Memory w) (stored : Stores N L (codec N fit) metadata lut input)
    (pin : Fin p → Bool) (initial : Fin N.internal → Bool)
    (outside : ∀ a < footprint N, a < cellsBase p N.internal ∨ mulBase p N.internal N.cells ≤ a →
      input a = memory N (codec N fit) pin initial a)
    (s : Word w) (extra : ℕ) :
    value (codec N fit) (interpreter p N.internal N.cells metadata lut (F := F) fit)
      (extra+13+5*N.internal+550*N.cells) s input = N.eval pin := by
  let e := reader (w:=w) p N.internal metadata lut
  have bounds : e.binds = 22 := binds_readCellWord _ _ _
  have cost : extra+13+5*N.internal+550*N.cells =
      extra+13+5*N.internal+22*N.cells+(11*N.cells)*(2*e.binds+4) := by rw [bounds]; omega
  unfold interpreter
  simp only [value_resize]
  rw [cost]
  apply value_eq_expression N fit e Fin.elim0 pin initial input s extra _ outside
  intro params a m hstart hend preserved
  let delta := a.val - cellsBase p N.internal
  have hd : cellsBase p N.internal + delta = a.val := Nat.add_sub_of_le hstart
  have ends : a.val < cellsBase p N.internal + 11*N.cells := hend
  let i : Fin N.cells := ⟨delta/11, by omega⟩
  let j : Fin 11 := ⟨Nat.mod delta 11, Nat.mod_lt delta (by decide : 0 < 11)⟩
  have ha : cellsBase p N.internal + 11*i.val+j.val = a.val := by
    rw [Nat.add_assoc]
    exact (congrArg (cellsBase p N.internal + ·) (Nat.div_add_mod delta 11)).trans hd
  have wordeq : ((cellsBase p N.internal + 11*i.val+j.val : ℕ) : Word w) = a := by
    rw [ha]
    exact Fin.cast_val_eq_self _
  change (readCellWord (cellsBase p N.internal : Word w) (metadata : Word w)
    (lut : Word w)).eval params m (fun _ => a) = _
  rw [eval_readCellWord]
  calc
    _ = record N (codec N fit) i j := by
      rw [← wordeq]
      exact read_record_eq N fit L _ _ _ m bm bl (stored.stable hm hl preserved) i j
    _ = memory N (codec N fit) pin initial (cellsBase p N.internal + 11*i.val+j.val) :=
      (BitLayout.read_record N _ _ _ i j).symm
    _ = _ := congrArg _ ha

end ThreeFlat.RAM.HistoryFactors

end OAI
