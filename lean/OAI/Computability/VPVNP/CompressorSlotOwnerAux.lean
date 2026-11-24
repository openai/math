import OAI.Computability.VPVNP.CompressorSlotOwnerAgreement
import OAI.Computability.VPVNP.CompressorSlotOwnerRuns

/-!
# Native initialization of the auxiliary endpoint owner tables

One eight-cell scan writes the selected layout's A, B, and D column offsets.
Another scan rotates the tag digit of each site, keeping its vertex and lane.
Both tables are produced by fixed straight-line programs, using one write per
cell and no external reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotOwners.Aux

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open Compression Compression.SurvivingSlots Slots SlotSchedule

variable {w : ℕ}

private abbrev wd (n : ℕ) : Word w := Fin.ofNat _ n
private abbrev div := @BinaryOp.eval w .div
private abbrev mod := @BinaryOp.eval w .mod
private abbrev xor := @BinaryOp.eval w .bitXor

private theorem val_wd {i : ℕ} (hi : i < 2^w) : (wd (w := w) i).val = i := Nat.mod_eq_of_lt hi

private theorem add_wd (a b : ℕ) : wd (w := w) a + wd b = wd (a+b) :=
  Fin.ext (Nat.add_mod a b (2^w)).symm

private theorem mul_wd (a b : ℕ) : wd (w := w) a * wd b = wd (a*b) :=
  Fin.ext (Nat.mul_mod a b (2^w)).symm

private theorem wd_val (b : Word w) : wd b.val = b := Fin.ext (Nat.mod_eq_of_lt b.isLt)

private theorem div_wd {a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    div (wd (w := w) a) (wd b) = wd (a/b) := by
  change Fin.ofNat _ ((wd a : Word w).val/(wd b : Word w).val) = _
  rw [val_wd ha, val_wd hb]

private theorem mod_wd {a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    mod (wd (w := w) a) (wd b) = wd (a%b) := by
  change Fin.ofNat _ ((wd a : Word w).val%(wd b : Word w).val) = _
  rw [val_wd ha, val_wd hb]

/-- The edge type has two binary digits. Its incoming end has role D precisely
when the digits differ. Its outgoing end has role D only on the last type. -/
def roleCode : List (Op 10 2) :=
  [.stateWord 0, .constant 1 1, .constant 2 2, .publicWord 3 0,
   .binary .mod 4 0 2, .binary .div 5 0 2, .binary .mod 6 5 2, .binary .div 7 5 2,
   .binary .sub 5 2 3, .binary .bitXor 8 6 7, .binary .mul 8 8 5, .binary .add 8 3 8,
   .binary .mul 6 6 5, .binary .add 6 3 6, .binary .sub 9 1 3, .binary .sub 6 6 9,
   .binary .mul 6 7 6, .binary .add 6 9 6, .binary .sub 8 8 6, .binary .mul 8 4 8,
   .binary .add 8 6 8, .publicWord 9 1, .binary .add 9 9 0, .write 9 8, .binary .add 0 0 1]

private def choose (b x y : Word w) := x + b*(y-x)

/-- Select the role-site offset for an edge type and endpoint side in the chosen layout, using
the low cursor bit for the side. -/
def roleValue (l i : Word w) : Word w :=
  let side := mod i 2
  let t := div i 2
  let low := mod t 2
  let high := div t 2
  let dst := choose (xor low high) l 2
  let src := choose high (1-l) (choose low l 2)
  choose side src dst

private def oneWrite (n : ℕ) (a v : Word w) : List (Event w) :=
  List.replicate n .tick ++ [.write a v, .tick]

private theorem oneWrite_after (n : ℕ) (a v : Word w) (m : Memory w) :
    after m (oneWrite n a v) = writeMemory m a v := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem oneWrite_work (n : ℕ) (a v : Word w) :
    countProbes (oneWrite n a v) = 1 ∧ (oneWrite n a v).length = n+2 := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [oneWrite, List.replicate_succ, List.cons_append, countProbes, List.length_cons]
    exact ⟨ih.1, by change (oneWrite n a v).length+1 = _; omega⟩

theorem role_native (p : Fin 2 → Word w) (m : Memory w) (i : Word w) :
    let M := (template roleCode 0).instantiate w p
    execute M.program 26 (M.program.start i) m [] = some
      ⟨oneWrite 23 (p 1+i) (roleValue (p 0) i), some (i+1)⟩ := by
  let M := (template roleCode 0).instantiate w p
  change execute M.program (1+roleCode.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]; rfl

open scoped Fin.CommRing in
/-- The program implements the selected layout's outgoing and incoming roles
on all eight entries of the finite role table. -/
theorem roleValue_eq (layout : Bool) (t : Fin 4) (s : Fin 2) (hw : 8 ≤ 2^w) :
    roleValue (wd (w := w) layout.toNat) (wd (2*t.val+s.val)) =
      wd (roleOffset (endRole layout (decide (s=1)) t)) := by
  have h2 : 2 < 2^w := by omega
  have hs : s.val < 2 := s.isLt
  have ht : t.val < 4 := t.isLt
  have hfield : 2*t.val+s.val < 2^w := by omega
  have hlt : t.val < 2^w := by omega
  have modField : (2*t.val+s.val)%2 = s.val := by omega
  have divField : (2*t.val+s.val)/2 = t.val := by omega
  change choose (mod (wd _) (wd 2)) (choose (div (div (wd _) (wd 2)) (wd 2)) _
    (choose (mod (div (wd _) (wd 2)) (wd 2)) _ _))
    (choose (xor (mod (div (wd _) (wd 2)) (wd 2)) (div (div (wd _) (wd 2)) (wd 2))) _ _) = _
  rw [div_wd hfield h2, mod_wd hfield h2, modField, divField, div_wd hlt h2, mod_wd hlt h2]
  have hx : xor (wd (w := w) (t.val%2)) (wd (t.val/2)) = wd ((t.val%2) ^^^ (t.val/2)) := by
    change Fin.ofNat _ ((wd (t.val%2) : Word w).val ^^^ (wd (t.val/2) : Word w).val) = _
    rw [val_wd (by omega : t.val%2 < 2^w), val_wd (by omega : t.val/2 < 2^w)]
  rw [hx]
  fin_cases t <;> fin_cases s <;> cases layout <;>
    simp [endRole, sourceRole, targetRole, roleOffset, choose, wd]

/-- Public fields give lane count, tag count and cyclic successor table start. -/
def nextCode : List (Op 9 3) :=
  [.stateWord 0, .constant 1 1, .publicWord 2 0, .publicWord 3 1,
   .binary .mod 4 0 2, .binary .div 5 0 2, .binary .mod 6 5 3, .binary .div 7 5 3,
   .binary .add 6 6 1, .binary .mod 6 6 3, .binary .mul 7 7 3, .binary .add 7 7 6,
   .binary .mul 7 7 2, .binary .add 7 7 4, .publicWord 8 2, .binary .add 8 8 0,
   .write 8 7, .binary .add 0 0 1]

/-- Compute a packed site's cyclic successor by advancing its tag modulo the tag count at the
same base vertex and residual lane. -/
def nextValue (p : Fin 3 → Word w) (i : Word w) : Word w :=
  let base := div i (p 0)
  (div base (p 1)*p 1 + mod (mod base (p 1)+1) (p 1))*p 0 + mod i (p 0)

theorem next_native (p : Fin 3 → Word w) (m : Memory w) (i : Word w) :
    let M := (template nextCode 0).instantiate w p
    execute M.program 19 (M.program.start i) m [] = some
      ⟨oneWrite 16 (p 2+i) (nextValue p i), some (i+1)⟩ := by
  let M := (template nextCode 0).instantiate w p
  change execute M.program (1+nextCode.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]; rfl

variable {V Tag L : Type*} {N J nL : ℕ}
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- Numeric cycle with the same original vertex and lane even when the tag wraps. -/
theorem nextValue_eq (p : Fin 3 → Word w) (b : Fin (N*(J*nL)))
    (hl : (p 0).val = nL) (ht : (p 1).val = J) (fit : N*(J*nL) ≤ 2^w) :
    let site := siteIndex vertices tags lanes
    nextValue p (wd b.val) = wd (site (dummyEnd tags true (site.symm b))).val := by
  intro site
  obtain ⟨⟨v,t,l⟩,rfl⟩ := site.surjective b
  let vertex := (vertices v).val
  let tag := (tags t).val
  let lane := (lanes l).val
  have hi : (site (v,t,l)).val = (vertex*J+tag)*nL+lane := by
    change lane+nL*tag+(J*nL)*vertex = _; ring
  have htag : tag < J := (tags t).isLt
  have hlane : lane < nL := (lanes l).isLt
  have hcap := (site (v,t,l)).isLt.trans_le fit
  have hlw : nL < 2^w := hl ▸ (p 0).isLt
  have htw : J < 2^w := ht ▸ (p 1).isLt
  have hp0 : p 0 = wd nL := hl ▸ (wd_val (p 0)).symm
  have hp1 : p 1 = wd J := ht ▸ (wd_val (p 1)).symm
  have lower (b m u : ℕ) (hu : u < m) : (b*m+u)/m = b := by
    rw [Nat.mul_comm b m, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hu, Nat.add_zero]
  have hb : vertex*J+tag < 2^w := by
    have := (Nat.div_le_self (site (v,t,l)).val nL).trans_lt hcap
    rwa [hi, lower _ _ _ hlane] at this
  rw [Equiv.symm_apply_apply]
  change nextValue p (wd (site (v,t,l)).val) = wd (site (v,tags.symm (finRotate J (tags t)),l)).val
  have he : (site (v,tags.symm (finRotate J (tags t)),l)).val =
      (vertex*J+(finRotate J (tags t)).val)*nL+lane := by
    change lane+nL*(tags (tags.symm _)).val+(J*nL)*vertex = _
    rw [tags.apply_symm_apply]; ring
  let := (tags t).neZero
  rw [he, finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  simp only [nextValue, hp0, hp1, hi]
  rw [div_wd (hi ▸ hcap) hlw, mod_wd (hi ▸ hcap) hlw, lower _ _ _ hlane, Nat.mul_add_mod_of_lt hlane,
    div_wd hb htw, mod_wd hb htw, lower _ _ _ htag, Nat.mul_add_mod_of_lt htag]
  change (wd vertex * wd J + mod (wd tag + wd 1) (wd J))*wd nL+wd lane = _
  rw [add_wd, mod_wd (by omega : tag+1 < 2^w) htw, mul_wd, add_wd, mul_wd, add_wd]

private theorem direct_run {C : Type*} (P : Program w C) (fuel n count : ℕ) (base : Word w)
    (value : Word w → Word w) (initial : Memory w) (fit : base.val+count ≤ 2^w)
    (visit : ∀ (m : Memory w) (i : Word w), execute P fuel (P.start i) m [] =
      some ⟨oneWrite n (base+i) (value i), some (i+1)⟩) :
    ∃ rs, FilledRun P fuel 1 (n+2) count base (fun i => value (wd i)) initial rs := by
  apply filled_run _ _ _ _ _ _ _ _ fit
  intro i _ _ m _
  have hnext : wd (w := w) i + 1 = wd (i+1) := add_wd i 1
  have hadd : base + wd i = wd (base.val+i) := by
    simpa only [wd_val] using add_wd (w := w) base.val i
  exact ⟨_, (visit m (wd i)).trans (by rw [hnext]), (oneWrite_after ..).trans (by rw [hadd]),
    (oneWrite_work ..).1, (oneWrite_work ..).2⟩

/-- Fill the finite role table. Its final cells are the role offsets needed
by the selected layout, with the outgoing cell first in each pair. -/
theorem roles_run (layout : Bool) (p : Fin 2 → Word w) (initial : Memory w)
    (hl : p 0 = wd layout.toNat) (fit : (p 1).val+8 ≤ 2^w) :
    let P := ((template roleCode 0).instantiate w p).program
    ∃ rs, FilledRun P 26 1 25 8 (p 1) (fun i => roleValue (p 0) (wd i)) initial rs ∧
      ∀ (t : Fin 4) (s : Fin 2), (after initial (eventLog rs) ((p 1).val+(2*t.val+s.val))).val =
        roleOffset (endRole layout (decide (s=1)) t) := by
  intro P
  obtain ⟨rs,hr⟩ := direct_run P 26 23 8 (p 1) (roleValue (p 0)) initial fit (role_native p)
  refine ⟨rs,hr,fun t s => ?_⟩
  have hi : 2*t.val+s.val < 8 := by have := t.isLt; have := s.isLt; omega
  rw [hr.filled _ hi, hl, roleValue_eq _ _ _ (by omega), val_wd (by have := role_lt' (endRole layout (decide (s=1)) t); omega)]
where
  role_lt' (r : PackedRole) : roleOffset r < 3 := by cases r <;> decide

/-- Build the entire cyclic successor table directly from the two radices.
The result satisfies the input predicate used by the native dummy worker. -/
theorem next_run (p q : Fin 3 → Word w) (initial : Memory w)
    (hl : (p 0).val = nL) (ht : (p 1).val = J) (pad : ℕ) (hp : (q 0).val = pad)
    (start : q 1 = p 2) (hw : 2 < 2^w) (fit : (p 2).val+N*(J*nL) ≤ 2^w) :
    let P := ((template nextCode 0).instantiate w p).program
    ∃ rs, FilledRun P 19 1 18 (N*(J*nL)) (p 2) (fun i => nextValue p (wd i)) initial rs ∧
      DummyTables vertices tags lanes pad q (after initial (eventLog rs)) := by
  intro P
  obtain ⟨rs,hr⟩ := direct_run P 19 16 _ (p 2) (nextValue p) initial fit (next_native p)
  refine ⟨rs,hr,hw,hp,start ▸ fit,fun b => ?_⟩
  rw [start, hr.filled _ b.isLt, nextValue_eq vertices tags lanes p b hl ht (by omega)]
  exact val_wd ((siteIndex vertices tags lanes _).isLt.trans_le (by omega))

end CompressorRecords.SlotOwners.Aux

end VPVNP
end Computability
end OAI
