import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Data.ZMod.Defs

/-!
# Computing endpoint owners in absolute field order

A genuine candidate has an edge type, an original base arc, a subdivision index,
an absolute source lane, and an endpoint side. The scan reads one selected role
from the layout table and follows it to the packed site in the original arc
record. Each missing candidate receives its own auxiliary owner. A separate
scan handles the contiguous dummy fields and uses the cyclic next-site table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotOwners

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

private abbrev divWord := @BinaryOp.eval w .div
private abbrev modWord := @BinaryOp.eval w .mod

/-- Public words are the number of lanes, sum of subdivision counts, number of old
base arcs, starts of the old arc records, role table and subdivision table,
number of real endpoint owners, and start of the output. -/
def genuine : List (Op 16 8) :=
  [.stateWord 0, .constant 1 1, .constant 2 2, .binary .mod 3 0 2,
   .binary .div 4 0 2, .publicWord 5 0, .binary .mod 6 4 5, .binary .div 4 4 5,
   .publicWord 7 1, .binary .mod 8 4 7, .binary .div 4 4 7, .publicWord 7 2,
   .binary .mod 9 4 7, .binary .div 10 4 7, .binary .mul 9 9 5, .binary .add 9 9 6,
   .binary .add 11 2 2, .binary .mul 9 11 9, .publicWord 11 3, .binary .add 9 11 9,
   .publicWord 11 4, .binary .mul 12 2 10, .binary .add 12 12 3, .binary .add 12 11 12,
   .read 12 12, .binary .add 12 9 12, .read 12 12,
   .constant 13 3, .binary .add 13 9 13, .read 13 13,
   .publicWord 14 5, .binary .add 14 14 10, .read 14 14,
   .binary .add 8 8 1, .binary .div 14 14 8, .binary .div 14 14 14, .binary .mul 13 13 14,
   .binary .mul 12 2 12, .binary .add 12 12 3,
   .publicWord 15 6, .binary .add 15 15 0, .binary .sub 12 12 15,
   .binary .mul 12 13 12, .binary .add 12 15 12, .publicWord 15 7, .binary .add 15 15 0,
   .write 15 12, .binary .add 0 0 1]

/-- The decoded side, role edge type, subdivision, and absolute old arc used to classify one
genuine candidate field. -/
structure Digits (α : Type) where
  /-- Endpoint bit of the candidate field, zero for the outgoing side and one for the incoming
  side. -/
  side : α
  /-- Index of the role edge type used to select the endpoint roles and subdivision limit. -/
  edgeType : α
  /-- Candidate subdivision index to compare with the selected edge type's subdivision count. -/
  subdivision : α
  /-- Absolute old arc index, with the residual lane as its least significant digit. -/
  oldArc : α

/-- The original arc keeps its lane as its least significant digit, even though
the subdivision digit lies between the old base arc and lane in the candidate ID. -/
def digits (p : Fin 8 → Word w) (i : Word w) : Digits (Word w) :=
  let arc := divWord i 2
  let key := divWord arc (p 0)
  let typeAndBase := divWord key (p 1)
  ⟨modWord i 2, divWord typeAndBase (p 2), modWord key (p 1),
    modWord typeAndBase (p 2) * p 0 + modWord arc (p 0)⟩

/-- Address of the role selector for the candidate's edge type and endpoint side. -/
def roleAddress (p : Fin 8 → Word w) (f : Digits (Word w)) := p 4 + (2 * f.edgeType + f.side)

/-- Start of the candidate's four-word old arc record, containing the role sites and CD flag. -/
def oldAddress (p : Fin 8 → Word w) (f : Digits (Word w)) := p 3 + ((2+2) * f.oldArc)

/-- Address of the subdivision count for the candidate's role edge type. -/
def subdivAddress (p : Fin 8 → Word w) (f : Digits (Word w)) := p 5 + f.edgeType

private def below (j n : Word w) : Word w :=
  let q := divWord n (j+1)
  divWord q q

private def select (b x y : Word w) : Word w := x + b * (y-x)

/-- Word written for a genuine candidate, including candidates that decode to holes. -/
def genuineOwner (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : Word w :=
  let f := digits p i
  let a := oldAddress p f
  let site := m (a + m (roleAddress p f).val).val
  let cd := m (a+3).val
  let n := m (subdivAddress p f).val
  select (cd * below f.subdivision n) (p 6+i) (2*site+f.side)

/-- Trace of one genuine candidate visit, reading its role selector, site, CD flag, and
subdivision count before writing its owner. -/
def genuineEvents (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let f := digits p i
  let role := roleAddress p f
  let a := oldAddress p f
  let site := a + m role.val
  let cd := a+3
  let n := subdivAddress p f
  List.replicate 24 .tick ++ [.read role (m role.val), .tick, .read site (m site.val),
    .tick, .tick, .read cd (m cd.val), .tick, .tick, .read n (m n.val)] ++
    List.replicate 13 .tick ++ [.write (p 7+i) (genuineOwner p m i), .tick]

theorem genuine_after (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    after m (genuineEvents p m i) = writeMemory m (p 7+i) (genuineOwner p m i) := rfl

theorem genuine_work (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    (genuineEvents p m i).length = 48 ∧ countProbes (genuineEvents p m i) = 5 := ⟨rfl,rfl⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
private theorem genuine_trace (p : Fin 8 → Word w) (m : Memory w) (i : Word w) (rs : Regs w 16) :
    ∃ rs', trace p i genuine rs m = some (genuineEvents p m i, rs', after m (genuineEvents p m i)) ∧
      rs' 0 = i+1 := by
  simp (config := {decide := true}) [genuine, trace, Op.effect, Function.update, BinaryOp.eval,
    genuineEvents, genuineOwner, roleAddress, oldAddress, subdivAddress, digits, below, select,
    divWord, modWord]
  repeat' apply And.intro
  all_goals rfl

/-- Four table reads and one write compute the next genuine field. -/
theorem genuine_native (p : Fin 8 → Word w) (m : Memory w) (i : Word w) :
    let M := (template genuine 0).instantiate w p
    execute M.program 49 (M.program.start i) m [] = some ⟨genuineEvents p m i, some (i+1)⟩ := by
  obtain ⟨rs, ht, hr⟩ := genuine_trace p m i (fun _ => 0)
  let M := (template genuine 0).instantiate w p
  change execute M.program (1 + genuine.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]; simp [hr]

/-- Dummy public words are the padding degree, cyclic next-site table start, and
start of the dummy output interval. Each dummy pass starts its cursor at zero. -/
def dummy : List (Op 8 3) :=
  [.stateWord 0, .constant 1 1, .constant 2 2, .binary .div 3 0 2, .binary .mod 4 0 2,
   .publicWord 5 0, .binary .div 3 3 5, .publicWord 5 1, .binary .add 5 5 3, .read 6 5,
   .binary .sub 6 6 3, .binary .mul 6 4 6, .binary .add 6 3 6, .binary .mul 6 2 6,
   .binary .add 6 6 4, .publicWord 7 2, .binary .add 7 7 0, .write 7 6, .binary .add 0 0 1]

/-- Recover the padding arc's source site from its field cursor by removing the side and
dummy-slot digits. -/
def dummySource (p : Fin 3 → Word w) (i : Word w) := divWord (divWord i 2) (p 0)

/-- Encode the source site and outgoing side for a dummy source field or the cyclic successor
and incoming side for its target field. -/
def dummyOwner (p : Fin 3 → Word w) (m : Memory w) (i : Word w) :=
  let s := dummySource p i
  let side := modWord i 2
  2 * select side s (m (p 1+s).val) + side

/-- Trace of one dummy field visit, reading the source site's cyclic successor and writing the
selected endpoint owner. -/
def dummyEvents (p : Fin 3 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let a := p 1 + dummySource p i
  List.replicate 9 .tick ++ [.read a (m a.val)] ++ List.replicate 7 .tick ++
    [.write (p 2+i) (dummyOwner p m i), .tick]

theorem dummy_after (p : Fin 3 → Word w) (m : Memory w) (i : Word w) :
    after m (dummyEvents p m i) = writeMemory m (p 2+i) (dummyOwner p m i) := rfl

theorem dummy_work (p : Fin 3 → Word w) (m : Memory w) (i : Word w) :
    (dummyEvents p m i).length = 19 ∧ countProbes (dummyEvents p m i) = 2 := ⟨rfl,rfl⟩

/-- One next-site read and one write compute the dummy field. -/
theorem dummy_native (p : Fin 3 → Word w) (m : Memory w) (i : Word w) :
    let M := (template dummy 0).instantiate w p
    execute M.program 20 (M.program.start i) m [] = some ⟨dummyEvents p m i, some (i+1)⟩ := by
  let M := (template dummy 0).instantiate w p
  change execute M.program (1 + dummy.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  rfl

/-- Natural-number decoding in the same mixed radices as the genuine arc address. -/
def natDigits (lanes subdivisions oldBases field : ℕ) : Digits ℕ :=
  let arc := field / 2
  let key := arc / lanes
  let typeAndBase := key / subdivisions
  ⟨field % 2, typeAndBase / oldBases, key % subdivisions,
    (typeAndBase % oldBases) * lanes + arc % lanes⟩

private theorem div_val (x y : Word w) : (divWord x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem mod_val (x y : Word w) : (modWord x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)

private theorem two_val (hw : 2 < 2^w) : (2 : Word w).val = 2 :=
  Nat.mod_eq_of_lt hw

private theorem below_eq (j n : Word w) (hj : j.val + 1 < 2^w) :
    below j n = if j.val < n.val then 1 else 0 := by
  have hs : (j+1).val = j.val + 1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2^w), Nat.mod_eq_of_lt hj]
  apply Fin.ext
  simp only [below, div_val, hs]
  by_cases h : j.val < n.val
  · rw [ite_eq_left h, Nat.div_self (Nat.div_pos h (Nat.zero_lt_succ _)),
      Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, Nat.div_eq_of_lt (by omega : n.val < j.val+1)]; rfl

/-- Input words and lookup addresses used by one genuine field. The old record
has three packed sites and a CD indicator. The role lookup always chooses one
of the three site fields, even on a candidate that ultimately becomes a hole. -/
structure GenuineInput (p : Fin 8 → Word w) (m : Memory w) (i : Word w) : Prop where
  twoFits : 2 < 2^w
  subdivPositive : 0 < (p 1).val
  oldFits : let f := natDigits (p 0).val (p 1).val (p 2).val i.val
            (p 3).val + 4*f.oldArc + 3 < 2^w
  roleFits : let f := natDigits (p 0).val (p 1).val (p 2).val i.val
             (p 4).val + (2*f.edgeType + f.side) < 2^w
  subdivFits : let f := natDigits (p 0).val (p 1).val (p 2).val i.val
               (p 5).val + f.edgeType < 2^w
  roleValid : let f := natDigits (p 0).val (p 1).val (p 2).val i.val
              (m ((p 4).val + (2*f.edgeType + f.side))).val < 3
  cdBit : let f := natDigits (p 0).val (p 1).val (p 2).val i.val
          (m ((p 3).val + 4*f.oldArc + 3)).val ≤ 1

/-- Numeric owner prior to conversion to a RAM word. The hole owner is unique
to the absolute field and starts just beyond the real endpoint owners. -/
def natGenuineOwner (p : Fin 8 → Word w) (m : Memory w) (i : ℕ) : ℕ :=
  let f := natDigits (p 0).val (p 1).val (p 2).val i
  let base := (p 3).val + 4*f.oldArc
  let role := (m ((p 4).val + (2*f.edgeType + f.side))).val
  if (m (base+3)).val = 1 ∧ f.subdivision < (m ((p 5).val+f.edgeType)).val
  then 2*(m (base+role)).val + f.side
  else (p 6).val+i

open scoped Fin.CommRing in
/-- With fitting addresses the native word implements the numerical decoder,
including both reasons a genuine candidate can be absent. -/
theorem genuineOwner_eq (p : Fin 8 → Word w) (m : Memory w) (i : Word w)
    (h : GenuineInput p m i) : genuineOwner p m i = Fin.ofNat _ (natGenuineOwner p m i.val) := by
  let f := natDigits (p 0).val (p 1).val (p 2).val i.val
  let g := digits p i
  let base := (p 3).val + 4*f.oldArc
  let r := (p 4).val + (2*f.edgeType + f.side)
  let n := (p 5).val + f.edgeType
  have hbase : base + 3 < 2^w := h.oldFits
  have hr : r < 2^w := h.roleFits
  have hn : n < 2^w := h.subdivFits
  have hrole : (m r).val < 3 := h.roleValid
  have hbit : (m (base+3)).val ≤ 1 := h.cdBit
  have hw := two_val h.twoFits
  have hd : g.side.val = f.side ∧ g.edgeType.val = f.edgeType ∧
      g.subdivision.val = f.subdivision ∧ g.oldArc.val = f.oldArc := by
    have hOld : f.oldArc < 2^w := by dsimp only [base] at hbase; omega
    simp only [g, digits, mod_val, div_val, hw, Fin.val_add, Fin.val_mul, Nat.mod_add_mod]
    exact ⟨rfl, rfl, rfl, Nat.mod_eq_of_lt hOld⟩
  obtain ⟨hs,ht,hj,ho⟩ := hd
  have haddr : (oldAddress p g).val = base := by
    simp only [oldAddress, Fin.val_add, Fin.val_mul, hw, ho, Nat.mod_mul_mod, Nat.add_mod_mod]
    exact Nat.mod_eq_of_lt (by omega : base < 2^w)
  have hraddr : (roleAddress p g).val = r := by
    simp only [roleAddress, Fin.val_add, Fin.val_mul, hw, hs, ht, Nat.mod_add_mod, Nat.add_mod_mod]
    exact Nat.mod_eq_of_lt hr
  have hnaddr : (subdivAddress p g).val = n := by
    rw [subdivAddress, Fin.val_add, ht, Nat.mod_eq_of_lt hn]
  have hcaddr : (oldAddress p g+3).val = base+3 := by
    have hthree : (3 : Word w).val = 3 := Nat.mod_eq_of_lt (by omega : 3 < 2^w)
    rw [Fin.val_add, haddr, hthree, Nat.mod_eq_of_lt hbase]
  have hsaddr : (oldAddress p g + m r).val = base + (m r).val := by
    rw [Fin.val_add, haddr, Nat.mod_eq_of_lt (by omega)]
  have hsub : f.subdivision < (p 1).val := Nat.mod_lt _ h.subdivPositive
  have hjfit : g.subdivision.val + 1 < 2^w := by rw [hj]; have := (p 1).isLt; omega
  change select (m (oldAddress p g+3).val * below g.subdivision (m (subdivAddress p g).val))
    (p 6+i) (2*m (oldAddress p g+m (roleAddress p g).val).val+g.side) = _
  rw [hcaddr, hnaddr, below_eq _ _ hjfit, hj, hraddr, hsaddr]
  change _ = Fin.ofNat _ (if (m (base+3)).val = 1 ∧ f.subdivision < (m n).val
    then 2*(m (base+(m r).val)).val+f.side else (p 6).val+i.val)
  have hole : p 6+i = Fin.ofNat _ ((p 6).val + i.val) := rfl
  have real : 2*m (base+(m r).val)+g.side = Fin.ofNat _ (2*(m (base+(m r).val)).val+f.side) := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_mul, hw, hs, Nat.mod_add_mod]; rfl
  by_cases hc : (m (base+3)).val = 1
  · have hc' : m (base+3) = 1 := Fin.ext (hc.trans (Nat.mod_eq_of_lt (by omega)).symm)
    by_cases hj' : f.subdivision < (m n).val
    · rw [ite_eq_left hj', ite_eq_left (c := (m (base+3)).val = 1 ∧ f.subdivision < (m n).val) ⟨hc,hj'⟩, hc', one_mul]
      simpa only [select, one_mul, add_sub_cancel] using real
    · rw [ite_eq_right hj', ite_eq_right (c := (m (base+3)).val = 1 ∧ f.subdivision < (m n).val) (fun a => hj' a.2), hc', mul_zero]
      simpa only [select, zero_mul, add_zero] using hole
  · have hc' : m (base+3) = 0 := Fin.ext (by change _ = 0; omega)
    rw [ite_eq_right (c := (m (base+3)).val = 1 ∧ f.subdivision < (m n).val) (fun a => hc a.1), hc', zero_mul]
    simpa only [select, zero_mul, add_zero] using hole

/-- The dummy source is recovered by stripping the side and padding-copy
digits. The incoming field reads the next site in the cyclic tag order. -/
def natDummyOwner (p : Fin 3 → Word w) (m : Memory w) (i : ℕ) : ℕ :=
  let s := i / 2 / (p 0).val
  let side := i % 2
  2 * (if side = 0 then s else (m ((p 1).val+s)).val) + side

open scoped Fin.CommRing in
theorem dummyOwner_eq (p : Fin 3 → Word w) (m : Memory w) (i : Word w)
    (hw : 2 < 2^w) (hfit : (p 1).val + i.val / 2 / (p 0).val < 2^w) :
    dummyOwner p m i = Fin.ofNat _ (natDummyOwner p m i.val) := by
  let s := i.val / 2 / (p 0).val
  have htwo := two_val hw
  have hs : (dummySource p i).val = s := by rw [dummySource, div_val, div_val, htwo]
  have ha : (p 1+dummySource p i).val = (p 1).val+s := by rw [Fin.val_add, hs, Nat.mod_eq_of_lt hfit]
  have hside : (modWord i 2).val = i.val % 2 := by rw [mod_val, htwo]
  have he : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases he with h | h
  · have hz : modWord i 2 = 0 := Fin.ext (hside.trans h)
    simp only [dummyOwner, hz, select, zero_mul, add_zero, natDummyOwner, h, ite_true]
    apply Fin.ext
    rw [Fin.val_mul, htwo, hs]; rfl
  · have hu : modWord i 2 = 1 := Fin.ext ((hside.trans h).trans (Nat.mod_eq_of_lt (by omega)).symm)
    simp only [dummyOwner, hu, select, one_mul, add_sub_cancel, ha, natDummyOwner, h, Nat.one_ne_zero,
      ite_false]
    apply Fin.ext
    rw [Fin.val_add, Fin.val_mul, htwo, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < 2^w),
      Nat.mod_add_mod]; rfl

end CompressorRecords.SlotOwners

end VPVNP
end Computability
end OAI
