import OAI.Computability.VPVNP.CompressorSlotState
import OAI.Computability.VPVNP.CompressorSlotOwnerPass
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Expanding base incidence into the actual slot columns

The forward scan reads the base mate and the source arc's displacement. The
reverse scan first recovers the source from the inverse base permutation and
then reads that source's displacement. In both directions the lane changes by
one native XOR, since binary-vector translations are their own inverses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotIncidencePass

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression IncidenceDirectory SourceTransport

variable {w a l : ℕ}

/-- Public words are the degree, lane count, base permutation, displacement,
and actual incidence output heads. The persistent word is the actual port. -/
def visit (reverse : Bool) : List (Op 9 5) :=
  [.stateWord 0, .publicWord 1 0, .publicWord 2 1,
   .binary .div 3 0 1, .binary .mod 4 0 1, .binary .div 5 3 2,
   .binary .mul 5 5 1, .binary .add 5 5 4, .binary .mod 3 3 2,
   .publicWord 6 2, .binary .add 6 6 5, .read 6 6,
   .publicWord 7 3, .binary .add 7 7 (if reverse then 6 else 5), .read 7 7,
   .binary .bitXor 3 3 7, .binary .div 8 6 1, .binary .mul 8 8 2, .binary .add 8 8 3,
   .binary .mul 8 8 1, .binary .mod 4 6 1, .binary .add 8 8 4,
   .publicWord 7 4, .binary .add 7 7 0, .write 7 8, .constant 7 1, .binary .add 0 0 7]

private abbrev divW := @BinaryOp.eval w .div
private abbrev modW := @BinaryOp.eval w .mod

variable (p : Fin 5 → Word w)

private def base (i : Word w) :=
  divW (divW i (p 0)) (p 1) * p 0 + modW i (p 0)

private def lane (i : Word w) := modW (divW i (p 0)) (p 1)

private def mate (m : Memory w) (i : Word w) := m (p 2 + base p i).val

private def shiftAddr (reverse : Bool) (m : Memory w) (i : Word w) :=
  p 3 + (if reverse then mate p m i else base p i)

private def dest (reverse : Bool) (m : Memory w) (i : Word w) :=
  let t := mate p m i
  let sh := m (shiftAddr p reverse m i).val
  (divW t (p 0) * p 1 + BinaryOp.bitXor.eval (lane p i) sh) * p 0 + modW t (p 0)

/-- Trace of one forward or reverse incidence visit, reading a base mate and the source arc's
displacement before writing the translated actual port. -/
def events (reverse : Bool) (m : Memory w) (i : Word w) : List (Event w) :=
  List.replicate 11 .tick ++ [.read (p 2 + base p i) (mate p m i), .tick, .tick,
    .read (shiftAddr p reverse m i) (m (shiftAddr p reverse m i).val)] ++
    List.replicate 9 .tick ++ [.write (p 4+i) (dest p reverse m i), .tick, .tick]

theorem events_work (rev : Bool) (m : Memory w) (i : Word w) :
    (events p rev m i).length = 27 ∧ countProbes (events p rev m i) = 3 := ⟨rfl,rfl⟩

private theorem events_after (rev : Bool) (m : Memory w) (i : Word w) :
    after m (events p rev m i) = writeMemory m (p 4+i) (dest p rev m i) := rfl

set_option maxRecDepth 4096 in
private theorem visit_trace (rev : Bool) (m : Memory w) (i : Word w) (rs : Regs w 9) :
    ∃ out, trace p i (visit rev) rs m =
        some (events p rev m i, out, after m (events p rev m i)) ∧ out 0 = i+1 := by
  rw [events_after]
  cases rev <;> simp (config := {decide := true}) [visit, events, dest, shiftAddr, mate, base, lane,
    trace, Op.effect, BinaryOp.eval, divW, modW, Function.update] <;> rfl

theorem native (rev : Bool) (m : Memory w) (i : Word w) :
    let M := (template (visit rev) 0).instantiate w p
    execute M.program 28 (M.program.start i) m [] = some ⟨events p rev m i, some (i+1)⟩ := by
  obtain ⟨rs, ht, hv⟩ := visit_trace p rev m i (fun _ => 0)
  let M := (template (visit rev) 0).instantiate w p
  change execute M.program (1+(visit rev).length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template, run_eq_trace, ht]
  simp [hv]

private theorem unpack {x d : Word w} {hi lo : ℕ} (h : x.val = hi*d.val+lo) (hl : lo < d.val) :
    (divW x d).val = hi ∧ (modW x d).val = lo := by
  have hd := Nat.zero_lt_of_lt hl
  constructor
  · change (x.val/d.val) % _ = hi
    rw [Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt),h,Nat.mul_comm hi,
      Nat.mul_add_div hd,Nat.div_eq_of_lt hl,Nat.add_zero]
  · change (x.val%d.val) % _ = lo
    rw [Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt),h,Nat.mul_add_mod_of_lt hl]

private theorem unpack_port (Y : State a l) (hd : (p 0).val = 2^a) (hl : (p 1).val = 2^l)
    (room : Fintype.card Y.Base * 2^a ≤ 2^w) (e : (Y.Base × BitWord l) × Fin (2^a))
    (i : Word w) (hi : i.val = (actualOrder Y e).val) :
    (base p i).val = (baseOrder Y (e.1.1,e.2)).val ∧
      (lane p i).val = (bitWordFinEquiv l e.1.2).val := by
  have digits : i.val =
      ((Y.baseIndex e.1.1).val * (p 1).val + (bitWordFinEquiv l e.1.2).val) * (p 0).val + e.2.val := by
    rw [hi,actualOrder_val,hl,hd]
  have hq := unpack digits (by rw [hd]; exact e.2.isLt)
  have hv := unpack hq.1 (by rw [hl]; exact (bitWordFinEquiv l e.1.2).isLt)
  refine ⟨?_,hv.2⟩
  rw [base,Fin.val_add,Fin.val_mul,hv.1,hq.2,hd,Nat.mod_add_mod,← baseOrder_val Y (e.1.1,e.2)]
  exact Nat.mod_eq_of_lt ((baseOrder Y _).isLt.trans_le room)

/-- Each native visit reads a base mate and a source displacement, then writes
the current actual port. The reverse visit uses the stored mate as its source
index, so a range bound on that word suffices for both directions. -/
theorem row_footprint (rev : Bool) (Y : State a l) (m : Memory w)
    (hd : (p 0).val = 2^a) (hl : (p 1).val = 2^l)
    (ht : (p 2).val + Fintype.card Y.Base*2^a ≤ (p 4).val)
    (hs : (p 3).val + Fintype.card Y.Base*2^a ≤ (p 4).val)
    (fit : (p 4).val + Fintype.card Y.Base*2^l*2^a ≤ 2^w)
    (hm : ∀ e, (m ((p 2).val + (baseOrder Y e).val)).val < Fintype.card Y.Base * 2^a)
    (j : ℕ) (hj : j < Fintype.card Y.Base * 2^l * 2^a) :
    Reads (fun x ↦ ((p 2).val ≤ x ∧ x < (p 2).val + Fintype.card Y.Base * 2^a) ∨
      ((p 3).val ≤ x ∧ x < (p 3).val + Fintype.card Y.Base * 2^a)) (events p rev m (Fin.ofNat _ j)) ∧
    Writes (fun x ↦ (p 4).val ≤ x ∧ x < (p 4).val + Fintype.card Y.Base * 2^l * 2^a)
      (events p rev m (Fin.ofNat _ j)) := by
  let i := Fin.ofNat (2^w) j
  let e := (actualOrder Y).symm ⟨j,hj⟩
  let b := (e.1.1,e.2)
  have hi : i.val = j := Nat.mod_eq_of_lt (by omega)
  have he : (actualOrder Y e).val = j := congrArg Fin.val ((actualOrder Y).apply_symm_apply ⟨j,hj⟩)
  have room := (p 4).isLt
  have hb : (base p i).val = (baseOrder Y b).val :=
    (unpack_port p Y hd hl (by omega) e i (hi.trans he.symm)).1
  have b_lt := (baseOrder Y b).isLt
  have atMate : (p 2 + base p i).val = (p 2).val + (baseOrder Y b).val := by
    rw [Fin.val_add,hb,Nat.mod_eq_of_lt (by omega)]
  have src_lt : (if rev then mate p m i else base p i).val < Fintype.card Y.Base * 2^a := by
    cases rev
    · simpa only [Bool.false_eq_true,ite_false,hb] using b_lt
    · simpa only [ite_true,mate,atMate] using hm b
  have atShift : (shiftAddr p rev m i).val =
      (p 3).val + (if rev then mate p m i else base p i).val := by
    rw [shiftAddr,Fin.val_add,Nat.mod_eq_of_lt (by omega)]
  constructor <;> intro addr val mem
  · change Event.read addr val ∈ events p rev m i at mem
    simp [events] at mem
    rcases mem with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · left; rw [atMate]; omega
    · right; rw [atShift]; omega
  · change Event.write addr val ∈ events p rev m i at mem
    simp [events] at mem
    rw [mem.1,Fin.val_add,hi,Nat.mod_eq_of_lt (by omega)]
    omega

private theorem read_row (rev : Bool) (Y : State a l) (m : Memory w)
    (hd : (p 0).val = 2^a) (hl : (p 1).val = 2^l)
    (ht : (p 2).val + Fintype.card Y.Base*2^a ≤ (p 4).val)
    (hs : (p 3).val + Fintype.card Y.Base*2^a ≤ (p 4).val)
    (fit : (p 4).val + Fintype.card Y.Base*2^l*2^a ≤ 2^w)
    (hm : ∀ e, m ((p 2).val+(baseOrder Y e).val) =
      Fin.ofNat _ (baseOrder Y ((if rev then Y.slots.base.target.symm else Y.slots.base.target) e)).val)
    (hsh : ∀ e, m ((p 3).val+(baseOrder Y e).val) =
      Fin.ofNat _ (bitWordFinEquiv l (Y.slots.displacement e)).val)
    (e : (Y.Base × BitWord l) × Fin (2^a)) :
    dest p rev m (Fin.ofNat _ (actualOrder Y e).val) =
      Fin.ofNat _ (actualOrder Y ((if rev then Y.slots.actualGraph.target.symm else Y.slots.actualGraph.target) e)).val := by
  rcases e with ⟨⟨v,g⟩,j⟩
  let e := (v,j)
  let t := (if rev then Y.slots.base.target.symm else Y.slots.base.target) e
  let s := Y.slots.displacement (if rev then t else e)
  let i := Fin.ofNat (2^w) (actualOrder Y ((v,g),j)).val
  have hbase (f : Y.Base × Fin (2^a)) : (baseOrder Y f).val < 2^w := by
    have := (baseOrder Y f).isLt
    have := (p 4).isLt
    omega
  have hi : i.val = (actualOrder Y ((v,g),j)).val :=
    Nat.mod_eq_of_lt (by have := (actualOrder Y ((v,g),j)).isLt; omega)
  obtain ⟨hb,hlane⟩ := unpack_port p Y hd hl (by have := (p 4).isLt; omega) ((v,g),j) i hi
  have hmate : mate p m i = Fin.ofNat _ (baseOrder Y t).val := by
    rw [mate,Fin.val_add,hb,Nat.mod_eq_of_lt (by have := (baseOrder Y e).isLt; have := (p 4).isLt; omega)]
    exact hm e
  have htval : (mate p m i).val = (baseOrder Y t).val := by
    rw [hmate,Fin.val_ofNat,Nat.mod_eq_of_lt (hbase t)]
  have hsource : (if rev then mate p m i else base p i).val =
      (baseOrder Y (if rev then t else e)).val := by cases rev <;> first | exact hb | exact htval
  have hread : (m (shiftAddr p rev m i).val).val = (bitWordFinEquiv l s).val := by
    rw [shiftAddr,Fin.val_add,hsource,Nat.mod_eq_of_lt (by
      have := (baseOrder Y (if rev then t else e)).isLt; have := (p 4).isLt; omega),hsh,Fin.val_ofNat]
    exact Nat.mod_eq_of_lt ((bitWordFinEquiv l s).isLt.trans (hl ▸ (p 1).isLt))
  have hu := unpack (x := mate p m i) (d := p 0) (hi := (Y.baseIndex t.1).val) (lo := t.2.val)
    (by rw [htval,baseOrder_val,hd]) (by rw [hd]; exact t.2.isLt)
  have hnum : (actualOrder Y ((if rev then Y.slots.actualGraph.target.symm else Y.slots.actualGraph.target) ((v,g),j))).val =
      ((Y.baseIndex t.1).val*2^l + (bitWordFinEquiv l (g+s)).val)*2^a + t.2.val := by
    have neg (x : BitWord l) : -x = x := funext fun u ↦ CharTwo.neg_eq (x u)
    cases rev <;> simp [e,t,s,LiftedSlots.actualGraph_target,LiftedSlots.actualGraph_target_symm,
      actualOrder_val,sub_eq_add_neg,neg]
  apply Fin.ext
  change (dest p rev m i).val = _ % _
  rw [hnum,dest,Fin.val_add,Fin.val_mul,Fin.val_add,Fin.val_mul,hu.1,hu.2,hl,hd,bitWordFinEquiv_add_val]
  change (((_ % _ + (((lane p i).val ^^^ _) % _)) % _ * _ % _ + _) % _) = _
  rw [hlane,hread]
  simp only [Nat.mod_add_mod,Nat.add_mod_mod,Nat.mod_mul_mod]

/-- Construct either actual incidence column over all positions, lanes and
slots. Every call uses two reads and one write, and preserves the input arrays. -/
theorem run (reverse : Bool) (Y : State a l) (p : Fin 5 → Word w) (m : Memory w)
    (hd : (p 0).val = 2^a) (hl : (p 1).val = 2^l)
    (ht : (p 2).val + Fintype.card Y.Base*2^a ≤ (p 4).val)
    (hs : (p 3).val + Fintype.card Y.Base*2^a ≤ (p 4).val)
    (fit : (p 4).val + Fintype.card Y.Base*2^l*2^a ≤ 2^w)
    (hm : ∀ e, m ((p 2).val+(baseOrder Y e).val) =
      Fin.ofNat _ (baseOrder Y ((if reverse then Y.slots.base.target.symm else Y.slots.base.target) e)).val)
    (hsh : ∀ e, m ((p 3).val+(baseOrder Y e).val) =
      Fin.ofNat _ (bitWordFinEquiv l (Y.slots.displacement e)).val) :
    let n := Fintype.card Y.Base*2^l*2^a
    let M := (template (visit reverse) 0).instantiate w p
    ∃ rs, runSegment M.program 28 (some 0) m (List.replicate n []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ n) ∧
      (∀ e, after m (eventLog rs) ((p 4).val+(actualOrder Y e).val) =
        Fin.ofNat _ (actualOrder Y ((if reverse then Y.slots.actualGraph.target.symm else Y.slots.actualGraph.target) e)).val) ∧
      (∀ addr, addr < (p 4).val ∨ (p 4).val+n ≤ addr → after m (eventLog rs) addr = m addr) ∧
      RAMBuckets.cost Report.probes rs = 4*n := by
  intro n M
  let order := actualOrder Y
  let f := if reverse then Y.slots.actualGraph.target.symm else Y.slots.actualGraph.target
  let value := fun j : ℕ ↦ Fin.ofNat (2^w) (order (f (order.symm (Fin.ofNat n j)))).val
  obtain ⟨rs, hr, hc, hvals, hframe, _, _, hcost⟩ := SlotOwnerPass.run M.program 28 3 27 (p 4).val 0 n value m
    (by simpa using fit) (by
      intro j _ hj mem frame
      have hjn : j < n := by simpa using hj
      let u : Fin n := ⟨j,hjn⟩
      let e := order.symm u
      have he : (actualOrder Y e).val = j := congrArg Fin.val (order.apply_symm_apply u)
      have hu : Fin.ofNat n j = u := Fin.ext (Nat.mod_eq_of_lt hjn)
      have hv := read_row p reverse Y mem hd hl ht hs fit (fun z ↦ by
        have := (baseOrder Y z).isLt; rw [frame _ (.inl (by omega))]; exact hm z) (fun z ↦ by
        have := (baseOrder Y z).isLt; rw [frame _ (.inl (by omega))]; exact hsh z) e
      rw [he] at hv
      have hval : dest p reverse mem (Fin.ofNat _ j) = value j := by simpa only [value,hu] using hv
      have hnext : Fin.ofNat (2^w) j + 1 = Fin.ofNat _ (j+1) := by
        apply Fin.ext; simp [Fin.val_add,Nat.mod_add_mod,Nat.add_mod_mod]
      have haddr : p 4 + Fin.ofNat _ j = Fin.ofNat _ ((p 4).val+j) := by
        apply Fin.ext; simp [Fin.val_add,Nat.add_mod_mod]
      exact ⟨events p reverse mem _,by rw [native,hnext],by rw [events_after,haddr,hval],
        (events_work ..).2,(events_work ..).1⟩)
  refine ⟨rs,hr,by simpa using hc,?_,fun addr ha ↦ hframe addr (by omega),by simpa using hcost⟩
  intro e
  have he := (order e).isLt
  have hu : Fin.ofNat n (order e).val = order e := Fin.ext (Nat.mod_eq_of_lt he)
  simpa only [value,hu,Equiv.symm_apply_apply] using hvals (order e).val (Nat.zero_le _) (by simpa only [Nat.zero_add] using he)

end CompressorRecords.SlotIncidencePass

end VPVNP
end Computability
end OAI
