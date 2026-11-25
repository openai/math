import OAI.Hierarchy.DescentOriginalEpochSheetCharge
import OAI.Hierarchy.DescentEpochVoteHeader
import OAI.Hierarchy.DescentPackedProfileTape
import OAI.Hierarchy.ProtocolRAMSumScoresCheap

namespace OAI
/-! # Checking all actual and padded profile fields in one native lookup per packed word -/
namespace Hierarchy.DescentPackedProfileValidity
open DescentSIMDLookup DescentTerminalEpochFlags DescentPackedProfileTape ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {A : Type} {C seats W : ℕ}

def cut (grain count r : ℕ) := min grain (count-r*grain)
private theorem local_good (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool)
    (grain count r : ℕ) :
    bad C grain (cut grain count r) (packed pin z grain r)=0 ↔
      ∀j : Fin grain,SeatValid C count (cell pin z (r*grain+j.val)).val (r*grain+j.val) := by
  have digit_ (j : Fin grain) :
      digit (DescentTerminalEpochBits.width C) j.val (packed pin z grain r).val=(cell pin z (r*grain+j.val)).val :=
    digit_encode _ j
  have cmp (j : Fin grain) : j.val < cut grain count r ↔ r*grain+j.val < count := by
    unfold cut;have h:=j.isLt;omega
  simp [bad,SeatValid,digit_,cmp]

theorem zero_valid (C count i : ℕ) : SeatValid C count 0 i := by
  let p : DescentSixParty.Profile C:=⟨fun _=>0,by simp⟩
  have e : DescentTerminalEpochFlags.encode p=0 := by
    change (∑j : Fin 8,(0:Fin (C+2)).val*(C+2)^j.val)=0
    simp
  have dec:=decode_encode p
  rw [e] at dec
  simp [SeatValid,dec]


theorem all_good (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool)
    (grain count : ℕ) (pos : 0 < grain) :
    (∀r : Fin (slots seats grain),bad C grain (cut grain count r.val) (packed pin z grain r.val)=0) ↔
      ∀i : Fin seats,SeatValid C count (DescentTerminalEpochBits.raw (z∘pin) i) i.val := by
  constructor
  · intro good i
    let r : Fin (slots seats grain):=⟨i.val/grain,by
      have := Nat.div_le_div_right (c:=grain) i.isLt.le;unfold slots;omega⟩
    let j : Fin grain:=⟨i.val%grain,Nat.mod_lt _ pos⟩
    have got:=(local_good pin z grain count r.val).mp (good r) j
    have coord : r.val*grain+j.val=i.val:=Nat.div_add_mod' ..
    rwa [coord,active pin z i] at got
  · intro good r
    apply (local_good pin z grain count r.val).mpr
    intro j
    by_cases live : r.val*grain+j.val < seats
    · let i : Fin seats:=⟨_,live⟩
      change SeatValid C count (cell pin z i.val).val i.val
      rw [active pin z i]
      exact good i
    · rw [inactive pin z (by omega : seats ≤ r.val*grain+j.val)]
      exact zero_valid ..

structure Banks where
  source : Bank
  starts : Bank
  shifts : Bank
  dictionary : Bank
  count : Bank

def usedExpr (b : Banks) (grain : ℕ) : Expr :=
  let n := Expr.lookup b.count (.lit 0)
  let lo := Expr.lookup b.starts .row
  let dif := Expr.op .sub n lo
  .branch .lt lo n (.branch .lt dif (.lit grain) dif (.lit grain)) (.lit 0)

def checkExpr (b : Banks) (grain : ℕ) : Expr :=
  .lookup b.dictionary (.op .add (.lookup b.shifts (usedExpr b grain)) (.lookup b.source .row))

def proc (b : Banks) (W grain seats dst : ℕ) :=
  SumScores.procedure W dst (slots seats grain) 1 (checkExpr b grain)

def fee (b : Banks) (grain seats : ℕ) :=
  4+(slots seats grain+1)*(42+2*(checkExpr b grain).work)

structure Room (b : Banks) (W C seats grain dst : ℕ) : Prop where
  codes : b.source.Fits W dst
  starts : b.starts.Fits W dst
  shifts : b.shifts.Fits W dst
  dictionary : b.dictionary.Fits W dst
  count : b.count.Fits W dst
  sourceSize : slots seats grain ≤ b.source.size
  startsSize : slots seats grain ≤ b.starts.size
  shiftsSize : grain+1 ≤ b.shifts.size
  dictSize : tariff C grain ≤ b.dictionary.size
  offsets : slots seats grain*grain < 2^W
  end_ : dst+(slots seats grain+1) < 2^W

/-- All mutable input comes from the issued count and the compact original
Boolean selector. The starts, shifts and dictionary columns are fixed literals. -/
structure Reads (b : Banks) (m : Memory W) (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool)
    (grain : ℕ) : Prop where
  source : ∀i : Fin (slots seats grain), m (b.source.base+i.val)=((packed pin z grain i.val).val:Word W)
  starts : ∀i : Fin (slots seats grain), m (b.starts.base+i.val)=(startsWord grain i.val:Word W)
  shifts : ∀u ≤ grain, m (b.shifts.base+u)=(bankShift C grain u:Word W)
  dictionary : ∀u ≤ grain,∀key : Cell (DescentTerminalEpochBits.width C*grain),
    m (b.dictionary.base+(bankShift C grain u+key.val))=(bad C grain u key:Word W)

private theorem bank_nat (b : Bank) (m : Memory W) (i dst : ℕ) (small : i < b.size) (fits : b.Fits W dst) :
    b.read m (i:Word W)=m (b.base+i) := by
  simp only [Bank.read,Fin.val_cast_of_lt (small.trans fits.2.1),Nat.mod_eq_of_lt small]

private theorem used_read (b : Banks) (grain dst count lo : ℕ) (m : Memory W) (i : Word W)
    (_hn : b.count.Fits W dst) (count_ : m b.count.base=(count:Word W))
    (start : b.starts.read m i=(lo:Word W)) (fitN : count < 2^W) (fitL : lo < 2^W) (fitG : grain < 2^W) :
    (usedExpr b grain).eval m i=((min grain (count-lo) : ℕ) : Word W) := by
  have read_ : b.count.read m (0:Word W)=m b.count.base := by simp [Bank.read]
  have cmp : ((lo:Word W) < (count:Word W)) ↔ lo < count := by
    change (lo:Word W).val < (count:Word W).val ↔ _
    rw [Fin.val_cast_of_lt fitN,Fin.val_cast_of_lt fitL]
  simp only [usedExpr,Expr.eval,DescriptorExpr.Comparison.test,decide_eq_true_eq,
    RowOp.opcode,BinaryOp.eval,Nat.cast_zero,read_,count_,start]
  by_cases lt : lo < count
  · rw [ite_eq_left (cmp.mpr lt),←Nat.cast_sub lt.le]
    have fits : count-lo < 2^W := by omega
    have diff : ((count-lo:ℕ):Word W) < (grain:Word W) ↔ count-lo < grain := by
      change (((count-lo:ℕ):Word W)).val < (grain:Word W).val ↔ _
      rw [Fin.val_cast_of_lt fits,Fin.val_cast_of_lt fitG]
    by_cases below : count-lo < grain
    · rw [ite_eq_left (diff.mpr below),min_eq_right below.le]
    · rw [ite_eq_right (mt diff.mp below),min_eq_left (by omega)]
  · rw [ite_eq_right (mt cmp.mp lt),Nat.sub_eq_zero_of_le (by omega),Nat.min_zero]; rfl

theorem read (b : Banks) (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool)
    (grain dst : ℕ) (m : Memory W) (space : Room b W C seats grain dst) (input : Reads b m pin z grain)
    (i : Fin (slots seats grain)) :
    (checkExpr b grain).eval m (i.val:Word W)=(bad C grain (cut grain (m b.count.base).val i.val)
      (packed pin z grain i.val):Word W) := by
  let u:=cut grain (m b.count.base).val i.val
  let key:=packed pin z grain i.val
  let a:=bankShift C grain u+key.val
  have hi : u ≤ grain := Nat.min_le_left ..
  have loc : a < tariff C grain := by
    have mul:=Nat.mul_le_mul_right (2^(DescentTerminalEpochBits.width C*grain)) hi
    have kw:=key.isLt
    dsimp [a,tariff,bankShift]
    rw [Nat.add_mul,Nat.one_mul]
    omega
  have os:=bank_nat b.starts m i.val dst (i.isLt.trans_le space.startsSize) space.starts
  have offset : i.val*grain < 2^W:= (Nat.mul_le_mul_right grain i.isLt.le).trans_lt space.offsets
  have reading : (usedExpr b grain).eval m (i.val:Word W)=(u:Word W) := by
    simpa only [u,cut] using (used_read b grain dst (m b.count.base).val (i.val*grain) m (i.val:Word W)
      space.count (by simp) (os.trans (input.starts i)) (m b.count.base).isLt offset
      (by have := space.shiftsSize.trans_lt space.shifts.2.1;omega))
  have incr:=(bank_nat b.shifts m u dst (by have := space.shiftsSize;omega) space.shifts).trans (input.shifts u hi)
  have source:=(bank_nat b.source m i.val dst (i.isLt.trans_le space.sourceSize) space.codes).trans (input.source i)
  change b.dictionary.read m (b.shifts.read m ((usedExpr b grain).eval m (i.val:Word W))+
    b.source.read m (i.val:Word W))=_
  rw [reading,incr,source,←Nat.cast_add]
  change b.dictionary.read m (a:Word W)=(bad C grain u key:Word W)
  exact (bank_nat b.dictionary m a dst (loc.trans_le space.dictSize) space.dictionary).trans
    (input.dictionary u hi key)

/-- The sticky failure bit can directly consume this result. Only one
RAM scan iteration is needed per packed profile word, including padding. -/
theorem run (b : Banks) (pin : DescentTerminalEpochBits.Pins C seats→A) (z : A→Bool)
    (grain dst : ℕ) (m : Memory W) (space : Room b W C seats grain dst) (input : Reads b m pin z grain)
    (pos : 0 < grain) :
    (proc b W grain seats dst).Spec (·=m) (fun _ o =>
      (o (dst+slots seats grain)=if ∀i : Fin seats,SeatValid C (m b.count.base).val
        (DescentTerminalEpochBits.raw (z∘pin) i) i.val then 0 else 1) ∧
      ∀a,a < dst ∨ dst+(slots seats grain+1) ≤ a → o a=m a) (fee b grain seats) ∧
      CheapCode (proc b W grain seats dst) := by
  let score (i : Fin (slots seats grain)):=bad C grain (cut grain (m b.count.base).val i.val) (packed pin z grain i.val)
  have sum : (∑i,score i) ≤ slots seats grain := by
    calc
      _ ≤ ∑_ : Fin (slots seats grain),1 := Finset.sum_le_sum fun i _=>by dsimp [score,bad];split <;> decide
      _ = _ := by simp
  have fit : (checkExpr b grain).Fits W dst := by
    simp only [checkExpr,usedExpr,Expr.Fits]
    repeat' first | exact space.dictionary | exact space.shifts | exact space.starts | exact space.codes | exact space.count | trivial | constructor
  refine ⟨?_,PruneFlag.cheap W dst (slots seats grain) 1 (checkExpr b grain)⟩
  intro P R K machine pc reg pub exit installed data cfg t entry eqn
  subst t
  have room:=space.end_
  obtain ⟨time,bill,state,o,steps,done,land⟩:=SumScores.run dst 1 (checkExpr b grain) score fit room
    (by omega) (by omega) machine pc reg pub exit installed data cfg m entry (read b pin z grain dst m space input)
  refine ⟨time,bill,state,o,steps,done,?_,?_⟩
  · rw [land,SumScores.read_flag]
    have correct : (∑i,score i)=0 ↔ ∀i : Fin seats,SeatValid C (m b.count.base).val
        (DescentTerminalEpochBits.raw (z∘pin) i) i.val := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _)]
      simpa only [Finset.mem_univ,true_implies] using all_good pin z grain (m b.count.base).val pos
    by_cases ok : (∑i,score i)=0
    · simp [ok,correct.mp ok]
    · rw [ite_eq_left (show 1 ≤ _ from Nat.pos_of_ne_zero ok),ite_eq_right (mt correct.mpr ok)]
  · intro a out
    simp [land,fillSegment,show ¬(dst ≤ a ∧ a < dst+(slots seats grain+1)) by omega]

end
end Hierarchy.DescentPackedProfileValidity

end OAI
