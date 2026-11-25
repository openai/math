import OAI.ThreeFlat.RAM.StableCompactProgram
import OAI.ThreeFlat.RAM.StableCompactROMEntry

namespace OAI
/-! # Fixed decoder for stable-compaction row descriptors in public memory -/

namespace ThreeFlat.RAM.StableCompactROMProgram

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Decoder registers hold kind, payload, xor mask, site, padded width and logical width. -/
private def byKind (tag : ℕ) (yes no : Term w k 6) : Term w k 6 :=
  .select .eq (.result 0) (.literal (tag : Word w)) yes no

def decodeProgram : Term w k 6 :=
  let bit : Term w k 6 := .binary .bitAnd (.binary .shiftRight (.result 3) (.result 1)) (.literal 1)
  let pin : Term w k 6 := .select .lt (.result 3) (.result 5)
    (.binary .add (.binary .add (.literal 2) (.binary .mul (.result 1) (.result 5))) (.result 3))
    (.literal 0)
  let hidden : Term w k 6 := .binary .add (.binary .add
    (.binary .add (.literal 2) (.binary .mul (.literal 3) (.result 5)))
    (.binary .mul (.result 1) (.result 4))) (.binary .bitXor (.result 3) (.result 2))
  byKind 0 (.result 1) (byKind 1 bit (byKind 2 pin hidden))

theorem decodeProgram_binds : (decodeProgram (w:=w) (k:=k)).binds ≤ 30 := by
  simp [decodeProgram,byKind,Term.binary,Term.select,Term.literal,Term.binds]

theorem decodeProgram_eval (e : Entry) (N n v : ℕ) (four : 4 < 2^w)
    (hn : n < 2^w) (hv : v < 2^w) (fit : e.Fits w)
    (words : Fin k → Word w) (mem : Memory w) (vs : Fin 6 → Word w)
    (hk : vs 0 = (e.kind : Word w)) (hp : vs 1 = (e.payload : Word w))
    (hm : vs 2 = (e.mask : Word w)) (hs : vs 3 = (v : Word w))
    (hN : vs 4 = (N : Word w)) (hwid : vs 5 = (n : Word w)) :
    decodeProgram.eval words mem vs = (e.atSite N n v : Word w) := by
  have choose (tag : ℕ) (ht : tag < 2^w) (yes no : Term w k 6) :
      (byKind tag yes no).eval words mem vs =
        if e.kind = tag then yes.eval words mem vs else no.eval words mem vs := by
    have hkind : e.kind < 2^w := lt_trans (show e.kind < 4 by cases e <;> norm_num [Entry.kind]) four
    have equal : ((e.kind : Word w) = (tag : Word w)) ↔ e.kind = tag := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt hkind,Fin.val_cast_of_lt ht]
    simp [byKind,Term.eval,Comparison.test,hk,equal]
  simp only [decodeProgram,choose 0 (by omega),choose 1 (by omega),choose 2 (by omega)]
  cases e with
  | literal a => simpa [Entry.kind,Entry.atSite,Entry.payload,Term.eval] using hp
  | siteBit j =>
    have pos : 0<w := Nat.pos_of_ne_zero (fun hw => by subst w; norm_num at four)
    change j < 2^w at fit
    change BinaryOp.eval .bitAnd (BinaryOp.eval .shiftRight (vs 3) (vs 1)) 1 = _
    rw [hs,hp]
    change BinaryOp.eval .bitAnd (BinaryOp.eval .shiftRight (v : Word w) (j : Word w)) 1 = _
    rw [Computability.VPVNP.PrimedInputRAM.Opcodes.readBit_word pos,Fin.val_cast_of_lt hv,Fin.val_cast_of_lt fit]
    cases eqn : v.testBit j <;> simp [Entry.atSite,eqn,Computability.VPVNP.PrimedInputRAM.encodeBit]
  | pin stream =>
    by_cases live : v < n <;> simp [Entry.kind,Entry.atSite,Term.eval,hs,hp,hwid,Entry.payload,
      Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hn,Fin.val_cast_of_lt hv,BinaryOp.eval,live]
  | hidden reg mask =>
    change mask < 2^w at fit
    simp [Entry.kind,Entry.atSite,Term.eval,hs,hp,hm,hN,hwid,Entry.payload,Entry.mask,
      Fin.val_cast_of_lt hv,Fin.val_cast_of_lt fit,BinaryOp.eval]

end ThreeFlat.RAM.StableCompactROMProgram

end OAI
