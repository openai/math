import OAI.Hierarchy.DescentResetFieldAssembler

namespace OAI
/-! # One scan for the measured reset parent word with its native seven-field live bit -/
namespace Hierarchy.DescentResetMixedWordRAM
open DescentPackedZip DescentSIMDLookup DescentResetFieldAssembler
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {b z u t o M H G w : ℕ}

private def packedPair (a b : ℕ) : Cell a × Cell b ≃ Cell (a+b):=finProdFinEquiv.trans (finCongr (pow_add 2 a b).symm)

def couple (a b : ℕ) (x : Cell a) (y : Cell b) : Cell (a+b) :=packedPair a b (x,y)

theorem zero_couple (a b : ℕ) : couple a b 0 0=0:=by
  apply Fin.ext;simp [couple,packedPair,finProdFinEquiv_apply_val]

def head (raw : Cell (b*7)) (zero : Cell z) : Cell 2 :=
  couple 1 1 (((encode b 7).symm raw 0).val:Cell 1) (zero.val:Cell 1)

theorem empty_head (b z : ℕ) : head (0:Cell (b*7)) (0:Cell z)=0:=by
  have t : (encode b 7).symm 0=(fun _=>0):=by apply (encode b 7).symm_apply_eq.mpr;apply Fin.ext;simp [encode]
  simp [head,t,zero_couple]

def result (f : ℕ→ℕ→ℕ→ℕ→ℕ) (h : Cell 2) (p : Cell (u+t)) : Cell o :=
  let flags:=(packedPair 1 1).symm h
  let args:=(packedPair u t).symm p
  f flags.1.val flags.2.val args.1.val args.2.val

theorem combine (f : ℕ→ℕ→ℕ→ℕ→ℕ) (m : Meta) (zero : Bool) (halo : Cell u) (arg : Cell t)
    (liveWidth : 0<b) (zWidth : 0<z) :
    result (o:=o) f (head (raw b m) (zero.toNat:Cell z)) (couple u t halo arg)=
      (f m.live.toNat zero.toNat halo.val arg.val:Cell o):=by
  have bit (flag : Bool) (k : ℕ) (positive : 0 < k) :
      (((flag.toNat : Cell k).val : Cell 1).val) = flag.toNat := by
    have fits : flag.toNat < 2^k :=
      (Bool.toNat_le flag).trans_lt (Nat.one_lt_two_pow_iff.mpr positive.ne')
    have one : flag.toNat < 2^1 := (Bool.toNat_le flag).trans_lt (by decide)
    rw [Fin.val_cast_of_lt fits, Fin.val_cast_of_lt one]
  simp only [result, head, raw, couple, Equiv.symm_apply_apply]
  change (f (((m.live.toNat : Cell b).val : Cell 1).val)
    (((zero.toNat : Cell z).val : Cell 1).val) halo.val arg.val : Cell o) = _
  rw [bit m.live b liveWidth, bit zero z zWidth]

structure Charts where
  mask : Tables
  args : Tables
  word : Tables

def operation (C : Charts) («meta» zero halo arg : Expr) : Expr :=
  C.word.read (C.mask.read «meta» zero) (C.args.read halo arg)

theorem read_op (C : Charts) («meta» zero halo arg : Expr) (out : Nat) (m : Memory w)
    (fn : ℕ→ℕ→ℕ→ℕ→ℕ) (absent : fn 0 0 0 0=0)
    (src : Fin H→Fin G→Meta) (test : Fin H→Fin G→Bool) (rank : Fin H→Fin G→Cell u) (operand : Fin H→Fin G→Cell t)
    (liveWidth : 0<b) (zeroWidth : 0<z)
    (ms : Source «meta» (fun h g=>raw b (src h g)) M m) (zs : Source zero (fun h g=>((test h g).toNat:Cell z)) M m)
    (hs : Source halo rank M m) (ds : Source arg operand M m)
    (ok₁ : Fits C.mask «meta» zero (b*7) z M out w) (ok₂ : Fits C.args halo arg u t M out w)
    (ok₃ : Fits C.word (C.mask.read «meta» zero) (C.args.read halo arg) 2 (u+t) M out w)
    (tab₁ : Static C.mask (head (b:=b) (z:=z)) M m) (tab₂ : Static C.args (couple u t) M m)
    (tab₃ : Static C.word (result (u:=u) (t:=t) (o:=o) fn) M m)
 : Source (operation C «meta» zero halo arg) (fun h g=>(fn (src h g).live.toNat (test h g).toNat (rank h g).val (operand h g).val:Cell o)) M m:=by
  have mask:=read_data C.mask «meta» zero out ok₁ _ (empty_head b z) m tab₁ _ _ ms zs
  have args:=read_data C.args halo arg out ok₂ _ (zero_couple u t) m tab₂ _ _ hs ds
  have unpair (a b : ℕ) : (packedPair a b).symm 0=(0,0):=
    (packedPair a b).symm_apply_eq.mpr (zero_couple a b).symm
  have unused : result (u:=u) (t:=t) (o:=o) fn 0 0=0:=by simp [result,unpair,absent]
  have read:=read_data C.word _ _ out ok₃ _ unused m tab₃ _ _ mask args
  have decoded :
      (fun (h : Fin H) (g : Fin G) => result (u:=u) (t:=t) (o:=o) fn
        (head (raw b (src h g)) ((test h g).toNat : Cell z)) (couple u t (rank h g) (operand h g))) =
      (fun h g => (fn (src h g).live.toNat (test h g).toNat (rank h g).val (operand h g).val : Cell o)) := by
    funext h g
    exact combine fn (src h g) (test h g) (rank h g) (operand h g) liveWidth zeroWidth
  rw [← decoded]
  exact read

theorem run (C : Charts) («meta» zero halo arg : Expr) (out : Bank) (m : Memory w)
    (fn : ℕ→ℕ→ℕ→ℕ→ℕ) (absent : fn 0 0 0 0=0)
    (src : Fin H→Fin G→Meta) (test : Fin H→Fin G→Bool) (rank : Fin H→Fin G→Cell u) (operand : Fin H→Fin G→Cell t)
    (liveWidth : 0<b) (zeroWidth : 0<z)
    (ms : Source «meta» (fun h g=>raw b (src h g)) M m) (zs : Source zero (fun h g=>((test h g).toNat:Cell z)) M m)
    (hs : Source halo rank M m) (ds : Source arg operand M m)
    (ok₁ : Fits C.mask «meta» zero (b*7) z M out.base w) (ok₂ : Fits C.args halo arg u t M out.base w)
    (ok₃ : Fits C.word (C.mask.read «meta» zero) (C.args.read halo arg) 2 (u+t) M out.base w)
    (tab₁ : Static C.mask (head (b:=b) (z:=z)) M m) (tab₂ : Static C.args (couple u t) M m)
    (tab₃ : Static C.word (result (u:=u) (t:=t) (o:=o) fn) M m)
    (ceiling : ℕ) (room : out.Fits w ceiling) (extent : H*chunks G M≤out.size)
    (space : out.base + H*chunks G M < 2^w) :
    let op:=operation C «meta» zero halo arg
    let N:=H*chunks G M
    let dst:=image out.base N op m
    (scan w out.base N op).Exec m dst (4+N*(2*op.work+4)) ∧
    Source (.lookup out .row) (fun h g=>(fn (src h g).live.toNat (test h g).toNat (rank h g).val (operand h g).val:Cell o)) M dst ∧
    (∀p : Row H G M,dst (out.base+(row H G M p).val)=((data (fun h g=>(fn (src h g).live.toNat (test h g).toNat (rank h g).val (operand h g).val:Cell o)) p).val:Word w)) ∧
    ∀j,j<out.base∨out.base+N≤j→dst j=m j:=by
  intro op N dst
  have seen:=read_op C «meta» zero halo arg out.base m fn absent src test rank operand liveWidth zeroWidth ms zs hs ds ok₁ ok₂ ok₃ tab₁ tab₂ tab₃
  have fit : op.Fits w out.base := ⟨ok₃.apply, ok₃.right, ok₃.shift, ok₃.left⟩
  have word (p : Row H G M) : dst (out.base+(row H G M p).val)=((data (fun h g=>(fn (src h g).live.toNat (test h g).toNat (rank h g).val (operand h g).val:Cell o)) p).val:Word w):=by
    apply (ProtocolRAMGeneratedWrite.read_image out.base N op m (row H G M p)).trans
    exact seen p
  exact ⟨scan_exec _ _ _ _ fit space,source_column out ceiling room _ _ extent word,word,fun j safe=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ j safe⟩

end
end Hierarchy.DescentResetMixedWordRAM

end OAI
