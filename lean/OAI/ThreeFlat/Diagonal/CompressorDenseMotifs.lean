import OAI.ThreeFlat.Diagonal.CompressorMotifBlocks
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Public dense histogram rows for physical source-major shrinking motifs -/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression
open scoped Classical
variable {B H Tag L : Type*} {c d N J K : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData B H Tag L d c)

abbrev Upper (B H Tag L : Type*) (d : ℕ) := (Site B Tag L × Fin d) × H

def upperDigits : Upper B H Tag L d ≃ (((B × Fin d) × L) × Tag) × H where
  toFun a := ((((a.1.1.1,a.1.2),a.1.1.2.2),a.1.1.2.1),a.2)
  invFun z := (((z.1.1.1.1,z.1.2,z.1.1.2),z.1.1.1.2),z.2)
  left_inv _ := rfl
  right_inv _ := rfl

def upperNumber (b : B ≃ Fin N) (tag : Tag ≃ Fin J) (lane : L ≃ Fin K) :
    Upper B H Tag L d ≃ Fin (N*d*K*J*d) :=
  let basePort := (Equiv.prodCongr b (Equiv.refl (Fin d))).trans finProdFinEquiv
  let withLane := (Equiv.prodCongr basePort lane).trans finProdFinEquiv
  let withTag := (Equiv.prodCongr withLane tag).trans finProdFinEquiv
  upperDigits.trans ((Equiv.prodCongr withTag P.slotLabel).trans finProdFinEquiv)

def blockCoordinates :
    P.Motif ≃ Σ a : Upper B H Tag L d, ↥(oldBlock P a.1 a.2) where
  toFun m := ⟨(m.val.1,m.val.2.2),Native.tagOrdinal c m.val.2.1,by
    simpa only [oldBlock,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply] using m.property⟩
  invFun z := ⟨(z.1.1,(Native.tagOrdinal c).symm z.2.val,z.1.2),by
    simpa only [oldBlock,Finset.mem_filter,Finset.mem_univ,true_and] using z.2.property⟩
  left_inv m := Subtype.ext (by simp)
  right_inv z := by rcases z with ⟨a,u,hu⟩; simp

def denseMotifRow (b : B ≃ Fin N) (tag : Tag ≃ Fin J) (lane : L ≃ Fin K) (hc : 2≤c) :
    P.Motif ≃ Fin ((N*d*K*J*d)*(3*2^(c-2))) :=
  let fibers (a : Upper B H Tag L d) : ↥(oldBlock P a.1 a.2) ≃ Fin (3*2^(c-2)) :=
    ((oldBlock P a.1 a.2).orderIsoOfFin (oldBlock_card P a.1 a.2 hc)).toEquiv.symm
  (blockCoordinates P).trans ((Equiv.sigmaEquivProdOfEquiv fibers).trans
    ((Equiv.prodCongr (upperNumber P b tag lane) (Equiv.refl _)).trans finProdFinEquiv))

theorem denseMotifRow_value (b : B ≃ Fin N) (tag : Tag ≃ Fin J) (lane : L ≃ Fin K)
    (hc : 2≤c) (m : P.Motif) :
    (denseMotifRow P b tag lane hc m).val =
      (upperNumber P b tag lane (m.val.1,m.val.2.2)).val*(3*2^(c-2)) +
        blockIndex P m.val.1 m.val.2.2 (Native.tagOrdinal c m.val.2.1) := by
  have eq := blockIndex_listed P m.val.1 m.val.2.2 ((blockCoordinates P m).2) hc
  rw [show Native.tagOrdinal c m.val.2.1 = ((blockCoordinates P m).2).val from rfl,eq]
  change _ + (3*2^(c-2))*(upperNumber P b tag lane (m.val.1,m.val.2.2)).val = _
  rw [Nat.mul_comm (3*2^(c-2)),Nat.add_comm]
  rfl

def baseNat (b : B ≃ Fin N) : B ↪ ℕ := b.toEmbedding.trans ⟨Fin.val,Fin.val_injective⟩

omit [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L] in
theorem upperNumber_physical (b : B ≃ Fin N) (tag : Tag ≃ Fin J) (lane : L ≃ Fin K)
    (a : Arc B H Tag L d c) :
    demandOrdinal P (baseNat b) tag.toEmbedding lane.toEmbedding a / 2^c =
      (upperNumber P b tag lane (a.1,a.2.2)).val := by
  change (appendKey _ (Native.tagOrdinal c a.2.1))/2^c = _
  unfold appendKey
  rw [Nat.mul_comm _ (2^c),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt (Native.tagOrdinal c _).isLt,
    Nat.add_zero]
  simp only [baseNat,upperNumber,upperDigits,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.coe_fn_mk,Prod.map_apply,finProdFinEquiv,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Function.Embedding.coeFn_mk,Equiv.refl_apply]
  ring

end ThreeFlat.Diagonal.CompressorPacking

end OAI
