import OAI.ThreeFlat.Diagonal.TraceBitRecord
import OAI.ThreeFlat.Diagonal.TraceStaticAddressRecord

namespace OAI
/-! # Source addresses of the physical trace with one open pin per input word -/

namespace ThreeFlat.Diagonal.TraceBitDescriptor

open Computability.VPVNP RAM.BitLayout TraceAddressRecord
variable {w p r k d S f : ℕ}

noncomputable def input (hw : 3≤w+1) (hs : S≤2^w) (hf : f≤2^(w+1)) (base : ℕ) (v : Fin (2^d)) :
    Fin (Fintype.card (StaticPortIndex w p r k d)) → BitSource (TraceUniformRow.SharedCount w p r k d f) S :=
  fun j => TraceBitHeader.relabel TraceBitHeader.bitPin
    (TraceStaticRow.portSource hw hs hf base v ((Fintype.equivFin _).symm j))

noncomputable def records (hw : 3≤w+1) (base S f : ℕ) :
    Fin (Fintype.card (StaticPortIndex w p r k d)) → Record :=
  fun j => staticBitPort hw base S f ((Fintype.equivFin _).symm j)

theorem records_correct (hw : 3≤w+1) (hs : S≤2^w) (hf : f≤2^(w+1)) (base : ℕ)
    (v : Fin (2^d)) (j : Fin (Fintype.card (StaticPortIndex w p r k d))) :
    (records hw base S f j).eval v.val = sourceAddress (input hw hs hf base v j) := by
  unfold records input
  cases h : (Fintype.equivFin (StaticPortIndex w p r k d)).symm j with
  | inl a => exact bitPort_eval hw base S f v a
  | inr a =>
    exact staticPort_eval (p:=p) (r:=r) (k:=k) hw hs hf base v (.inr a)

end ThreeFlat.Diagonal.TraceBitDescriptor

end OAI
