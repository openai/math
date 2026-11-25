import OAI.ThreeFlat.Diagonal.LaneRelayNetwork

namespace OAI
/-! # Four-word metadata of relay rows, with the prefix of owned pins -/

namespace ThreeFlat.Diagonal.TraceBucketRelay

open LaneCursor
open scoped Classical

variable {F O D : Type*} [CommSemiring F] {r k t : ℕ}
abbrev arcs (r : ℕ) := (r+1)*2

def sendPin (s : Fin (arcs r)) (a : Fin t) : BitSource 0 (arcs r*t+arcs r*t) :=
  .pin ((finProdFinEquiv (s,a)).castAdd _)

def recvPin (s : Fin (arcs r)) (a : Fin t) : BitSource 0 (arcs r*t+arcs r*t) :=
  .pin (Fin.natAdd _ (finProdFinEquiv (s,a)))

def previous (i : Fin (k+1)) : Fin (k+1) := ⟨i.val-1,by omega⟩

variable (ord : Fin t ≃ O × D) (mask : O → Lane (k+1)) (i : Fin (k+1))

theorem hole_sources (s : Fin (arcs r)) (a : Fin t) :
    (RelayNetwork.network (F:=F) ord mask i).source ((finProdFinEquiv (s,a)).castAdd t) =
      ![sendPin s a,if s = selected mask (ord a).1 i then sendPin s a else .constant false,.constant false] := by
  refine (Fin.append_left _ _ (finProdFinEquiv (s,a))).trans ?_
  change (fun z : Fin (arcs r) × Fin t => ![sendPin z.1 z.2,
    if z.1 = selected mask (ord z.2).1 i then sendPin z.1 z.2 else .constant false,.constant false])
    (finProdFinEquiv.symm (finProdFinEquiv (s,a))) = _
  rw [Equiv.symm_apply_apply]

theorem forward_sources (a : Fin t) :
    (RelayNetwork.network (F:=F) (r:=r) ord mask i).source (Fin.natAdd (arcs r*t) a) =
      ![sendPin (selected mask (ord a).1 i) a,
        if i=0 then sendPin (selected mask (ord a).1 i) a
        else recvPin (selected mask (ord a).1 (previous i)) a,.constant false] := by
  exact (Fin.append_right _ _ a).trans (by rfl)

def shiftedSource (extra : ℕ) {h p : ℕ} : BitSource h p → ℕ
  | .constant b => b.toNat
  | .pin j => 2+extra+j.val
  | .hidden j => 2+extra+p+j.val

def metadata {p : ℕ} (extra : ℕ) (tag : ((Fin 3 → Bool) → F) → ℕ)
    (N : BitNetwork F p) (c : Fin N.cells) (j : Fin 4) : ℕ :=
  if h : j.val<3 then shiftedSource extra (N.source c ⟨j.val,h⟩) else tag (N.table c)

end ThreeFlat.Diagonal.TraceBucketRelay

end OAI
