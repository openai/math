import OAI.Computability.NearSquareRoot.ScheduleGeneratorFunction

/-! # Computable operations on the read buffer of the alphabet controller -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator

open CommonAlphabet

variable {X R S T : Type} [Primcodable X] [Primcodable R] [Primcodable S] [Primcodable T]

/-- Apply a computable binary operation along matching positions of two lists. -/
theorem computable_zipWith [Inhabited R] [Inhabited S]
    {xs : X → List R} {ys : X → List S} {f : X → R × S → T}
    (ha : Computable xs) (hb : Computable ys) (hf : Computable₂ f) :
    Computable fun x => List.zipWith (fun a b => f x (a,b)) (xs x) (ys x) := by
  have n := Primrec.nat_min.to_comp.comp (Computable.list_length.comp ha) (Computable.list_length.comp hb)
  have getLeft := (Primrec.list_getD (default : R)).to_comp.comp
    (ha.comp (Computable.fst (α := X) (β := ℕ))) Computable.snd
  have getRight := (Primrec.list_getD (default : S)).to_comp.comp
    (hb.comp (Computable.fst (α := X) (β := ℕ))) Computable.snd
  apply (computable_rangeMap n (hf.comp Computable.fst (getLeft.pair getRight)).to₂).of_eq
  intro x
  apply List.ext_getElem
  · simp
  · intro i hi hj
    obtain ⟨hi₁, hi₂⟩ : i < (xs x).length ∧ i < (ys x).length := by simpa using hj
    simp [hi₁, hi₂]

theorem computable_replicate {n : X → ℕ} {v : X → R} (hn : Computable n) (hv : Computable v) :
    Computable fun x => List.replicate (n x) (v x) := by
  simpa only [List.map_const', List.length_range] using
    computable_rangeMap hn (f := fun x _ => v x) (hv.comp Computable.fst).to₂

namespace PhaseLists

theorem zipWith_map {A B C D : Type} (domain : List A) (f : B → C → D) (g : A → B) (h : A → C) :
    List.zipWith f (domain.map g) (domain.map h) = domain.map fun x => f (g x) (h x) := by
  rw [List.zipWith_map, List.zipWith_self]

theorem fin_all {n : ℕ} : (Numbering.fin n).all = List.finRange n := by
  change (List.finRange n).map id = _
  exact List.map_id _

theorem set_finRange_map {A : Type} {n : ℕ} (f : Fin n → A) (i : Fin n) (v : A) :
    ((List.finRange n).map f).set i.val v = (List.finRange n).map (Function.update f i v) := by
  simp [(List.nodup_finRange n).map_update]

/-- The scalar representation of every track's pending one-block read. -/
def bufferView {I : Type} {w : ℕ} (indices : Numbering I) (buf : I → Letters w) : List (List ℕ) :=
  indices.all.map fun u => (Numbering.fin w).all.map fun k => (Numbering.ternary.equiv (buf u k)).val

/-- Update one column of the pending reads. -/
def stash (j : ℕ) (buf : List (List ℕ)) (read : List ℕ) : List (List ℕ) :=
  List.zipWith (fun row v => row.set j v) buf read

theorem computable_stash {k : X → ℕ} {b : X → List (List ℕ)} {r : X → List ℕ}
    (hk : Computable k) (hb : Computable b) (hr : Computable r) :
    Computable fun x => stash (k x) (b x) (r x) :=
  computable_zipWith hb hr
    (Primrec.list_set.to_comp.comp (Computable.fst.comp Computable.snd)
      ((hk.comp Computable.fst).pair (Computable.snd.comp Computable.snd))).to₂

theorem stash_view {I : Type} {w : ℕ} (indices : Numbering I) (buf : I → Letters w)
    (j : Fin w) (read : I → Option Bool) :
    stash j.val (bufferView indices buf) (indices.all.map fun i => (Numbering.ternary.equiv (read i)).val) =
      bufferView indices (CommonAlphabet.stash buf j read) := by
  simp only [stash, bufferView, zipWith_map, fin_all, set_finRange_map]
  apply List.map_congr_left
  intro i _
  congr 1
  exact (Function.comp_update (fun v => (Numbering.ternary.equiv v).val) (buf i) j (read i)).symm

theorem emptyBuffer_view {A I : Type} (indices : Numbering I) (c : Code A) :
    bufferView indices (emptyBuffer c) = List.replicate indices.size (List.replicate c.width 0) := by
  change indices.all.map (fun _ => (Numbering.fin c.width).all.map fun _ => 0) = _
  simp only [List.map_const', fin_all, List.length_finRange]
  simp [Numbering.all]

end PhaseLists
end Generator

end NearSquareRoot
end Computability
end OAI
