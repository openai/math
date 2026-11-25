import OAI.Hierarchy.TaggedLocalDestinationData
import OAI.Hierarchy.TaggedLocalSortBuckets

namespace OAI
/-! # Occupied slots and stable real-word observations of the canonical block alignment -/

namespace Hierarchy.Tagged.Radix
open ThreeFlat Routing SortNetwork SortedBlock
open scoped Classical
noncomputable section

variable {d w j t : ℕ}

private theorem address_bound {r m p : ℕ} (hp : 0 < p) (key : Fin r → Fin m) (mono : Monotone key) (i : Fin r) :
    Align.realAddress p key i < r+m*p := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r => exact Align.dest_lt_slots hp key mono i

theorem align_support (x : Records (j+t) w) (real : Fin w) (digit : Fin d → Fin w)
    (ok : AlignedInput digit real x) (i : Row (j+t)) (alive : align digit real x i real = true) :
    i.val < prefixSize real x + 2^d * 2^j := by
  let e := SortedBlock.perm digit real x ok
  have active : x (e.symm i) real = true := by simpa [align,ok,e] using alive
  let q := liveEquiv digit real x ok ⟨e.symm i,active⟩
  have eq : e (Align.split (prefixSize_le real x) (.inl q)) = i := e.apply_symm_apply i
  have pos := congrArg Fin.val eq
  simp only [e,destination,placement,Align.embed_val] at pos
  rw [←pos]
  exact address_bound (Nat.two_pow_pos j) (blockKeys digit real x) (blockKeys_mono digit real x ok) q

theorem localAlign_buckets (x : Records (j+t) w) (real : Fin w) (digit : Fin d → Fin w) (a : ℕ)
    (ok : AlignedInput digit real x) :
    sweep (2^(j+t)) (fun i => observeRow real digit a (align digit real x i)) =
      sweep (2^(j+t)) (fun i => observeRow real digit a (x i)) := by
  let e := SortedBlock.perm digit real x ok
  let p (z : Bits w) := z real = true
  let transport := RealTransport.perm (real := p) e.symm x
  have ordered : StrictMono transport.route := fun i j ij => align_order digit real x ok i.property j.property ij
  have allRows := RealTransport.same_read transport ordered
  have same : (List.ofFn (x ∘ e.symm)).filter (fun z => z real) =
      (List.ofFn x).filter (fun z => z real) := by
    simpa only [p, Bool.decide_eq_true] using allRows
  simpa only [sweep_rows,align,dite_eq_left ok,e] using congrArg (bucket (readKey digit) a) same

end
end Hierarchy.Tagged.Radix

end OAI
