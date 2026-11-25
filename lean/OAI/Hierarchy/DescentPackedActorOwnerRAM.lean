import OAI.Hierarchy.DescentPackedOwnerWord
import OAI.Hierarchy.DescentDonorShape
import OAI.Hierarchy.DescentPackedActorOwners
import OAI.Hierarchy.DescentPackedCensusRAM

namespace OAI
/-! # Native register of root, dyadic leaf and slot for all previous sites -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Owners
open DescentSIMDLookup DescentSixParty Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {r D p d : ℕ}
private theorem pack_count {I : Type*} (wt : I→ℕ) (B : ℕ) (xs : List I) :
    (thinPacks wt B xs).length≤xs.length := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    rw [thinPacks];cases ps : thinPacks wt B xs with
    | nil=>simp
    | cons q rest=>rw [ps] at ih;simp only [List.length_cons] at ih ⊢;split <;> simp <;> omega

private theorem slot_bound {U : Type*} [DecidableEq U] (xs : List (List U)) (u : U) :
    readPack xs u≤xs.length := by
  unfold readPack
  cases (List.finRange xs.length).find? (fun i=>decide (u∈xs.get i)) with
  | none=>exact Nat.zero_le _
  | some j=>exact j.isLt

private theorem thick_bound (u : Panel r D p d) (l : Bool) (n : ℕ) :
    let q:=thickAddress u l n
    q.1≤D ∧ q.2.1<2^d ∧ q.2.2=0 := by
  have sub (x : Cell d) : leaf x.val<2^d := (Nat.div_le_self _ _).trans_lt ((Nat.sub_le _ _).trans_lt x.isLt)
  unfold thickAddress
  split <;> (first | split | skip) <;> (first | split | skip) <;> simp_all []

theorem resolved_bound (u : Panel r D p d) (B profile : ℕ) (l : Bool) (x : Fin r) :
    let q:=resolved B profile u l x
    q.1≤D ∧ q.2.1<2^d ∧ q.2.2≤r := by
  have depth : leaf (u.winner x).val<2^d := (Nat.div_le_self _ _).trans_lt ((Nat.sub_le _ _).trans_lt (u.winner x).isLt)
  have slot (k bins) : readPack (packs u bins B k) x≤r :=
    (slot_bound ..).trans ((pack_count ..).trans (site_length u k false))
  dsimp only [resolved]
  split
  · split
    · exact ⟨Nat.zero_le _,depth,slot _ _⟩
    · rename_i j
      obtain ⟨a,b,c⟩:=thick_bound u l _
      exact ⟨a,b,c ▸ Nat.zero_le _⟩
  · exact ⟨Nat.zero_le _,depth,slot _ _⟩

theorem read_cell (u : Panel r D p d) (B profile : ℕ) (l : Bool) (x : Fin r) (j : Fin 3) :
    let q:=resolved B profile u l x
    (((encode (digits r D d) 3).symm (cell r D d q)) j).val=(![q.1,q.2.1,q.2.2] : Fin 3→ℕ) j := by
  dsimp only
  simp only [cell,Equiv.symm_apply_apply]
  obtain ⟨root,depth,slot⟩:=resolved_bound u B profile l x
  have limit : max r D<2^(digits r D d) := (Nat.lt_succ_self _).trans_le
    ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..)))
  fin_cases j
  · exact Nat.mod_eq_of_lt ((root.trans (le_max_right ..)).trans_lt limit)
  · exact Nat.mod_eq_of_lt (depth.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left ..)))
  · exact Nat.mod_eq_of_lt ((slot.trans (le_max_left ..)).trans_lt limit)

theorem render_register (B profile : ℕ) (l : Bool) (u : Panel r D p d) :
    render r D p d B profile (register l u)=encode (digits r D d*3) r (fun j=>cell r D d (resolved B profile u l j)) := by
  cases l <;> simp [render,register,decode_encode_panel]

theorem publish {H J M w : ℕ} (banks : Banks) (out B profile : ℕ)
    (fit : Fits banks (inputBits r D p d) ((digits r D d*3)*r) M H J w out)
    (l : Fin H→Fin J→Bool) (u : Fin H→Fin J→Panel r D p d) (m : Memory w)
    (loaded : PinFrame (M:=M) banks (render r D p d B profile) (fun v j=>register (l v j) (u v j)) m) :
    ∃last,(program banks out H J M w).Exec m last (4+44*(H*chunks J M)) ∧
      (∀a : Row H J M,last (out+(row H J M a).val)=
        ((data (fun v j=>encode (digits r D d*3) r (fun x=>cell r D d (resolved B profile (u v j) (l v j) x))) a).val:Word w)) ∧
      ∀x,x<out ∨ out+H*chunks J M≤x→last x=m x := by
  let last:=image out (H*chunks J M) (lookup banks) m
  refine ⟨last,?_,(fun a=>by simpa only [render_register] using DescentSixParty.PackedCensus.col_read _ _ fit _ _ m loaded a),?_⟩
  · rw [show 4+44*(H*chunks J M)=4+(H*chunks J M)*(2*(lookup banks).work+4) by
      rw [lookup_work]
      ring]
    exact scan_exec out (H*chunks J M) (lookup banks) m
      (show (lookup banks).Fits w out from by simp [lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]) fit.output
  · rintro x (h|h)
    · simp [last,image,fillSegment,Nat.not_le.mpr h]
    · simp [last,image,fillSegment,Nat.not_lt.mpr h]

end
end Hierarchy.DescentPacking.PackedMatch.Local.Owners

end OAI
