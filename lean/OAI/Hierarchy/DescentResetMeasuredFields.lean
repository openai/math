import OAI.Hierarchy.DescentResetIssuedStencil
import OAI.Hierarchy.DescentResetContactRoster

namespace OAI
/-! # Finite fields of a stencil assembled from the original measured columns -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil
open DescentColonies DescentGL DescentIssuedFallbackPanel DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {m c n q : ℕ} (small : c≤ m)
variable (near : V→Finset V) (b : V→ℕ) (L : Layout m) (weight : V→Block m→ℕ) (traffic : V→V→Block m→ℕ)
variable (hub : V→Bool) (Δ f B K g cap : ℕ) (ports : V→Fin q→Option (Contacts near)) (inc : V→List V)
local notation "D" => (32*Nat.clog 2 (2*Δ))
local notation "weights" => (fun hi u z=>rearrangedLoad weight L u (join small hi z))
local notation "rows" => (fun hi=>Scan.build inc (weights hi) D (2^(f+1)*B) (m-c))

def measured (v : V) (hi : Block c) : panel (m-c) q n
  | .inl s=>(((if s.val=0 then b v-c else if s.val=1 then m-g-c else (hub v).toNat):ℕ):Cell n)
  | .inr (.inl (.inl x))=>(weights hi v x:Cell n)
  | .inr (.inl (.inr (d,x)))=>((Scan.lookup (rows hi) d.val v x).toNat:Cell n)
  | .inr (.inr (.inl (i,x)))=>((decide ((rearrange L).symm (join small hi i)<(rearrange L).symm (join small hi x))).toNat:Cell n)
  | .inr (.inr (.inr (p,j)))=>(edgeWords small near b L traffic f B K cap hi (ports v p) j:Cell n)

private theorem bool_fits (a : Bool) (hn : 1<2^n) : a.toNat<2^n := by cases a <;> simp_all

omit [DecidableEq V] in
theorem measured_input (depth : ∀v,b v≤ m) (hword : m-c<2^n) (positive : 1<2^n)
    (wroom : ∀v x,weight v x<2^n) (troom : ∀u v x,traffic u v x≤cap) (clipped : 2^(m-c)*cap<2^n)
    (v : V) (hi : Block c) :
    Input small near b L weight traffic hub Δ f B K g cap hi v (ports v) inc
      (measured (n:=n) small near b L weight traffic hub Δ f B K g cap ports inc v hi) := by
  have md (z : V) : b z-c<2^n:=(Nat.sub_le_sub_right (depth z) c).trans_lt hword
  have merged : m-g-c<2^n:=(Nat.sub_le_sub_right (Nat.sub_le ..) c).trans_lt hword
  have tcell : cap<2^n:=by
    have lo : 1*cap≤2^(m-c)*cap := Nat.mul_le_mul_right cap (Nat.two_pow_pos (m-c))
    exact (by simpa only [one_mul] using lo : cap≤2^(m-c)*cap).trans_lt clipped
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simp [header,measured,Fin.val_cast_of_lt (md v)]
  · simp [header,measured,Fin.val_cast_of_lt merged]
  · have nonzero : n≠0 := by rintro rfl; simp at positive
    cases h : hub v <;> simp [header,measured,h,nonzero]
  · intro x
    exact Fin.val_cast_of_lt (wroom v _)
  · intro d x
    have h:=bool_fits (Scan.lookup (rows hi) d.val v x) positive
    simp only [marked,measured,Fin.val_cast_of_lt h]
    cases Scan.lookup (rows hi) d.val v x <;> decide
  · intro i x
    let test:=decide ((rearrange L).symm (join small hi i)<(rearrange L).symm (join small hi x))
    have h:=bool_fits test positive
    change decide (((test.toNat:Cell n).val)≠0)=test
    rw [Fin.val_cast_of_lt h]
    cases test <;> decide
  · intro p j
    apply Fin.val_cast_of_lt
    cases read : ports v p with
    | none => simp only [edgeWords];omega
    | some e =>
      cases j with
      | inl s =>
        simp only [edgeWords]
        split
        · exact (Nat.sub_le_sub_right (max_le (depth _) (depth _)) c).trans_lt hword
        · exact (min_le_left ..).trans_lt clipped
      | inr x=>exact (troom _ _ _).trans_lt tcell

end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil

end OAI
