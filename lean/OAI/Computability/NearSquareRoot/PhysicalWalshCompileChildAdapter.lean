import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildAdapterSpec

/-! # Source-generating the descent and return frames of a recursive call -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileChild

open IntegerMultiplication Code PhysicalWalshNode CommonRegisters GeneratorSyntax
open KernelEffectiveFamily Filter

open private header_size expose expose_easy tagRow tagRow_easy replaceRow replaceRow_easy
  from OAI.Computability.NearSquareRoot.PhysicalWalshChildAdapter

private theorem fitsLeft {c : Cmd} {a b z : Tree} {env : Env} {park : Deck} {n : ℕ}
    (h : Fits env c (pile 0 a (pile 0 z park)) (pile 0 b (pile 0 z park)) n) :
    Fits env (leftCmd c) (pile 0 (.fork a z) park) (pile 0 (.fork b z) park) (n+7) :=
  (fits_pair (h.join (fits_pack _ _ _ _ _))).mono (by omega)

/-- Both commands have the same meaning for any compact descriptor program
satisfying the polynomial bound on its own input and output. -/
private theorem assemble {d : ℕ} (hd : 1 ≤ d) {c : Control → Cmd} (calculate : Configured d c)
    {ex tg ret : Cmd} (xe : Runs ex (expose ([] : Stream))) (xt : Runs tg (@tagRow Stream))
    (xr : Runs ret (@replaceRow Stream)) :
    Adapter d (fun k => (ex.join (leftCmd (c k))).join tg) ret := by
  obtain ⟨E,hE⟩ := xe
  obtain ⟨T,hT⟩ := xt
  obtain ⟨U,hU⟩ := xr
  intro a W ax
  obtain ⟨G,g⟩ := calculate a W ax
  let C := E*45 + G + T*(G+45) + U*(G+45) + (G+45) + 12
  refine ⟨C,fun s pos row => ?_⟩
  let t := (⟨a,W,ax,s⟩ : World)
  let parent := ChildAdapter.saved a W s
  let pow := (Header.scale (a+1) s+1)^d
  let v := ChildAdapter.volume (a+1) s
  let b := pow + v + size row + 1
  have bp : 1 ≤ b := by dsimp [b]; omega
  have pbound : pow ≤ b := by dsimp [b]; omega
  have scale : Header.scale (a+1) s ≤ pow := by
    have hp := Nat.pow_le_pow_right (Nat.succ_pos (Header.scale (a+1) s)) hd
    rw [pow_one] at hp
    exact (Nat.le_succ _).trans hp
  have hdr := header_size a W s pos
  change size parent ≤ 30*v + Header.scale (a+1) s + 9 at hdr
  have room : size parent ≤ 40*b := by dsimp only [b]; omega
  have small : size parent + size row + 4 ≤ 45*b := by dsimp only [b] at *; omega
  let tagged := tag t
  have hc := g s
  have tagCap : size tagged ≤ G*pow := hc.2
  have wireCap : size tagged.2 ≤ size tagged := by
    rw [size_prod tagged]
    omega
  have budget : size tagged + size row + size parent + 3 ≤ (G+45)*b := by
    rw [Nat.add_mul]
    have := Nat.mul_le_mul_left G pbound
    omega
  have qSize : size (parent,[row])+1 ≤ 45*b := by
    simpa only [size_prod,size_cons,size_nil,Prod.fst,Prod.snd] using (by omega :
      size parent + (size row+1+1)+1+1 ≤ 45*b)
  have tagSize : size (tagged,row,parent)+1 ≤ (G+45)*b := by
    simpa only [size_prod,Prod.fst,Prod.snd] using (by omega :
      size tagged + (size row + size parent + 1)+1+1 ≤ (G+45)*b)
  have replySize : size ((tagged.2,row),parent)+1 ≤ (G+45)*b := by
    simpa only [size_prod,Prod.fst,Prod.snd] using (by omega :
      size tagged.2 + size row+1+size parent+1+1 ≤ (G+45)*b)
  have allBudget : G*b + (E*45)*b + (T*(G+45))*b + (U*(G+45))*b + (G+45)*b + 12*b ≤ C*b := by
    dsimp [C]; simp only [Nat.add_mul]; omega
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro env park
    have ep := hE (parent,[row]) env park
    have cl := fitsLeft (hc.1 env (pile 0 (send (row,parent)) park))
    have tc := hT (tagged,row,parent) env park
    apply ((ep.join cl).join tc).mono
    have eb := Nat.mul_le_mul_left E qSize
    have tb := Nat.mul_le_mul_left T tagSize
    have gb := Nat.mul_le_mul_left G pbound
    rw [← Nat.mul_assoc] at eb tb
    change E*(size (parent,[row])+1)+(G*pow+7)+2 + T*(size (tagged,row,parent)+1)+2 ≤ C*b
    omega
  · intro env park
    apply (hU ((tagged.2,row),parent) env park).mono
    have ub := Nat.mul_le_mul_left U replySize
    rw [← Nat.mul_assoc] at ub
    change U*(size ((tagged.2,row),parent)+1) ≤ C*b
    omega
  · change size (parent,[row]) ≤ C*b
    have h45 : 45*b ≤ (G+45)*b := Nat.mul_le_mul_right _ (by omega)
    omega
  · change size ((tagged.2,row),parent) ≤ C*b
    omega
  · change size parent ≤ C*b
    have h40 : 40*b ≤ (G+45)*b := Nat.mul_le_mul_right _ (by omega)
    omega

/-- The prologue and return adapter are chosen before the template, slot,
layout, input rows, and recursive time and space budgets. -/
theorem compiledFrames : ∃ (R d : ℕ) (down : Control → Cmd) (up : Cmd),
    1 ≤ d ∧ Effective ltr down ∧ (∀ k, Within R (down k)) ∧ Within R up ∧ Adapter d down up := by
  obtain ⟨R,d,c,hd,he,hR,calculate⟩ := configured
  obtain ⟨ex,xe⟩ := expose_easy ([] : Stream)
  obtain ⟨tg,xt⟩ := @tagRow_easy Stream _
  obtain ⟨ret,xr⟩ := @replaceRow_easy Stream _
  obtain ⟨L,lr,le',rex,rtg,rret⟩ := ((eventually_ge_atTop R).and ((eventually_ge_atTop 1).and
    ((RegisterSelect.within_eventually ex).and ((RegisterSelect.within_eventually tg).and
      (RegisterSelect.within_eventually ret))))).exists
  exact ⟨L,d,_,ret,hd,((effective_const ltr ex).join (effective_left he)).join (effective_const ltr tg),
    fun k => ⟨⟨rex,within_left le' (RegisterSelect.within_mono lr _ (hR k))⟩,rtg⟩,rret,assemble hd calculate xe xt xr⟩

end PhysicalWalshCompileChild

end NearSquareRoot
end Computability
end OAI
