import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalRoles
import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalReadback

/-! # Native execution of every owned row and publication of the verified banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Physical Physical.Owned Scatter Padding.Banks TeamRowSources Tally
open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages VPVNP.BurstRAM

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout}
variable {A : Data n l.d blocks b h K s} {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ}
variable {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ} {pub : Arg → Word w} {original m : Memory w}

/-- Choose the physical role by the two actual symbols returned by the native preparation. -/
theorem PhysicalSetup.roleRun (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
    (mac : TeamOpcode.Macros w 8) (v : Fin l.d × Fin l.d) (owned : owner v.1 = l.teamID)
    (r : Bank w) (same : ∀ x ∈ source l power n, m x = original x)
    (output : readings r 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (key v))
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key v) (.ofWords r m)) :
    TraceRun pub mac (if v.1 = v.2 then diagonalRole n b h K s else strictRole n b h K s) r m
      (A.privateTapeAt l (key v)) (physicalCostAt l blocks b h K s A.axis (key v))
      (PhysicalReturn A power actual pub v r m) := by
  rcases v with ⟨a,e⟩
  change TraceRun pub mac (if a = e then _ else _) _ _ _ _ _
  rcases lt_trichotomy a e with lo | eq | hi
  · rw [ite_eq_right lo.ne]
    exact P.strictRun mac ⟨(a,e),lo⟩ false owned r same output prep
  · subst e
    rw [ite_eq_left rfl]
    exact P.diagonalRun mac a r same prep
  · rw [ite_eq_right hi.ne']
    exact P.strictRun mac ⟨(e,a),hi⟩ true owned r same output prep

/-- Native completion carries the real vertex count, every local packet and singleton read,
and the preserved source words. The pre-publication memory is the genuine return of the row scan. -/
structure PhysicalCompletion (A : Data n l.d blocks b h K s) (owner : Fin l.d → ℕ)
    (power base : ℕ) (original : Memory w) (J : ℕ → Memory w → Prop) (t : Bank w) (mt : Memory w) : Prop where
  vertex : readings t 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (l.d*l.d)
  views : ∀ x : View n l.d blocks (h*b), owner (x.row A.axis).1 = l.teamID → A.Holds mt x
  count : readings mt (l.frame+46) = vertexPrefix l (wordOwner owner) n blocks (l.d*l.d)
  sourceWords : ∀ a ∈ source l power n, a ≠ l.frame+46 → mt a = original a
  publication : ∃ pre : Memory w, J (l.d*l.d) pre ∧ mt = publishVertexCount pre l.frame
    (vertexPrefix l (wordOwner owner) n blocks (l.d*l.d))

/-- Execute the complete native program. An additional property of the returned memory
can be propagated by inspecting its genuine scatter and checker histories on each owned row. -/
theorem PhysicalSetup.physical_run_induction (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
    (mac : TeamOpcode.Macros w 8) (r : Bank w) (J : ℕ → Memory w → Prop) (start : J 0 original)
    (skip : ∀ v : Fin l.d × Fin l.d, owner v.1 ≠ l.teamID → ∀ mu, J (key v) mu → J (key v+1) mu)
    (step : ∀ v : Fin l.d × Fin l.d, owner v.1 = l.teamID → ∀ u mu t mt,
      J (key v) mu → readings u 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (key v) →
      PhysicalStages A power actual pub u mu t mt v → J (key v+1) mt) :
    TraceRun pub mac (ownedGroups n b h K s) r original (choices l (wordOwner owner) (A.privateTapeAt l))
      (4+(ticks l (wordOwner owner) (physicalCostAt l blocks b h K s A.axis)+11))
      (PhysicalCompletion A owner power base original J) := by
  let I (q : ℕ) (mu : Memory w) := (∀ a ∈ source l power n, mu a = original a) ∧ A.Past (l := l) owner q mu ∧ J q mu
  have first : I 0 original := ⟨fun _ _ => rfl,A.past_zero owner original,start⟩
  have inventory (q : ℕ) (mu : Memory w) (hi : I q mu) := P.inventory hi.1
  have pairKey (q : Fin (l.d*l.d)) : key (pairAt l.d q) = q.val :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply q)
  have ownerEq (q : Fin (l.d*l.d)) : wordOwner owner (q.val/l.d) = owner (pairAt l.d q).1 := by
    have digit := (key_digits (pairAt l.d q)).1
    rw [pairKey q] at digit
    rw [digit,wordOwner,dite_eq_left (pairAt l.d q).1.isLt]
  have miss (q : ℕ) (hq : q < l.d*l.d) (ho : wordOwner owner (q/l.d) ≠ l.teamID)
      (mu : Memory w) (hi : I q mu) : I (q+1) mu := by
    let f : Fin (l.d*l.d) := ⟨q,hq⟩
    have foreign : owner (pairAt l.d f).1 ≠ l.teamID := (ownerEq f) ▸ ho
    have old : J (key (pairAt l.d f)) mu := (pairKey f).symm ▸ hi.2.2
    have vk : key (pairAt l.d f) = q := pairKey f
    exact ⟨hi.1,Data.Past.skip f hi.2.1 foreign,by simpa only [vk] using skip _ foreign mu old⟩
  have visit (q : ℕ) (hq : q < l.d*l.d) (ho : wordOwner owner (q/l.d) = l.teamID)
      (u : Bank w) (mu : Memory w) (hi : I q mu)
      (output : readings u 7 = base+3*vertexPrefix l (wordOwner owner) n blocks q)
      (prep : TeamRowPrepare.ReadyRow l (readings mu) q (.ofWords u mu)) :
      TraceRun pub mac (if q/l.d = q%l.d then diagonalRole n b h K s else strictRole n b h K s) u mu
        (A.privateTapeAt l q) (physicalCostAt l blocks b h K s A.axis q) (fun t mt =>
          I (q+1) mt ∧ readings t 7 = readings u 7+(if q/l.d = q%l.d then 0 else 3*strictVertices n l.d blocks) ∧
          readings t 22 = q ∧ readings t 23 = l.d*l.d) := by
    let f : Fin (l.d*l.d) := ⟨q,hq⟩
    let v := pairAt l.d f
    have vk : key v = q := pairKey f
    have owned : owner v.1 = l.teamID := (ownerEq f) ▸ ho
    have digits := key_digits v
    rw [vk] at digits
    have eq : (q/l.d = q%l.d) ↔ (v.1 = v.2) := by rw [digits.1,digits.2]; exact ⟨Fin.ext,congrArg Fin.val⟩
    have branch {α : Type} (x y : α) : (if q/l.d = q%l.d then x else y) = (if v.1 = v.2 then x else y) := by
      by_cases hd : q/l.d = q%l.d
      · simp only [ite_eq_left hd,ite_eq_left (eq.mp hd)]
      · simp only [ite_eq_right hd,ite_eq_right (fun hv => hd (eq.mpr hv))]
    have output' : readings u 7 = base+3*vertexPrefix l (wordOwner owner) n blocks (key v) := vk.symm ▸ output
    have run := P.roleRun mac v owned u hi.1 output' (vk.symm ▸ prep)
    rw [branch,branch]
    rw [vk] at run
    apply run.mono le_rfl
    intro t mt ret
    have next : A.Past (l := l) owner (q+1) mt := P.past_step f hi.2.1 (by simpa only [vk] using ret.bankWords)
    exact ⟨⟨fun x hx => (ret.sourceWords x hx).trans (hi.1 x hx),next,
      by simpa only [vk] using step v owned u mu t mt (vk.symm ▸ hi.2.2) output' ret.stages⟩,
      ret.vertex,ret.cursor.trans vk,ret.bound⟩
  have run := ownedGroups_run pub mac n blocks b h K s l (wordOwner owner) (physicalCostAt l blocks b h K s A.axis)
    (A.privateTapeAt l) I base r original P.fits P.seed.frame first inventory miss visit
  apply run.mono le_rfl
  rintro t mt ⟨vertex,pre,hi,published⟩
  obtain ⟨views,count,src⟩ := P.publish_readback hi.2.1 hi.1 published
  exact ⟨vertex,views,count,src,pre,hi.2.2,published⟩

/-- All owned row inputs are correct in the final returned memory of the assembled native evaluator. -/
theorem ownedGroups_physical_run (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
    (mac : TeamOpcode.Macros w 8) (r : Bank w) :
    TraceRun pub mac (ownedGroups n b h K s) r original (choices l (wordOwner owner) (A.privateTapeAt l))
      (4+(ticks l (wordOwner owner) (physicalCostAt l blocks b h K s A.axis)+11))
      (PhysicalCompletion A owner power base original (fun _ _ => True)) :=
  P.physical_run_induction mac r (fun _ _ => True) trivial (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ => trivial)

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
