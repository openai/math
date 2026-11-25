import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleStrictInverse
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTripleNative
import OAI.Computability.BorderVNP.CubeTeamOwnedDiagonalSound
import OAI.Computability.BorderVNP.CubeTeamOwnedReturn

/-! # Public vertex lookup column on every passing native team history

Every complete native return, with any admitted private choices, recovers
exactly the publicly selected packet, vertex and bank address at each
chronological row. Its attached private data can depend on those choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks
open BorderVNP.Cube.TeamRowSources BorderVNP.Cube.Tally VPVNP.BurstRAM RoutingISA
open scoped Classical

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout} {A : Data n l.d blocks b h K s}
variable {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ} {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ}
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {original m mt : Memory w} {r t : Bank w} {es : List (TeamRAM.Event w)}
variable (P : PhysicalSetup A owner power base stop actual claimed rows pub original)

include P in
private theorem role_return (v : Fin l.d × Fin l.d) (own : owner v.1=l.teamID) (same : ∀ a ∈ source l power n, m a=original a)
    (old : Past (l := l) A owner base (key v) m) (cur : readings r 7=base+3*vertexPrefix l (wordOwner owner) n blocks (key v))
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key v) (.ofWords r m))
    (run : Runs pub mac (if v.1=v.2 then diagonalRole n b h K s else strictRole n b h K s) r m es t mt) :
    StepReturn A owner power base stop v r m t mt := by
  rcases v with ⟨x,y⟩
  change Runs pub mac (if x=y then _ else _) _ _ _ _ _ at run
  rcases lt_trichotomy x y with less | rfl | greater
  · rw [ite_eq_right less.ne] at run
    exact strict_step_sound P ⟨(x,y),less⟩ false own same old cur prep run
  · rw [ite_eq_left rfl] at run
    obtain ⟨_,vert,idx,lim,_,_,src,keep⟩ := P.diagonal_role_sound x same prep run
    let q := finProdFinEquiv (x,x)
    have pair : pairAt l.d q=(x,x) := finProdFinEquiv.symm_apply_apply _
    have baseLe : base ≤ stop := (Nat.le_add_right ..).trans P.capacity
    exact ⟨old.diagonal q (by rw [pair]) (fun a lo _ => keep a lo),src,fun a top => keep a (baseLe.trans top),
      by simpa only [ite_true,Nat.add_zero] using vert,idx,lim⟩
  · rw [ite_eq_right greater.ne'] at run
    exact strict_step_sound P ⟨(y,x),greater⟩ true own same old cur prep run

/-- Public directory and immutable data at the output of an arbitrary successful
native traversal. Each position names a concrete entry of the assigned team list. -/
structure PublicColumn (A : Data n l.d blocks b h K s) (owner : Fin l.d → ℕ) (power base stop : ℕ)
    (original mem : Memory w) : Prop where
  count : readings mem (l.frame+46)=(CubeVisits.teamList A.axis blocks owner l.teamID).length
  pointer : readings mem (l.frame+78)=base
  triples : ∀ i, (visits (l := l) A owner i).tripleAt (readings mem) (base+3*i.val)
  sourceWords : ∀ a ∈ source l power n, a ≠ l.frame+46 → mem a=original a
  above : ∀ a, stop ≤ a → mem a=original a

include P in
/-- Invert the complete native program, carrying an additional RAM invariant
through each physically owned role up to the last count publication. -/
theorem native_return_induction (J : Memory w → Prop) (initial : J original)
    (advance : ∀ (v : Fin l.d × Fin l.d) (u : Bank w) (mu : Memory w) (fs : List (TeamRAM.Event w)) (z : Bank w) (mz : Memory w),
      owner v.1=l.teamID → (∀ a ∈ source l power n, mu a=original a) →
      readings u 7=base+3*vertexPrefix l (wordOwner owner) n blocks (key v) →
      TeamRowPrepare.ReadyRow l (readings mu) (key v) (.ofWords u mu) →
      Runs pub mac (if v.1=v.2 then diagonalRole n b h K s else strictRole n b h K s) u mu fs z mz → J mu → J mz)
    (run : Runs pub mac (ownedGroups n b h K s) r original es t mt) :
    ∃ H : OwnedReturnTrace pub mac l n b h K s r original es t mt,
      DiagonalResidueRAM.TraceOK es (H.rows.flatMap (List.flatMap TeamRAM.Event.choices)) es.length ∧
        PublicColumn (l := l) A owner power base stop original mt ∧ J H.pre ∧
        mt=publishVertexCount H.pre l.frame (vertexPrefix l (wordOwner owner) n blocks (l.d*l.d)) := by
  let I (q : ℕ) (mu : Memory w) :=
    (∀ a ∈ source l power n, mu a=original a) ∧ Past (l := l) A owner base q mu ∧
      (∀ a, stop ≤ a → mu a=original a) ∧ J mu
  have start : I 0 original := ⟨fun _ _ => rfl,past_zero A owner base original,fun _ _ => rfl,initial⟩
  have digits (q : Fin (l.d*l.d)) : wordOwner owner (q.val/l.d)=owner (pairAt l.d q).1 := by
    have lower : q.val/l.d < l.d := (pairAt l.d q).1.isLt
    simp only [wordOwner,dite_eq_left lower]; rfl
  have skip (q : ℕ) (hq : q<l.d*l.d) (miss : wordOwner owner (q/l.d)≠l.teamID)
      (mu : Memory w) (old : I q mu) : I (q+1) mu := by
    let pos : Fin (l.d*l.d) := ⟨q,hq⟩
    exact ⟨old.1,old.2.1.skip pos ((digits pos) ▸ miss),old.2.2⟩
  have step (q : ℕ) (hq : q<l.d*l.d) (own : wordOwner owner (q/l.d)=l.teamID)
      (u : Bank w) (mu : Memory w) (old : I q mu) (cur : readings u 7=base+3*vertexPrefix l (wordOwner owner) n blocks q)
      (prep : TeamRowPrepare.ReadyRow l (readings mu) q (.ofWords u mu)) (fs : List (TeamRAM.Event w)) (z : Bank w) (mz : Memory w)
      (row : Runs pub mac (if q/l.d=q%l.d then diagonalRole n b h K s else strictRole n b h K s) u mu fs z mz) :
      I (q+1) mz ∧ readings z 7=readings u 7+(if q/l.d=q%l.d then 0 else 3*strictVertices n l.d blocks) ∧
        readings z 22=q ∧ readings z 23=l.d*l.d := by
    let pos : Fin (l.d*l.d) := ⟨q,hq⟩
    let v := pairAt l.d pos
    have vk : key v=q := congrArg Fin.val (finProdFinEquiv.apply_symm_apply pos)
    have same : (q/l.d=q%l.d)=(v.1=v.2) := propext (show v.1.val=v.2.val ↔ _ from Fin.val_inj)
    have rr : Runs pub mac (if v.1=v.2 then diagonalRole n b h K s else strictRole n b h K s) u mu fs z mz := by
      by_cases hit : v.1=v.2
      · simpa only [ite_eq_left hit,ite_eq_left (same.mpr hit)] using row
      · simpa only [ite_eq_right hit,ite_eq_right (fun h => hit (same.mp h))] using row
    have ret := role_return P v ((digits pos) ▸ own) old.1 (vk.symm ▸ old.2.1) (vk.symm ▸ cur) (vk.symm ▸ prep) rr
    exact ⟨⟨fun a inSrc => (ret.sourceWords a inSrc).trans (old.1 a inSrc),vk ▸ ret.next,
      fun a top => (ret.above a top).trans (old.2.2.1 a top),
      advance v u mu fs z mz ((digits pos) ▸ own) old.1 (vk.symm ▸ cur) (vk.symm ▸ prep) rr old.2.2.2⟩,by simpa only [same] using ret.vertex,ret.cursor.trans vk,ret.bound⟩
  obtain ⟨H,_,⟨src,past,above,invariant⟩,cur,pubEq,_⟩ := ownedGroups_return_induction n blocks b h K s l (wordOwner owner) I base
    P.fits P.seed.frame start (fun _ _ hi => P.inventory hi.1) skip step run
  have ptr := (P.inventory src).2.1
  obtain ⟨count,here,triples⟩ := published A owner base H.pre t past ptr (frame_before P) cur
  refine ⟨H,H.traceOK,?_,invariant,pubEq⟩
  rw [pubEq]
  refine ⟨count,here,triples,fun a inSrc ne => (publishVertexCount_other _ _ _ _ ne).trans (src a inSrc),?_⟩
  intro a top
  have before := frame_before P
  have room : base ≤ stop := (Nat.le_add_right ..).trans P.capacity
  exact (publishVertexCount_other _ _ _ _ (by omega)).trans (above a top)

include P in
/-- Every native traversal recovers its field-46 and field-78 readback,
selector and vertex column, and exact chronological private word. -/
theorem native_return (run : Runs pub mac (ownedGroups n b h K s) r original es t mt) :
    ∃ H : OwnedReturnTrace pub mac l n b h K s r original es t mt,
      DiagonalResidueRAM.TraceOK es (H.rows.flatMap (List.flatMap TeamRAM.Event.choices)) es.length ∧
        PublicColumn (l := l) A owner power base stop original mt := by
  obtain ⟨H,ok,col,_,_⟩ := native_return_induction P (fun _ => True) trivial (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial) run
  exact ⟨H,ok,col⟩

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
