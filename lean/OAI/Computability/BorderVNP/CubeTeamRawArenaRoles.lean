import OAI.Computability.BorderVNP.CubeTeamRawArenaSides

/-! # Native returning roles preserve the raw scan's actual source and cursors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned
open BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources BorderVNP.Cube.TeamRows
open BorderVNP.Cube.Scatter OwnedStages CellDispatch

variable {a : Layout} {w frame team : ℕ} {decl : LengthDeclaration a.n a.header.d} {copies : 1 ≤ a.K}
variable {owner : Fin a.header.d → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {original m mt : Memory w} {r t : Bank w} {es : List (TeamRAM.Event w)}

/-- Actual received selector-prefix words in every directed view incident with the team. -/
def Layout.RawPrefixes (a : Layout) {w : ℕ} (frame team : ℕ) (decl : LengthDeclaration a.n a.header.d)
    (owner : Fin a.header.d → ℕ) (raw : Symbols a.header.d → List Bool) (original : Memory w) : Prop :=
  let l := a.scanner frame team decl.1.val a.rowSelectorBits
  ∀ p high, owner (oriented p high).1 = team →
    (raw p).length = 2*a.header.blocks*(a.header.d.choose 2)^a.n*selectorWidth a.n a.K a.h ∧
      Resident (source l a.powerBase a.n) original (l.view (key (oriented p high))) (raw p)

private theorem strictRoleReturn (P : a.RawInputs frame team decl copies owner pub original)
    {raw : Symbols a.header.d → List Bool} (views : a.RawPrefixes frame team decl owner raw original)
    (p : Symbols a.header.d) (high : Bool) (owned : owner (oriented p high).1 = team) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    let q := key (oriented p high)
    let src := source l a.powerBase a.n
    (∀ x ∈ src, m x = original x) → readings r 7 = a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q →
    TeamRowPrepare.ReadyRow l (readings m) q (.ofWords r m) →
    Runs pub mac (strictRole a.n a.b a.h a.K a.s) r m es t mt →
    (∀ x ∈ src, mt x = m x) ∧ readings t 7 = readings r 7+3*strictVertices a.n a.header.d a.header.blocks ∧
      readings t 22 = q ∧ readings t 23 = a.header.d*a.header.d := by
  intro l q src same cursor prep run
  obtain ⟨_,u,mu,_,_,side,checker⟩ := seq_split run
  obtain ⟨len,bits⟩ := views p high owned
  obtain ⟨z,keep,ctrl,_,out,S,_,stored⟩ := P.strictSide p high (raw p) owned same cursor prep len (bits.congr same) side
  let v := a.checkAddresses
  have test := (LocalRow.strictChecked_run pub mac u mu (v.layout a.header.d a.header.blocks a.b a.h) decl.1 p
    a.b a.h a.K a.s v.actual v.claimed S decl.2 z.loaded z.actual z.claimed z.table z.space rfl
    P.labelsFit P.packetFit P.capFit stored z.entry.zero z.entry.one z.entry.axis z.entry.left z.entry.right).sound checker
  have ret := test.2
  refine ⟨fun x hx => (Fin.ext (ret.outside x (P.checkSafe x hx))).trans (keep x hx),?_,
    ret.cursor.trans ((congrArg Fin.val (ctrl 22 (by decide) (by decide))).trans prep.cursor),
    ret.bound.trans ((congrArg Fin.val (ctrl 23 (by decide) (by decide))).trans prep.bound)⟩
  have restore : readings t 7 = readings u 7 := ret.vertex
  rw [restore,out,cursor]
  simp only [l,q,strictVertices,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]

private theorem diagonalRoleReturn (P : a.RawInputs frame team decl copies owner pub original) (g : Fin a.header.d) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    let q := key (g,g)
    let src := source l a.powerBase a.n
    (∀ x ∈ src, m x = original x) → TeamRowPrepare.ReadyRow l (readings m) q (.ofWords r m) →
    Runs pub mac (diagonalRole a.n a.b a.h a.K a.s) r m es t mt →
    (∀ x ∈ src, mt x = m x) ∧ readings t 7 = readings r 7 ∧ readings t 22 = q ∧ readings t 23 = a.header.d*a.header.d := by
  intro l q src same prep run
  let A := a.addressData decl.1 copies
  have ready := diagonal_ready P.seed P.allocation g r ((Nat.le_add_right ..).trans P.capacity) same prep
  have fr : (pub 0).val = l.frame := P.seed.frame
  obtain ⟨_,vert,cur,bound,_,_,safe,_⟩ := diagonal_role_recover (l := l) (A := A) g ready
    (fr ▸ frame_protected (A := A) (l := l) (power := a.powerBase)) (P.image.transfer same) P.checker P.labelsFit P.capFit P.afterScratch
    P.allocation.orderSingles P.checkSafe run
  exact ⟨safe,vert,cur.trans prep.cursor,bound.trans prep.bound⟩

/-- Invert the real branch selected by the quotient and remainder. Both directed
orientations are included, even when a single team owns both symbols. -/
theorem Layout.RawInputs.visit (P : a.RawInputs frame team decl copies owner pub original)
    {raw : Symbols a.header.d → List Bool} (views : a.RawPrefixes frame team decl owner raw original)
    (q : Fin (a.header.d*a.header.d)) :
    let l := a.scanner frame team decl.1.val a.rowSelectorBits
    let src := source l a.powerBase a.n
    wordOwner owner (q.val/l.d) = team → (∀ x ∈ src, m x = original x) →
    readings r 7 = a.vertexBase+3*vertexPrefix l (wordOwner owner) a.n a.header.blocks q.val →
    TeamRowPrepare.ReadyRow l (readings m) q.val (.ofWords r m) →
    Runs pub mac (if q.val/l.d = q.val%l.d then diagonalRole a.n a.b a.h a.K a.s else strictRole a.n a.b a.h a.K a.s) r m es t mt →
    (∀ x ∈ src, mt x = m x) ∧ readings t 7 = readings r 7+(if q.val/l.d = q.val%l.d then 0 else 3*strictVertices a.n l.d a.header.blocks) ∧
      readings t 22 = q.val ∧ readings t 23 = l.d*l.d := by
  intro l src owned same cursor prep run
  let v := pairAt a.header.d q
  have keyAt : key v = q.val := congrArg Fin.val (finProdFinEquiv.apply_symm_apply q)
  have digits := key_digits v
  rw [keyAt] at digits
  change wordOwner owner (q.val/a.header.d) = team at owned
  have owns : owner v.1 = team := by simpa only [digits.1,wordOwner,dite_eq_left v.1.isLt] using owned
  have eqn : q.val/l.d = q.val%l.d ↔ v.1 = v.2 := by
    change q.val/a.header.d = q.val%a.header.d ↔ _
    rw [digits.1,digits.2]; exact ⟨Fin.ext,congrArg Fin.val⟩
  have strict (p : Symbols a.header.d) (high : Bool) (order : oriented p high = v) (different : v.1 ≠ v.2) :
      (∀ x ∈ src, mt x = m x) ∧ readings t 7 = readings r 7+3*strictVertices a.n l.d a.header.blocks ∧
        readings t 22 = q.val ∧ readings t 23 = l.d*l.d := by
    have ho := order.symm ▸ owns
    have k : key (oriented p high) = q.val := (congrArg key order).trans keyAt
    have path := (ite_eq_right (different ∘ eqn.mp)) ▸ run
    have ret := strictRoleReturn P views p high ho same (k.symm ▸ cursor) (k.symm ▸ prep) path
    exact ⟨ret.1,ret.2.1,ret.2.2.1.trans k,ret.2.2.2⟩
  rcases lt_trichotomy v.1 v.2 with lo | eq | hi
  · rw [ite_eq_right (lo.ne ∘ eqn.mp)]
    exact strict ⟨v,lo⟩ false rfl lo.ne
  · rw [ite_eq_left (eqn.mpr eq),Nat.add_zero]
    have k : key (v.1,v.1) = q.val := by rw [eq,show (v.2,v.2) = v from Prod.ext eq.symm rfl]; exact keyAt
    have path := (ite_eq_left (eqn.mpr eq)) ▸ run
    have ret := diagonalRoleReturn P v.1 same (k.symm ▸ prep) path
    exact ⟨ret.1,ret.2.1,ret.2.2.1.trans k,ret.2.2.2⟩
  · rw [ite_eq_right (hi.ne' ∘ eqn.mp)]
    exact strict ⟨v.swap,hi⟩ true rfl hi.ne'

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
