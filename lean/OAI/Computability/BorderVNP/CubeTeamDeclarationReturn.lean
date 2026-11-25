import OAI.Computability.BorderVNP.CubeTeamDeclarationChecks
import OAI.Computability.BorderVNP.CubeTeamPublicMinimumReturn

/-! # Recovering the unique declaration from the distributed native verifiers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA Cube.Physical Cube.Physical.Owned Cube.Tally VPVNP.BurstRAM TeamRowPrepare

variable {Team : Type*} {w n d blocks b h K s : ℕ}

/-- Actual ordered-visit histories, their propagated memory state, and the owner cell read
by the dispatch instruction. These data are independent of the selector tuple. -/
structure DispatchScans (owner : Fin d → Team) (pub : Team → Arg → Word w)
    (mac : Team → TeamOpcode.Macros w 8) (n b h K s : ℕ) where
  /-- The actual row dispatcher layout on each team. -/
  scanLayout : Team → Layout
  /-- All teams scan the same alphabet. -/
  dimension : ∀ team, (scanLayout team).d = d
  /-- Memory invariant at a real ordered-pair cursor. -/
  resident : Team → ℕ → Word w → Memory w → Prop
  /-- Native row-by-row history obtained from each team return. -/
  history : ∀ team, ∃ r m rows es t mt, resident team 0 (r 7) m ∧
    ReturnedRows (pub team) (mac team) (scanLayout team) (strictRole n b h K s) (diagonalRole n b h K s)
      0 r m rows es t mt
  /-- The memory invariant survives every reached native visit, including skipped rows. -/
  advance : ∀ team {q r m es t mt}, q < (scanLayout team).d*(scanLayout team).d → resident team q (r 7) m →
    ReadyRow (scanLayout team) (readings m) q (.ofWords r m) →
    Visit (pub team) (mac team) (scanLayout team) (strictRole n b h K s) (diagonalRole n b h K s) q r m es t mt →
    resident team (q+1) (t 7) mt
  /-- On the team assigned the first symbol, the actual owner probe identifies that team. -/
  owns : ∀ (x y : Fin d) {v : Word w} (m : Memory w), resident (owner x) (finProdFinEquiv (x,y)).val v m →
    readings m ((scanLayout (owner x)).ownerBase+x.val) = (scanLayout (owner x)).teamID

/-- The reached check states for a shared selector tuple in real team traversals. The
supplied facts concern only the addressed frame, table and selector words. -/
structure CheckedScans (owner : Fin d → Team) (pub : Team → Arg → Word w)
    (mac : Team → TeamOpcode.Macros w 8) (decl : LengthDeclaration n d)
    (select : Packet n d blocks → Selector n K h) (b s : ℕ) extends DispatchScans owner pub mac n b h K s where
  /-- Addressed checker entry and stored selector words produced by an actual strict scatter.
  Only the lower owner's canonical orientation is used to recover a strict row. -/
  strict : ∀ (p : Symbols d) {r m gs u mu},
    resident (owner p.val.1) (finProdFinEquiv p.val).val (r 7) m →
    ReadyRow (scanLayout (owner p.val.1)) (readings m) (finProdFinEquiv p.val).val (.ofWords r m) →
    Runs (pub (owner p.val.1)) (mac (owner p.val.1)) (OwnedStages.strictSide n b h K s) r m gs u mu →
    ∃ v : CheckAddresses, CheckWords blocks b h K s v (pub (owner p.val.1)) decl p.val.1 p.val.2 u mu ∧
      ∀ z : {z : Packet n d blocks // z.1.1 decl.1 = p}, SelectorRead.Stored (readings mu)
        (v.bank+packetIndex z.val*bankWidth n b h K s) (select z.val)
  /-- Addressed checker entry produced by an actual repeated-symbol scatter. -/
  diagonal : ∀ (x : Fin d) {r m gs u mu}, resident (owner x) (finProdFinEquiv (x,x)).val (r 7) m →
    ReadyRow (scanLayout (owner x)) (readings m) (finProdFinEquiv (x,x)).val (.ofWords r m) →
    Runs (pub (owner x)) (mac (owner x)) (OwnedStages.diagonalSide n) r m gs u mu →
    ∃ v : CheckAddresses, CheckWords blocks b h K s v (pub (owner x)) decl x x u mu

variable {owner : Fin d → Team} {pub : Team → Arg → Word w} {mac : Team → TeamOpcode.Macros w 8}
    {decl : LengthDeclaration n d} {select : Packet n d blocks → Selector n K h}

/-- At the row's canonical owner, the diagonal and strict return paths both force the
advertised vector. This holds even when the strict pair has the same owner at both ends. -/
theorem CheckedScans.row_counts (runs : CheckedScans owner pub mac decl select b s)
    (labels : d^(n+1) ≤ 2^w) (packets : packetTrials n d blocks*(h*s) < 2^w)
    (cap : declarationCap n d blocks b h s < 2^w) :
    ∀ row j, decl.2 row j = subtotals itemRow (crossCount b s select) decl.1 row j := by
  have canonical (x y : Fin d) (order : x ≤ y) : ∀ j, decl.2 (Sym2.mk x y) j =
      subtotals itemRow (crossCount b s select) decl.1 (Sym2.mk x y) j := by
    let q := finProdFinEquiv (x,y)
    let team := owner x
    have shape := runs.dimension team
    obtain ⟨r,m,_,_,_,_,init,path⟩ := runs.history team
    obtain ⟨a,ma,ys,u,mu,resident,ready,visit⟩ := path.visit_at (runs.resident team) init
      (fun range hm ready visit => runs.advance team range hm ready visit) q.val (Nat.zero_le _) (by rw [shape]; exact q.isLt)
    have de : q.val / (runs.scanLayout team).d = x.val := by
      rw [shape]; exact congrArg (fun z : Fin d × Fin d => z.1.val) (finProdFinEquiv.symm_apply_apply (x,y))
    have re : q.val % (runs.scanLayout team).d = y.val := by
      rw [shape]; exact congrArg (fun z : Fin d × Fin d => z.2.val) (finProdFinEquiv.symm_apply_apply (x,y))
    have owns : readings ma ((runs.scanLayout team).ownerBase+q.val/(runs.scanLayout team).d) = (runs.scanLayout team).teamID :=
      de ▸ runs.owns x y ma resident
    cases visit with
    | skip miss => exact (miss owns).elim
    | offDiagonal _ different run =>
      have hxy : x < y := lt_of_le_of_ne order (fun eqn => different (de.trans ((congrArg Fin.val eqn).trans re.symm)))
      let pair : Symbols d := ⟨(x,y),hxy⟩
      exact strictRole_counts decl select pair run (fun scatter => runs.strict pair resident ready scatter) labels packets cap
    | onDiagonal _ same run =>
      have eqn : x = y := Fin.ext (de.symm.trans (same.trans re))
      subst y
      exact diagonalRole_counts decl select x run (fun scatter => runs.diagonal x resident ready scatter) labels cap
  intro row
  induction row using Sym2.inductionOn with
  | _ x y =>
    rcases le_total x y with hxy | hyx
    · exact canonical x y hxy
    · rw [Sym2.eq_swap (a := x) (b := y)]; exact canonical y x hyx

/-- All team checks and an actual public-minimum return force both the physical declaration
and every supplied total cell. The public scanner may be any team with the parsed table. -/
theorem CheckedScans.passes (runs : CheckedScans owner pub mac decl select b s)
    (labels : d^(n+1) ≤ 2^w) (packets : packetTrials n d blocks*(h*s) < 2^w)
    (cap : declarationCap n d blocks b h s < 2^w)
    {p : Arg → Word w} {mc : TeamOpcode.Macros w 8} {r : Bank w} {m : Memory w} {es t mt}
    (minRun : Runs p mc CubeLengths.publicMinimum r m es t mt) (fit : CubeLengths.Fits w (readings p) (readings m))
    (shape : (CubeLengths.layout (readings p) (readings m)).entries = d*d*(n+1))
    (dim : (CubeLengths.layout (readings p) (readings m)).coordinates = n+1)
    (index : (CubeLengths.layout (readings p) (readings m)).chosen = decl.1.val)
    (table : CubeLengths.StoredRows (readings m) (CubeLengths.layout (readings p) (readings m)).claimed decl.2) :
    passesLengths b s select decl ∧ ∀ j : Fin (n+1),
      readings m ((CubeLengths.layout (readings p) (readings m)).totals+j.val) = ∑ row, decl.2 row j := by
  obtain ⟨least,totals⟩ := publicMinimum_return decl minRun fit shape dim index table
  exact ⟨(rows_and_minimum_iff owner b s select decl).mp ⟨fun _ _ _ => runs.row_counts labels packets cap _,least⟩,totals⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
