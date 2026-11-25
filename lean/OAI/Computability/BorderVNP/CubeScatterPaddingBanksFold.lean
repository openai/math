import OAI.Computability.BorderVNP.CubeScatterPaddingBanksFrame
import OAI.Computability.BorderVNP.CubeTeamRowFold

/-! # Owned bank readback at the end of the complete native team-row traversal

For each physical view, the ordered-pair counter reaches its designated row once.
All later rows preserve the completed view, including another side of the same packet.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding.Banks

open Physical HostAddress TeamRows VPVNP.BurstRAM RoutingISA Tally

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout}
  (A : Data n l.d blocks b h K s)

/-- Once the ordered-pair cursor has passed an owned view's row, its actual local
input is present. The per-row premise concerns only the genuine scatter's memory
image on its reserved addresses, permitting the vertex directory and tally writes. -/
theorem Data.fold_holds (owner : Fin l.d → ℕ) (step : Fin l.d → Fin l.d → ViewState w → ViewState w)
    (start : ViewState w) (sel cross : Fin l.d → Fin l.d → ℕ) (sep : A.Separate) (hw : 0 < w)
    (row : ∀ q : Fin (l.d*l.d), let p := pairAt l.d q
      let z := fold l owner step start q.val
      owner p.1 = l.teamID → ∀ a, A.BankWord a →
        (step p.1 p.2 z).mem a = A.rowMem p.1 p.2 (sel p.1 p.2) (cross p.1 p.2) z.mem a)
    (x : View n l.d blocks (h*b)) (owned : owner (x.row A.axis).1 = l.teamID)
    (k : ℕ) (past : (finProdFinEquiv (x.row A.axis)).val < k) (hk : k ≤ l.d*l.d) :
    A.Holds (fold l owner step start k).mem x := by
  let q := finProdFinEquiv (x.row A.axis)
  change q.val < k at past
  induction k with
  | zero => omega
  | succ k ih =>
    let pos : Fin (l.d*l.d) := ⟨k,hk⟩
    let p := finProdFinEquiv.symm pos
    have unfoldRow : fold l owner step start (k+1) =
        if owner p.1 = l.teamID then step p.1 p.2 (fold l owner step start k) else fold l owner step start k := by
      exact fold_succ l owner step start k hk
    rw [unfoldRow]
    by_cases here : q.val = k
    · have same : p = x.row A.axis := by
        have eq : pos = q := Fin.ext here.symm
        rw [show p = finProdFinEquiv.symm pos from rfl,eq,show q = finProdFinEquiv (x.row A.axis) from rfl,
          Equiv.symm_apply_apply]
      rw [same,ite_eq_left owned]
      have matchRow := row pos (by change owner p.1 = l.teamID; rw [same]; exact owned)
      change ∀ a, A.BankWord a → (step p.1 p.2 (fold l owner step start k)).mem a =
        A.rowMem p.1 p.2 (sel p.1 p.2) (cross p.1 p.2) (fold l owner step start k).mem a at matchRow
      rw [same] at matchRow
      exact A.holds_of_words matchRow x (A.row_hits sep hw _ _ _ x)
    · have old := ih (by omega) (by omega)
      by_cases visit : owner p.1 = l.teamID
      · rw [ite_eq_left visit]
        exact A.holds_of_words (row pos visit) x (A.row_keeps sep hw p.1 p.2 _ _ _ x old)
      · rw [ite_eq_right visit]
        exact old

/-- The final memories of the native team folds supply both actual endpoint banks of
the padded host, uniformly across singleton bits and packet demand words. -/
theorem Data.fold_endBanks {Team : Type*} (group : Fin l.d → Team) (number : Team → ℕ)
    (pack singles : Team → ℕ) (step : Team → Fin l.d → Fin l.d → ViewState w → ViewState w)
    (start : Team → ViewState w) (sel cross : Team → Fin l.d → Fin l.d → ℕ) (hw : 0 < w)
    (sep : ∀ t, (A.atTeam pack singles t).Separate)
    (row : ∀ t (q : Fin (l.d*l.d)), let p := pairAt l.d q
      let z := fold {l with teamID := number t} (number ∘ group) (step t) (start t) q.val
      number (group p.1) = number t → ∀ a, (A.atTeam pack singles t).BankWord a →
        (step t p.1 p.2 z).mem a = (A.atTeam pack singles t).rowMem p.1 p.2 (sel t p.1 p.2) (cross t p.1 p.2) z.mem a) :
    EndBanks A.axis group pack singles
      (fun t => readings (fold {l with teamID := number t} (number ∘ group) (step t) (start t) (l.d*l.d)).mem)
      (fun q => A.value q.1.val q.2) A.demand K s := by
  apply A.endBanks_of_views hw
  intro t x owned
  exact (A.atTeam pack singles t).fold_holds (l := {l with teamID := number t}) (number ∘ group) (step t)
    (start t) (sel t) (cross t) (sep t) hw (row t) x (congrArg number owned) _ (finProdFinEquiv (x.row A.axis)).isLt le_rfl

/-- Fold the concrete strict and diagonal store images themselves. Each returned team
memory has all the physical singleton and packet endpoint words, independently of its
initial memory and the native source cursor positions. -/
theorem Data.scatter_endBanks {Team : Type*} (group : Fin l.d → Team) (number : Team → ℕ)
    (pack singles : Team → ℕ) (start : Team → ViewState w) (sel cross : Team → Fin l.d → Fin l.d → ℕ)
    (hw : 0 < w) (sep : ∀ t, (A.atTeam pack singles t).Separate) :
    let step t g f (z : ViewState w) := {z with mem := (A.atTeam pack singles t).rowMem g f (sel t g f) (cross t g f) z.mem}
    EndBanks A.axis group pack singles
      (fun t => readings (fold {l with teamID := number t} (number ∘ group) (step t) (start t) (l.d*l.d)).mem)
      (fun q => A.value q.1.val q.2) A.demand K s := by
  intro step
  exact A.fold_endBanks (l := l) group number pack singles step start sel cross hw sep (fun _ _ _ _ _ => rfl)

/-- The native ordered-row program has a complete positive trace, with its prescribed
private choices, whose output memory contains every owned physical input. The inventory,
role runs and row-word equality are needed only at the genuine reached prefix states. -/
theorem Data.scan_views (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (strict diagonal : Code) (owner : Fin l.d → ℕ) (cost : ℕ → ℕ) (bits : ℕ → List Bool)
    (step : Fin l.d → Fin l.d → ViewState w → ViewState w) (r : Bank w) (m : Memory w)
    (fit : l.Fits w) (hf : readings pub 0 = l.frame)
    (inventory : ∀ q, let z := fold l owner step ⟨readings r 7,m⟩ q
      l.Fields (readings z.mem) ∧ ∀ g : Fin l.d, readings z.mem (l.ownerBase+g.val) = owner g)
    (role : ∀ q : Fin (l.d*l.d), let p := pairAt l.d q
      let z := fold l owner step ⟨readings r 7,m⟩ q.val
      let next := step p.1 p.2 z
      owner p.1 = l.teamID → ∀ u : Bank w, readings u 7 = z.out →
        TeamRowPrepare.ReadyRow l (readings z.mem) q.val (.ofWords u z.mem) →
        Owned.TraceRun pub mac (if p.1 = p.2 then diagonal else strict) u z.mem (bits q.val) (cost q.val)
          (fun t mt => readings t 7 = next.out ∧ mt = next.mem ∧ readings t 22 = q.val ∧ readings t 23 = l.d*l.d))
    (sel cross : Fin l.d → Fin l.d → ℕ) (sep : A.Separate) (hw : 0 < w)
    (row : ∀ q : Fin (l.d*l.d), let p := pairAt l.d q
      let z := fold l owner step ⟨readings r 7,m⟩ q.val
      owner p.1 = l.teamID → ∀ a, A.BankWord a →
        (step p.1 p.2 z).mem a = A.rowMem p.1 p.2 (sel p.1 p.2) (cross p.1 p.2) z.mem a) :
    Owned.TraceRun pub mac (scan strict diagonal) r m (choices l (wordOwner owner) bits)
      (ticks l (wordOwner owner) cost) (fun _ mt => ∀ x : View n l.d blocks (h*b),
        owner (x.row A.axis).1 = l.teamID → A.Holds mt x) := by
  apply (scan_fold pub mac strict diagonal l owner cost bits step r m fit hf inventory role).mono le_rfl
  intro _ _ post x own
  rw [post.2.1]
  exact A.fold_holds owner step _ sel cross sep hw row x own _ (finProdFinEquiv (x.row A.axis)).isLt le_rfl

end Cube.Padding.Banks

end BorderVNP
end Computability
end OAI
