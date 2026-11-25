import OAI.Computability.BorderVNP.CubeISALocalRowCleared
import OAI.Computability.BorderVNP.CubeISALocalRowFrame
import OAI.Computability.BorderVNP.CubeISALocalRowSpace
import OAI.Computability.BorderVNP.CubeISALengthImage

/-! # Combining the genuine local initialization with the guarded role traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube OwnedRowSetup

/-- Words unaffected by a complete role tally. Its only mutable intervals
are the temporary subtotal and the consecutive descriptor and digit scratch. -/
def Protected (n h actual descriptor x : ℕ) : Prop :=
  (x < actual ∨ actual+(n+1) ≤ x) ∧ (x < descriptor ∨ descriptor+8+h ≤ x)

/-- A complete verified row restores all three caller cursors and the physically
recomputed row. All data outside its two temporary reservations survives. -/
structure Return {n : ℕ} (h actual descriptor : ℕ) (r : Reg → ℕ) (m : ℕ → ℕ)
    (values : Fin (n+1) → ℕ) (z : NatState) : Prop where
  vertex : z.reg 7 = r 7
  cursor : z.reg 22 = r 22
  bound : z.reg 23 = r 23
  row : ∀ j : Fin (n+1), z.mem (actual+j.val) = values j
  outside : ∀ x, Protected n h actual descriptor x → z.mem x = m x

private theorem keptTest {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {c : Code}
    {r : Bank w} {m : Memory w} {cost : ℕ} {ok : Prop} {P : NatState → Prop}
    (ret : TestRun pub mac c r m cost ok P) :
    TestRun pub mac c r m cost ok (fun z => P z ∧ ∀ k, c.keeps k = true → z.reg k = readings r k) :=
  ⟨fun good => withKeptRegs (ret.complete good), fun run => ⟨(ret.sound run).1,(ret.sound run).2,
    fun _ hk => congrArg Fin.val (run.keepsReg hk)⟩⟩

/-- A row-major stored public table supplies the exact addressed vector for a
sorted pair, including the diagonal case. -/
theorem atPair_stored {d n base : ℕ} {m : ℕ → ℕ} {rows : Sym2 (Fin d) → Fin (n+1) → ℕ}
    (stored : CubeLengths.StoredRows m base rows) (lo hi : Fin d) (sort : lo ≤ hi)
    (j : Fin (n+1)) : m (atPair base d n lo.val hi.val+j.val) = rows (Sym2.mk lo hi) j := by
  simpa only [CubeLengths.entryOrder_val,ite_eq_left sort,atPair,Nat.add_assoc] using stored lo hi j

/-- Generic concrete sequence for a strict or diagonal role. The only dependent
callback below is the already-implemented native tally body, supplied at its
true cleared physical state. -/
theorem role_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (l : Layout) (i : Fin (n+1)) (lo hi : Fin l.d)
    (b h K s actual claimed : ℕ) (body : Code) (bodyCost : ℕ) (ok : Prop) (values : Fin (n+1) → ℕ)
    (loaded : l.Loaded n (readings pub) (readings m)) (A : readings m l.header = actual)
    (D : readings m (l.header+1) = claimed) (space : Space l w n b h K s (readings pub 0) actual claimed)
    (h0 : readings r 0 = 0) (h1 : readings r 1 = 1) (axis : readings r 4 = i.val)
    (left : readings r 14 = lo.val) (right : readings r 15 = hi.val)
    (keep : ∀ k : Reg, k = 22 ∨ k = 23 → (Code.seq (setup n b h K s) (.seq clear body)).keeps k = true)
    (pass : ∀ t mt, Cleared l b h K s actual (atPair claimed l.d n lo.val hi.val) (readings r 7)
      i lo hi (.ofWords t mt) →
      (∀ x, Protected n h actual (head l n b h K s) x → readings mt x = readings m x) →
      TestRun pub mac body t mt bodyCost ok (fun z => z.reg 7 = readings r 7 ∧
        (∀ j, z.mem (actual+j.val) = values j) ∧
        ∀ x, Protected n h actual (head l n b h K s) x → z.mem x = readings mt x)) :
    TestRun pub mac (.seq (setup n b h K s) (.seq clear body)) r m
      ((setup n b h K s).slots+(4*(n+1)+1+bodyCost)) ok
      (Return h actual (head l n b h K s) (readings r) (readings m) values) := by
  let hd := head l n b h K s
  let claim := atPair claimed l.d n lo.val hi.val
  have bound := bank_le_head l n b h K s
  have hA := space.beforeClaim
  have hB := space.beforeBank
  have endRoom := space.endRoom
  have setupDet : (setup n b h K s).deterministic = true := by
    have hc := strictChecked_deterministic n b h K s
    change ((setup n b h K s).deterministic && _) = true at hc
    exact (Bool.and_eq_true_iff.mp hc).1
  let P := fun z : NatState => z.reg 7 = readings r 7 ∧ (∀ j : Fin (n+1), z.mem (actual+j.val) = values j) ∧
    ∀ x, Protected n h actual hd x → z.mem x = readings m x
  have test : TestRun pub mac (.seq (setup n b h K s) (.seq clear body)) r m
      ((setup n b h K s).slots+(4*(n+1)+1+bodyCost)) (True ∧ True ∧ ok) P := by
    apply ((setup_run pub mac r m l i lo hi b h K s actual claimed loaded A D space h0 h1 axis left right).asTest setupDet).seq
    rintro u mu ⟨ready,keepM⟩
    apply ((clearReady_run pub mac u mu l i lo hi b h K s actual claim (readings r 7) ready
      (by omega) (by omega)).asTest (by decide)).seq
    rintro v mv ⟨clearState,unchanged⟩
    have same (x : ℕ) (hx : Protected n h actual hd x) : readings mv x = readings m x := by
      rcases hx with ⟨out,area⟩
      exact (unchanged x out).trans (keepM x (area.imp_right (fun _ => by omega)))
    apply (pass v mv clearState same).mono le_rfl Iff.rfl
    rintro z ⟨vertex,rows,rest⟩
    exact ⟨vertex,rows,fun x hx => (rest x hx).trans (same x hx)⟩
  apply (keptTest test).mono le_rfl (by simp)
  rintro z ⟨⟨vertex,rows,rest⟩,ret⟩
  exact ⟨vertex,ret 22 (keep 22 (.inl rfl)),ret 23 (keep 23 (.inr rfl)),rows,rest⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
