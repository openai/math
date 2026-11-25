import OAI.Hierarchy.ProtocolRAMTurnRead

namespace OAI
/-! # Authenticating a native itinerary field only on the positive row that reads it -/

namespace Hierarchy.ProtocolRAMTurnItinerary
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open ProtocolRAM
open scoped Fin.CommRing
variable {W N : ℕ}

structure Chart.Row (p : Chart) (m : Memory W) (x : Word W) (t : Turn) : Prop where
  item : p.item.eval m x=(t.item:Word W)
  origin : p.origin.eval m x=(t.origin:Word W)
  length : p.length.eval m x=(t.length:Word W)
  position : p.position.eval m x=(t.position:Word W)
  reverse : p.reverse.eval m x=(t.reverse.toNat:Word W)
  width : p.width.eval m x=(t.width:Word W)
  site : p.site.eval m x=(t.site:Word W)
  seat : p.seat.eval m x=(t.seat:Word W)

/-- Reads at either original boundary or one of the (at most two) adjacent
occurrences. Even an inhabited edge catalogue can have dormant rows without
any physical input port. They do not occur among these hypotheses. -/
structure Banks.Adjacent (b : Banks) (v : Values) (m : Memory W) (t : Turn) : Prop where
  oldSource : t.boundary false → b.oldSource.read m (t.item:Word W)=(v.oldSource t.item:Word W)
  oldTarget : t.boundary true → b.oldTarget.read m (t.item:Word W)=(v.oldTarget t.item:Word W)
  starts : ∀s, ¬t.boundary s → b.starts.read m ((4*t.occurrence s:ℕ):Word W)=(v.starts (t.occurrence s):Word W)
  edge : ∀s, ¬t.boundary s → b.edge.read m (t.occurrence s:Word W)=(v.edge (t.occurrence s):Word W)
  tailSite : ∀s, ¬t.boundary s → b.tailSite.read m (v.edge (t.occurrence s):Word W)=(v.tailSite (v.edge (t.occurrence s)):Word W)
  tailRole : ∀s, ¬t.boundary s → b.tailRole.read m (v.edge (t.occurrence s):Word W)=(v.tailRole (v.edge (t.occurrence s)):Word W)
  headRole : ∀s, ¬t.boundary s → b.headRole.read m (v.edge (t.occurrence s):Word W)=(v.headRole (v.edge (t.occurrence s)):Word W)
  tailFits : ∀s, ¬t.boundary s → v.tailSite (v.edge (t.occurrence s))<2^W

private theorem lossless {a b : ℕ} (ha : a < 2^W) (hb : b < 2^W) :
    ((a:Word W)=(b:Word W)) ↔ a=b := by
  rw [Fin.ext_iff,Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]

theorem boundary_at {p : Chart} {m : Memory W} {x : Word W} {t : Turn}
    (rd : p.Row m x t) (s : Bool) (yes no : Expr) (pos : t.position < 2^W) (len : t.length < 2^W) :
    (onEnd p s yes no).eval m x=(if t.position=(if s then t.length else 0) then yes.eval m x else no.eval m x) := by
  have zd : 2^W ∣ t.position ↔ t.position=0 :=
    ⟨fun h=>Nat.eq_zero_of_dvd_of_lt h pos,fun h=>h ▸ dvd_zero _⟩
  cases s <;> simp [onEnd,Expr.eval,Comparison.test,rd.position,rd.length,lossless pos len,zd]

theorem occurrence_at {p : Chart} {m : Memory W} {x : Word W} {t : Turn}
    (rd : p.Row m x t) (s : Bool) (one : 1 < 2^W) (inside : t.position ≤ t.length) (hop : ¬t.boundary s) :
    (occurrence p s).eval m x=(t.occurrence s:Word W) := by
  have nz : (1:Word W)≠0 := fun same=>Nat.one_ne_zero ((lossless one (Nat.two_pow_pos W)).mp same)
  cases s <;> cases h : t.reverse <;>
    simp (disch := omega) [occurrence,Turn.occurrence,Turn.boundary,plus,minus,Expr.eval,RowOp.opcode,
      BinaryOp.eval,Comparison.test,rd.origin,rd.position,rd.length,rd.reverse,h,nz,
      Nat.cast_add,Nat.cast_sub] at hop ⊢
  · rw [Nat.cast_sub (by omega : 1 ≤ t.position),Nat.cast_one]
  · rw [Nat.cast_sub (by omega : 1 ≤ t.length-t.position),Nat.cast_sub inside,Nat.cast_one]

theorem role_at {p : Chart} {m : Memory W} {x : Word W} {t : Turn} {b : Banks} {v : Values}
    (rd : p.Row m x t) (address : b.Adjacent v m t) (s : Bool) (one : 1 < 2^W)
    (inside : t.position ≤ t.length) (len : t.length < 2^W) (small : t.site < 2^W) :
    (role p b s).eval m x=(t.role v s:Word W) := by
  classical
  rw [role,boundary_at rd s _ _ (inside.trans_lt len) len]
  by_cases atEnd : t.boundary s
  · have hp : t.position=(if s then t.length else 0) := atEnd
    simp only [Turn.role,atEnd,hp,ite_true]
    cases s
    · exact (congrArg (b.oldSource.read m) rd.item).trans (address.oldSource atEnd)
    · exact (congrArg (b.oldTarget.read m) rd.item).trans (address.oldTarget atEnd)
  · have hp : ¬t.position=(if s then t.length else 0) := atEnd
    simp only [Turn.role,atEnd,hp,ite_false]
    simp only [Expr.eval,Comparison.test,occurrence_at rd s one inside atEnd,address.edge s atEnd,
      address.tailSite s atEnd,address.tailRole s atEnd,address.headRole s atEnd,rd.site,
      beq_iff_eq,lossless (address.tailFits s atEnd) small]
    by_cases same : v.tailSite (v.edge (t.occurrence s))=t.site <;> simp [same]

theorem start_at {p : Chart} {m : Memory W} {x : Word W} {t : Turn} {b : Banks} {v : Values}
    (rd : p.Row m x t) (address : b.Adjacent v m t) (s : Bool) (one : 1 < 2^W)
    (inside : t.position ≤ t.length) (len : t.length < 2^W) :
    (start p b s).eval m x=(t.start v s:Word W) := by
  classical
  rw [start,boundary_at rd s _ _ (inside.trans_lt len) len]
  by_cases atEnd : t.boundary s
  · have hp : t.position=(if s then t.length else 0) := atEnd
    simp only [Turn.start,atEnd,hp,ite_true,Expr.eval,Nat.cast_zero]
  · have hp : ¬t.position=(if s then t.length else 0) := atEnd
    simp only [Turn.start,atEnd,hp,ite_false]
    change b.starts.read m ((four _).eval m x)=_
    rw [eval_four,occurrence_at rd s one inside atEnd]
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using address.starts s atEnd

/-- Every actual chronology row has a position within its own (possibly empty)
route, regardless of orientation. A zero original width is copied even if the
orientation lookup uses arbitrary dormant endpoint words. -/
theorem width_at (p : Chart) (m : Memory W) (x : Word W) (n : ℕ)
    (width : p.width.eval m x=(n:Word W))
    (within : ¬p.length.eval m x < p.position.eval m x) : (live p).eval m x=(n:Word W) := by
  simp [live,Expr.eval,Comparison.test,within,width]

theorem observed_live (base : ℕ) (p : Chart) (b : Banks) (r : Fin N → Turn) (v : Values) (m : Memory W)
    (one : 1 < 2^W) (fit : ∀ f,(field p b f).Fits W base) (room : base+7*N < 2^W)
    (within : ∀i,(r i).position ≤ (r i).length)
    (weights : ∀i,(live p).eval m (i.val:Word W)=((r i).width:Word W))
    (active : ∀i,0<(r i).width → p.Row m (i.val:Word W) (r i) ∧ b.Adjacent v m (r i) ∧
      (r i).length < 2^W ∧ (r i).site < 2^W) :
    ∃ out,(program W base N p b).Exec m out (ticks base N p b) ∧
      (∀ (i : Fin N) (f : Fin 7), f=4 ∨ (r i).field v 4≠0 →
        out (base+f.val*N+i.val)=((r i).field v f:Word W)) ∧
      ∀ a,a<base ∨ base+7*N≤a → out a=m a := by
  obtain ⟨out,exec,read,frame⟩ := run base p b m fit room
  refine ⟨out,exec,?_,frame⟩
  intro i f relevant
  have atWidth : (r i).field v 4=(r i).width := ite_eq_right (Nat.not_lt_of_ge (within i))
  rw [read]
  rcases relevant with rfl|pos
  · rw [atWidth]
    exact weights i
  · rw [atWidth] at pos
    obtain ⟨rd,ad,len,site⟩ := active i (Nat.pos_of_ne_zero pos)
    fin_cases f
    · exact role_at rd ad false one (within i) len site
    · exact role_at rd ad true one (within i) len site
    · exact start_at rd ad false one (within i) len
    · exact start_at rd ad true one (within i) len
    · change (live p).eval m (i.val:Word W)=((r i).field v (4:Fin 7):Word W)
      rw [atWidth]
      exact weights i
    · exact rd.site
    · exact rd.seat

end Hierarchy.ProtocolRAMTurnItinerary

end OAI
