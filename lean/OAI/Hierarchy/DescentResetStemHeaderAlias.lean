import OAI.Hierarchy.DescentResetStemHeaders

namespace OAI
/-! # A runtime optional actor pointer for the alternate packed reset header -/
namespace Hierarchy.DescentResetStemHeaders
open DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM DescriptorExpr PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def pointerBank (ptr H : ℕ) : Bank := ⟨ptr,Nat.clog 2 H⟩

/-- One runtime address per actor. The number of actors is the sentinel. -/
def Aliases {w H : ℕ} (ptr : ℕ) (alt : Fin H → Option (Fin H)) (m : Memory w) : Prop :=
  ∀ v, m (ptr+v.val) = (((alt v).elim H Fin.val : ℕ) : Word w)

def alternate (H G M b raw base ptr j : ℕ) : Expr :=
  let n := H*chunks G M
  let v := Expr.lookup (actorBank base b n) .row
  let target := Expr.lookup (pointerBank ptr H) v
  .branch .eq target (.lit H) (.lit 0)
    (.op .mask (.lookup (wideBank base b) (.lookup (rawBank raw H j) target)) (.lookup (maskBank base b n) .row))

theorem alternate_work (H G M b raw base ptr j : ℕ) : (alternate H G M b raw base ptr j).work = 45 := rfl

private theorem table_frame {w K H G M b raw base : ℕ} (m : Memory w) (a : ℕ)
    (ha : a < outputBase H G M b base) :
    (phase w K H G M b raw base).image m a=(prepare w H G M b base).image m a := by
  exact ProbeStage.Native.columns_frame _ _ (Or.inl ha)

private theorem kept_tables {w K H G M b raw base : ℕ} (m : Memory w)
    (room : outputBase H G M b base < 2^w) :
    TablesOK H G M b base ((phase w K H G M b raw base).image m) := by
  have old := (prepared w H G M b base m room).2.1
  let n := H*chunks G M
  have endAddr : outputBase H G M b base = base+(2^b+2*span n) := rfl
  refine ⟨fun x=>?_,fun p=>?_,fun p=>?_⟩
  · exact (table_frame m _ (show base+x.val < outputBase H G M b base by have := x.isLt;omega)).trans (old.word x)
  · have h := (row H G M p).isLt.trans_le (span_ge n)
    exact (table_frame m _ (show base+2^b+(row H G M p).val < outputBase H G M b base by omega)).trans (old.actor p)
  · have h := (row H G M p).isLt.trans_le (span_ge n)
    exact (table_frame m _ (show base+2^b+span n+(row H G M p).val < outputBase H G M b base by omega)).trans (old.mask p)

private theorem take_true {α : Type} {cond : Prop} {d : Decidable cond} {x y z : α}
    (present : cond) (yes : x=z) : @ite α cond d x y=z := by
  cases d with
  | isTrue _ => exact yes
  | isFalse no => exact False.elim (no present)

private theorem take_false {α : Type} {cond : Prop} {d : Decidable cond} {x y z : α}
    (absent : ¬cond) (no : y=z) : @ite α cond d x y=z := by
  cases d with
  | isFalse _ => exact no
  | isTrue yes => exact False.elim (absent yes)

private theorem read_alternate {w K H G M b raw base ptr : ℕ}
    (β : Fin K→Fin H→Cell b) (alt : Fin H→Option (Fin H)) (m : Memory w)
    (stored : Raw raw β m) (tables : TablesOK H G M b base m) (pointers : Aliases ptr alt m)
    (rawRoom : raw+K*H+span H ≤ base) (ptrRoom : ptr+span H ≤ base)
    (space : outputBase H G M b base+K*(H*chunks G M) < 2^w) (bits : b*M ≤ w) (j : Fin K) :
    (alternate H G M b raw base ptr j.val).Fits w (outputBase H G M b base) ∧
    DescentPackedZip.Source (alternate H G M b raw base ptr j.val)
      (fun v (_ : Fin G) => (alt v).elim 0 (β j)) M m := by
  let n := H*chunks G M
  let out := outputBase H G M b base
  obtain ⟨fits, direct⟩ := runtime_word β m stored tables rawRoom space bits j
  change ((wideBank base b).Fits w out ∧ (rawBank raw H j.val).Fits w out ∧
    (actorBank base b n).Fits w out ∧ True) ∧ (maskBank base b n).Fits w out ∧ True at fits
  obtain ⟨⟨wf,rf,af,_⟩,mf,_⟩ := fits
  have oroom : out < 2^w := (Nat.le_add_right _ _).trans_lt space
  have baseBelow : base ≤ out := Nat.le_add_right ..
  have pf : (pointerBank ptr H).Fits w out :=
    ⟨span_pos _, by change span H < 2^w;omega, by change ptr+span H ≤ out;omega⟩
  have range : H < 2^w := (span_ge H).trans_lt pf.2.1
  refine ⟨⟨⟨pf,af,trivial⟩,trivial,trivial,⟨wf,rf,pf,af,trivial⟩,mf,trivial⟩,?_⟩
  intro p
  have ac (q : Row H G M) :
      (actorBank base b n).read m ((row H G M q).val : Word w)=(q.1.val : Word w) :=
    (DescentPackedZip.bank_read (actorBank base b n) m ((row H G M q).isLt.trans_le (span_ge n)) af).trans (tables.actor q)
  have mask (q : Row H G M) :
      (maskBank base b n).read m ((row H G M q).val : Word w)=(maskWord b M G q.2.val : Word w) :=
    (DescentPackedZip.bank_read (maskBank base b n) m ((row H G M q).isLt.trans_le (span_ge n)) mf).trans (tables.mask q)
  have ptrRead := (DescentPackedZip.bank_read (pointerBank ptr H) m (p.1.isLt.trans_le (span_ge H)) pf).trans (pointers p.1)
  cases h : alt p.1 with
  | none =>
    have empty : (data (fun v (_ : Fin G) => (alt v).elim 0 (β j)) p).val=0 := by
      change (finFunctionFinEquiv (fun i : Fin M =>
        if _ : p.2.val*M+i.val < G then (alt p.1).elim (0 : Cell b) (β j) else 0)).val=0
      simp [h]
    simp only [alternate,Expr.eval,Comparison.test]
    have hit : ((pointerBank ptr H).read m ((actorBank base b n).read m ((row H G M p).val : Word w)) == (H : Word w)) = true := by
      rw [ac p,ptrRead,h]
      simp
    apply take_true
    · exact hit
    · rw [empty]
  | some u =>
    have neq : ((u.val : Word w)==(H : Word w))=false := by
      apply beq_eq_false_iff_ne.mpr
      intro e
      have hval := congrArg Fin.val e
      rw [Fin.val_cast_of_lt (u.isLt.trans range),Fin.val_cast_of_lt range] at hval
      exact (Nat.ne_of_lt u.isLt) hval
    have fixed := direct (u,p.2)
    have same : data (fun v (_ : Fin G) => (alt v).elim 0 (β j)) p =
        data (fun v (_ : Fin G) => β j v) (u,p.2) := by simp only [data,h,Option.elim_some]
    rw [same]
    simp only [alternate,Expr.eval,Comparison.test]
    have miss : ¬((pointerBank ptr H).read m ((actorBank base b n).read m ((row H G M p).val : Word w)) == (H : Word w)) = true := by
      rw [ac p,ptrRead,h]
      simp only [Option.elim_some,neq,Bool.false_eq_true,not_false_eq_true]
    apply take_false
    · exact miss
    · simp only [n] at ac mask
      rw [ac p,ptrRead,h,Option.elim_some,mask p]
      simp only [body,Expr.eval] at fixed
      rw [ac (u,p.2),mask (u,p.2)] at fixed
      exact fixed

/-- The direct publisher pays once for the shape tables. Each subsequent alias lookup
uses one pointer word from the actor directory, shared across every field and group. -/
theorem alias_source {w K H G M b raw base ptr : ℕ} (β : Fin K→Fin H→Cell b)
    (alt : Fin H→Option (Fin H)) (m : Memory w) (stored : Raw raw β m) (pointers : Aliases ptr alt m)
    (rawRoom : raw+K*H+span H ≤ base) (ptrRoom : ptr+span H ≤ base)
    (space : outputBase H G M b base+K*(H*chunks G M) < 2^w) (bits : b*M ≤ w) (j : Fin K) :
    (alternate H G M b raw base ptr j.val).Fits w (outputBase H G M b base) ∧
    DescentPackedZip.Source (alternate H G M b raw base ptr j.val)
      (fun v (_ : Fin G) => (alt v).elim 0 (β j)) M ((phase w K H G M b raw base).image m) := by
  have frame := (run β m stored rawRoom space bits).2.2
  have rawStill : Raw raw β ((phase w K H G M b raw base).image m) := by
    intro k v
    have h := Nat.mul_le_mul_right H (Nat.le_of_lt k.isLt)
    have hv := v.isLt.trans_le (span_ge H)
    exact (frame _ (.inl (by omega))).trans (stored k v)
  have ptrStill : Aliases ptr alt ((phase w K H G M b raw base).image m) := by
    intro v
    have hv := v.isLt.trans_le (span_ge H)
    exact (frame _ (.inl (by omega))).trans (pointers v)
  exact read_alternate β alt _ rawStill (kept_tables m ((Nat.le_add_right _ _).trans_lt space))
    ptrStill rawRoom ptrRoom space bits j

end
end Hierarchy.DescentResetStemHeaders

end OAI
