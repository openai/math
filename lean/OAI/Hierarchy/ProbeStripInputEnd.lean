import OAI.Hierarchy.ProbeStripFormat
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Prefix endpoints of the actual purchased and payload strip failure readers -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe PurchaseStage ProbeStage PurchaseFrozen
open Calendar.StockCommit
open scoped Classical

variable {z d k n q w cut : ℕ} {E A : Type*} [Fintype A]

structure Channels.Before (c : Channels A E) (cut : ℕ) : Prop where
  address : ∀a,(c.address a).inputEnd≤cut
  live : c.live.inputEnd≤cut

private theorem substitute (x a : Expr) (endX : x.inputEnd≤cut) (endA : a.inputEnd≤cut) :
    (x.atRow a).inputEnd≤cut := by
  induction x <;> simp_all [Expr.atRow,Expr.inputEnd]

private theorem choice (n start : ℕ) (xs : Fin n→Expr) (which : Expr)
    (known : ∀i,(xs i).inputEnd≤cut) (read : which.inputEnd≤cut) :
    (chooseField n start xs which).inputEnd≤cut := by
  induction n generalizing start with
  | zero=>simp [chooseField,Expr.inputEnd]
  | succ n ih=>
    simp only [chooseField,Expr.inputEnd,max_le_iff]
    exact ⟨⟨read,Nat.zero_le _⟩,known 0,ih _ _ (fun i=>known i.succ)⟩

private theorem scaled (n : ℕ) (x : Expr) (read : x.inputEnd≤cut) :
    (scale n x).inputEnd≤cut := by
  induction n with
  | zero=>simp [scale,Expr.inputEnd]
  | succ n ih=>simpa only [scale,Expr.inputEnd,max_le_iff] using And.intro read ih

private theorem digits (radix : ℕ) (xs : List Expr) (read : ∀x∈xs,x.inputEnd≤cut) :
    (menuKey radix xs).inputEnd≤cut := by
  induction xs with
  | nil=>simp [menuKey,Expr.inputEnd]
  | cons x xs ih=>
    change max x.inputEnd (scale radix (menuKey radix xs)).inputEnd≤cut
    exact max_le (read _ List.mem_cons_self) (scaled _ _ (ih (fun y hy=>read y (List.mem_cons_of_mem _ hy))))

theorem payload_before (z n k cut : ℕ) : (payloadChannels z n k).Before cut := by
  constructor
  · rintro (u|⟨j,a⟩) <;> simp [payloadChannels,payloadSlot,Expr.inputEnd]
  · simp [payloadChannels,Expr.inputEnd]

/-- The retained DFS tile-source pages, the flag bank and the two public
key/candidate ordinal words are the only additional purchased-strip inputs. -/
theorem purchased_before (sh : Shelf) (S : PurchaseSampler) (depth start cut : ℕ)
    (source : ∀key : Key z d k,
      (sh.L S depth key).source.base+(sh.L S depth key).source.size≤cut)
    (flag : (flagBank sh S z d k depth).base+(flagBank sh S z d k depth).size≤cut)
    (directory : let h:=stratumHeader z d k S.degree depth start
      h.ball.base+h.ball.size≤cut ∧ h.field.base+h.field.size≤cut) :
    (purchasedChannels (z:=z) (d:=d) (k:=k) sh S depth start).Before cut := by
  let h:=stratumHeader z d k S.degree depth start
  constructor
  · intro a
    change (allChainSlot sh S depth h a).inputEnd≤cut
    unfold allChainSlot
    apply choice
    · intro key
      apply substitute
      · simpa [keySlot,chainSlot,tile,Expr.inputEnd] using source key
      · simpa [PortHeader.fieldTerm,Expr.inputEnd] using directory.2
    · simpa [PortHeader.ballTerm,Expr.inputEnd] using directory.1
  · simpa [purchasedChannels,Expr.inputEnd] using flag

/-- The failure word for either native strip geometry is a genuine prefix
reader at the chosen event cutoff, including its retained geometry flags. -/
theorem Channels.Before.failure_fits (c : Channels A E) (hc : c.Before cut)
    (test : StripTest (Fintype.card A)) (price offsets stocks : Bank) (rows population : ℕ)
    (priceEnd : price.base+price.size≤cut) (offEnd : offsets.base+offsets.size≤cut)
    (stockEnd : stocks.base+stocks.size≤cut) (discEnd : test.table.base+test.table.size≤cut)
    (word : cut<2^w) :
    (tested {test with live:=c.live, rows:=rows, population:=population} price offsets stocks c.digit).failure.effective.Fits w cut := by
  apply Expr.fits_of_inputEnd _ _ word
  change max (max c.live.inputEnd 0) (max 0 (max (test.table.base+test.table.size)
    (menuKey test.radix (List.ofFn (quoted price offsets stocks c.digit))).inputEnd))≤cut
  rw [max_zero,zero_max]
  refine max_le hc.live (max_le discEnd (digits _ _ ?_))
  intro e he
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
  apply substitute
  · simp [AttemptGate.valueTerm,Expr.inputEnd,priceEnd,offEnd,stockEnd]
  · exact hc.address _

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
