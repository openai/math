import OAI.Hierarchy.DescentNamedEarnedCalendarRates
import OAI.Hierarchy.DescentTerminalEarnedFrontier

namespace OAI
/-! # One terminal address exponent before selecting the calendar and the aperture -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook ProtocolRAM
open AddressPlan DescentTerminalVertexFields
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset n depth C : ℕ)


variable (op : RotorSpec) (drift : ℕ)

theorem earned_last_uniform (branch : G.b≤2^(capRate G t g)) :
    ∃rate : ℕ,∀τ B : ℕ, 20≤B → 2*localSocketRate G t g≤τ →
      2*(localSocketRate G t g+(τ+groupRate G t f g reset+4))+Nat.clog 2 G.b*(t+1)≤B →
      2*((τ+groupRate G t f g reset+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2)≤B →
      2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B →
      2*bookRate G t f g reset τ≤B →
      ∀ᶠ height:ℕ in atTop,∀(x : ShellSource F height) (L : TerminalPlacement),
        let J:=Nat.log 2 height/(2*B)
        let S:=stageNumbers G t J f g reset x.sites (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let W:=NativeBranch.binLimit (k:=k) S
        let q:=2^Nat.clog 2 (NativeBranch.localLimit G S)*(G.b^(t*J)*G.b)
        let p:=W*(height/(16*(q*W)))
        let cfg:=earnedShell G t f g reset τ B n depth C x L
        let I:=earnedInput G t f g reset τ B n depth C op drift x L
        ∀(channels : MaskAllocation.Channels S.radix) (start : ℕ),
          last (earnedFormat G op S q p drift) cfg I channels start≤ start+2^(rate*height) :=by
  obtain ⟨R,uniform⟩:=uniform_shell_address G t f g reset n depth C
  let U:=max 1 R
  refine ⟨U+12,?_⟩
  intro τ B big reserve packing router cohorts books
  filter_upwards [uniform τ B,earned_tables G op drift t f g reset τ B branch big reserve packing router cohorts books,
    earned_field_rate G op drift t f g reset τ B branch (by omega) cohorts,
    native_format_widths G t f g reset τ B (by omega) router,early_matrix_words G t f g reset τ B big,
    eventually_ge_atTop 1] with h sized menus fieldBudget widths matrix positive
  intro x loc J S k W q p cfg I channels start
  let E:=2^(U*h)
  have rp : 2^(R*h)≤E:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (le_max_right 1 R))
  have page : 2^h≤E:=Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_left h (show 0<U from le_max_left 1 R))
  have axes:=sized x
  have tables:=earned_counts_at G t f g reset τ B n depth C op drift x loc (menus x.sites)
  obtain ⟨_,_,ps,qs,_,_⟩:=widths x.sites
  have field : 32*fieldSum (earnedFormat G op S q p drift) S.radix≤h:=fieldBudget x.sites p q ps qs
  let dim:=S.groupWidth k (tail τ J) 0+k
  have square : 4*(dim*dim+dim+1)≤h:=(matrix x.sites).2.2
  have kd : k≤dim:=Nat.le_add_left _ _
  have radix : S.radix≤E:=(Nat.pow_le_pow_right (by decide) (show k≤h by omega)).trans page
  obtain ⟨sites,pool,raw,pub,head⟩:=shell_word_fields G t f g reset τ B n depth C x loc axes
  have shared : last (earnedFormat G op S q p drift) cfg I channels start≤ start+4096*E:=
    tables.last_le _ channels start page (by omega) radix (sites.trans rp) (pool.trans rp)
      (raw.trans rp) (pub.trans rp) (head.trans rp)
  have pay : 4096*E≤2^((U+12)*h):=calc
    4096*E=2^(12+U*h):=(pow_add (2:ℕ) 12 (U*h)).symm
    _≤_:=Nat.pow_le_pow_right (by decide) (by rw [Nat.add_mul];omega)
  exact shared.trans (Nat.add_le_add_left pay _)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
