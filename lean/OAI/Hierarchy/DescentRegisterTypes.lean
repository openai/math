import OAI.Hierarchy.DescentDatedOperandHeader
import OAI.Hierarchy.DescentStageVenueDate

namespace OAI
/-! # Public addresses and widths retained between arithmetic descent dates -/
namespace Hierarchy.DescentDatedAddressBook
open ProtocolRAM

structure PriorRolePages where
  first : ℕ
  stride : ℕ
  bits : ℕ
  blocks : ℕ

structure PriorResetArchive where
  nodeBase : ℕ
  arguments : ℕ
  seed : Bool
  roles : PriorRolePages
  count : Bank

end Hierarchy.DescentDatedAddressBook

namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage

structure DatePorts where
  archive : PriorResetArchive
  venue : StageVenueTail.Date
  io : Dated.Operands
  operandBits : ℕ
  operandLanes : ℕ
  argumentsPerNode : ℕ
  nodes : ℕ
  roleLanes : ℕ
  /-- Physical height of the archived seven operand pages. -/
  operandHosts : ℕ
  /-- Width of one primitive token in the recorded archive. -/
  tokenBits : ℕ

end Hierarchy.DescentSixParty.Chronology

end OAI
