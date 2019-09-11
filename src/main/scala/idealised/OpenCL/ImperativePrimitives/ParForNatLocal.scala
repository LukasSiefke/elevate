package idealised.OpenCL.ImperativePrimitives

import idealised.C.AST.Stmt
import idealised.DPIA.Phrases.Phrase
import idealised.DPIA.Types.{AccType, CommType, NatToData}
import idealised.DPIA.{->:, Nat, `(nat)->:`, freshName}
import idealised.OpenCL
import idealised.OpenCL.AST.Barrier
import idealised.OpenCL.{BuiltInFunction, get_local_id, get_local_size}
import lift.arithmetic.{?, ContinuousRange, PosInf, RangeAdd}

final case class ParForNatLocal(dim:Int)(override val n:Nat,
                                         override val ft:NatToData,
                                         override val out:Phrase[AccType],
                                         override val body: Phrase[`(nat)->:`[AccType ->: CommType]],
                                         init: Nat = get_local_id(dim),
                                         step: Nat = get_local_size(dim),
                                         unroll: Boolean = false)
  extends OpenCLParForNat(n, ft, out, body, init, step, unroll) {

  def makeParForNat =
    (n, ft, out, body) => ParForNatLocal(dim)(n, ft, out, body, init, step, unroll)

  override val parallelismLevel = OpenCL.Local

  override val name: String = freshName("l_id_")

//  lazy val local_size_range: RangeAdd = ContinuousRange(1, PosInf)
  //    if (env.localSize == ?) ContinuousRange(1, PosInf)
  //    else RangeAdd(env.localSize, env.localSize + 1, 1)

  override def synchronize: Stmt = Barrier(local = true, global = true)
}
