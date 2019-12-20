package shine.OpenCL.IntermediatePrimitives

import shine.DPIA.Compilation.TranslationContext
import shine.DPIA.DSL.{λ, _}
import shine.DPIA.Phrases.Phrase
import shine.DPIA.Types.{AccType, CommType, DataType, ExpType, read}
import shine.DPIA._
import shine.OpenCL.ImperativePrimitives.ParForWorkGroup
import shine.OpenCL.AddressSpace
import shine._

final case class MapWorkGroupI(dim: Int) {
  def apply(n: Nat, dt1: DataType, dt2: DataType,
            f: Phrase[ExpType ->: AccType ->: CommType],
            in: Phrase[ExpType],
            out: Phrase[AccType])
           (implicit context: TranslationContext): Phrase[CommType] =
  {
    comment("mapWorkgroup")`;`
    ParForWorkGroup(dim)(n, dt2, out, λ(exp"[idx($n), $read]")(i => λ(acc"[$dt2]")(a => {

      //      val access = (out `@` 0) `@` 0 // TODO: this is totally not generic ...
      //      TypeChecker(access)
      //      val identifier = ToOpenCL.acc(access, new ToOpenCL(?, ?))
      //      val addressSpace = env.addressspace(identifier.name)
      val addressSpace = AddressSpace.Global // FIXME: address space of 'a'

      f(in `@` i)(a)
    })))
  }
}
