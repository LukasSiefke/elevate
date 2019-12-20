package shine.DPIA.FunctionalPrimitives

import shine.DPIA.Compilation.TranslationContext
import shine.DPIA._
import shine.DPIA.DSL._
import shine.DPIA.Phrases._
import shine.DPIA.Semantics.OperationalSemantics
import shine.DPIA.Semantics.OperationalSemantics.Store
import shine.DPIA.Types._

import scala.xml.Elem

final case class Gather(n: Nat, m: Nat, dt: DataType,
                        indices: Phrase[ExpType],
                        input: Phrase[ExpType])
  extends ExpPrimitive
{
  override val t: ExpType =
    (n: Nat) ->: (m: Nat) ->: (dt: DataType) ->:
      (indices :: exp"[$m.idx($n), $read]") ->:
      (input :: exp"[$n.$dt, $read]") ->:
      exp"[$m.$dt, $read]"

  override def visitAndRebuild(f: VisitAndRebuild.Visitor): Phrase[ExpType] =
    Gather(f.nat(n), f.nat(m), f.data(dt),
      VisitAndRebuild(indices, f),
      VisitAndRebuild(input, f))

  override def eval(s: Store): OperationalSemantics.Data = ???

  override def acceptorTranslation(A: Phrase[AccType])(implicit context: TranslationContext): Phrase[CommType] =
    throw new Exception("this should not happen")

  override def continuationTranslation(C: Phrase[ExpType ->: CommType])(implicit context: TranslationContext): Phrase[CommType] = {
    import shine.DPIA.Compilation.TranslationToImperative._

    con(indices)(fun(exp"[$m.idx($n), $read]")(y =>
      con(input)(fun(exp"[$n.$dt, $read]")(x =>
        C(Gather(n, m, dt, y, x))
      ))
    ))
  }

  override def prettyPrint: String = s"(gather ${PrettyPhrasePrinter(indices)} ${PrettyPhrasePrinter(input)})"

  override def xmlPrinter: Elem =
    <gather>
      <indices>{Phrases.xmlPrinter(indices)}</indices>
      <input>{Phrases.xmlPrinter(input)}</input>
    </gather>
}
