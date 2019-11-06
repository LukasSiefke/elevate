package idealised.DPIA.FunctionalPrimitives

import idealised.DPIA.Compilation.{TranslationContext, TranslationToImperative}
import idealised.DPIA.DSL._
import idealised.DPIA.ImperativePrimitives.MapFstAcc
import idealised.DPIA.Phrases._
import idealised.DPIA.Semantics.OperationalSemantics
import idealised.DPIA.Semantics.OperationalSemantics._
import idealised.DPIA.Types._
import idealised.DPIA._

import scala.language.reflectiveCalls
import scala.xml.Elem

final case class MapFst(dt1: DataType,
                        dt2: DataType,
                        dt3: DataType,
                        f: Phrase[ExpType ->: ExpType],
                        record: Phrase[ExpType]) extends ExpPrimitive
{

  override val t: ExpType =
    (dt1: DataType) ->: (dt2: DataType) ->: (dt3: DataType) ->:
      (f :: exp"[$dt1, $read]" ->: exp"[$dt3, $read]") ->:
      (record :: exp"[$dt1 x $dt2, $read]") ->: exp"[$dt3 x $dt2, $read]"

  override def eval(s: Store): Data = {
    val fE = OperationalSemantics.eval(s, f)
    OperationalSemantics.eval(s, record) match {
      case r: PairData => PairData(OperationalSemantics.eval(s, fE(Literal(r.fst))), r.snd)
      case _ => throw new Exception("This should not happen")
    }
  }

  override def visitAndRebuild(fun: VisitAndRebuild.Visitor): Phrase[ExpType] = {
    MapFst(fun.data(dt1), fun.data(dt2), fun.data(dt3),
      VisitAndRebuild(f, fun),
      VisitAndRebuild(record, fun))
  }

  override def prettyPrint: String = s"(mapFst ${PrettyPhrasePrinter(f)} ${PrettyPhrasePrinter(record)})"

  override def xmlPrinter: Elem =
    <mapFst dt1={ToString(dt1)} dt2={ToString(dt2)} dt3={ToString(dt3)}>
      <f>{Phrases.xmlPrinter(f)}</f>
      <record>{Phrases.xmlPrinter(record)}</record>
    </mapFst>

  override def fedeTranslation(env: scala.Predef.Map[Identifier[ExpType], Identifier[AccType]])
                              (C: Phrase[AccType ->: AccType]) : Phrase[AccType] = {
    import TranslationToImperative._

    val x = Identifier(freshName("fede_x"), ExpType(dt1, read))

    val otype = AccType(dt3)
    val o = Identifier(freshName("fede_o"), otype)

    fedAcc(env)(record)(fun(env.toList.head._2.t)(y =>
      MapFstAcc(dt1, dt2, dt3,
        Lambda(o, fedAcc(scala.Predef.Map(x -> o))(f(x))(fun(otype)(x => x))),
        C(y))))
  }

  override def acceptorTranslation(A: Phrase[AccType])
                                  (implicit context: TranslationContext): Phrase[CommType] = {
    import TranslationToImperative._

    val x = Identifier(freshName("fede_x"), ExpType(dt1, read))

    val otype = AccType(dt3)
    val o = Identifier(freshName("fede_o"), otype)

    acc(record)(MapFstAcc(dt1, dt2, dt3,
      Lambda(o, fedAcc(scala.Predef.Map(x -> o))(f(x))(fun(otype)(x => x))),
      A))
  }

  override def continuationTranslation(C: Phrase[ExpType ->: CommType])
                                      (implicit context: TranslationContext): Phrase[CommType] = {
    import TranslationToImperative._

    // assumption: f does not need to be translated, it does indexing only
    con(record)(fun(record.t)(x => C(MapFst(dt1, dt2, dt3, f, x))))
  }
}
