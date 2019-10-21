package idealised.DPIA.FunctionalPrimitives

import idealised.DPIA.Compilation.{TranslationContext, TranslationToImperative}
import idealised.DPIA.DSL._
import idealised.DPIA.ImperativePrimitives.UnzipAcc
import idealised.DPIA.Phrases._
import idealised.DPIA.Semantics.OperationalSemantics
import idealised.DPIA.Semantics.OperationalSemantics._
import idealised.DPIA.Types._
import idealised.DPIA.{Phrases, _}

import scala.language.reflectiveCalls
import scala.xml.Elem

final case class Unzip(n: Nat,
                       dt1: DataType,
                       dt2: DataType,
                       e: Phrase[ExpType])
  extends ExpPrimitive {

  override val t: ExpType =
    (n: Nat) ->: (dt1: DataType) ->: (dt2: DataType) ->:
      (e :: exp"[$n.($dt1 x $dt2), $read]") ->:
      ExpType(PairType(ArrayType(n, dt1), ArrayType(n, dt2)), read)

  // TODO: fix parsing of this:
//        exp"[($n.$dt1 x $n.$dt2)]"

  override def visitAndRebuild(f: VisitAndRebuild.Visitor): Phrase[ExpType] = {
    Unzip(f.nat(n), f.data(dt1), f.data(dt2), VisitAndRebuild(e, f))
  }

  override def eval(s: Store): Data = {
    OperationalSemantics.eval(s, e) match {
      case ArrayData(xs) =>
        val (lhs, rhs) = xs.foldLeft(Vector[Data](), Vector[Data]()){
          case (vs: (Vector[Data], Vector[Data]), p: PairData) =>
            (vs._1 :+ p.fst, vs._2 :+ p.snd)
          case _ => throw new Exception("This should not happen")
        }
        PairData(ArrayData(lhs), ArrayData(rhs))

      case _ => throw new Exception("This should not happen")
    }
  }

  override def prettyPrint: String = s"(unzip ${PrettyPhrasePrinter(e)})"

  override def xmlPrinter: Elem =
    <unzip n={ToString(n)} dt1={ToString(dt1)} dt2={ToString(dt2)}>
      <e type={ToString(ExpType(ArrayType(n, dt1), read))}>
        {Phrases.xmlPrinter(e)}
      </e>
    </unzip>

  override def acceptorTranslation(A: Phrase[AccType])
                                  (implicit context: TranslationContext): Phrase[CommType] = {
    import TranslationToImperative._

    con(e)(λ(exp"[$n.($dt1 x $dt2), $read]")(x =>
      A :=|PairType(ArrayType(n, dt1), ArrayType(n, dt2))| Unzip(n, dt1, dt2, x)
    ))
  }

  override def continuationTranslation(C: Phrase[ExpType ->: CommType])
                                      (implicit context: TranslationContext): Phrase[CommType] = {
    import TranslationToImperative._

    con(e)(λ(exp"[$n.($dt1 x $dt2), $read]")(x =>
      C(Unzip(n, dt1, dt2, x)) ))
  }
}