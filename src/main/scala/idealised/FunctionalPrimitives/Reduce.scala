package idealised.FunctionalPrimitives

import idealised._
import idealised.Core._
import idealised.Core.OperationalSemantics._
import idealised.Compiling.RewriteToImperative
import idealised.DSL.typed._
import idealised.IntermediatePrimitives.ReduceI

import scala.xml.Elem

abstract class AbstractReduce(n: Nat,
                              dt1: DataType,
                              dt2: DataType,
                              f: Phrase[ExpType -> (ExpType -> ExpType)],
                              init: Phrase[ExpType],
                              array: Phrase[ExpType])
  extends ExpPrimitive {

  def makeReduce: (Nat, DataType, DataType, Phrase[ExpType -> (ExpType -> ExpType)], Phrase[ExpType], Phrase[ExpType]) => AbstractReduce

  def makeReduceI: (Nat, DataType, DataType, Phrase[ExpType -> (ExpType -> (AccType -> CommandType))], Phrase[ExpType], Phrase[ExpType], Phrase[ExpType -> CommandType]) => ReduceI

  override lazy val `type` = exp"[$dt2]"

  override def typeCheck(): Unit = {
    import TypeChecker._
    (n: Nat) -> (dt1: DataType) -> (dt2: DataType) ->
      (f :: t"exp[$dt1] -> exp[$dt2] -> exp[$dt2]") ->
      (init :: exp"[$dt2]") ->
      (array :: exp"[$n.$dt1]") ->
      `type`
  }

  override def inferTypes: AbstractReduce = {
    import TypeInference._
    val array_ = TypeInference(array)
    val init_ = TypeInference(init)
    (init_.t, array_.t) match {
      case (ExpType(dt2_), ExpType(ArrayType(n_, dt1_))) =>
        val f_ = TypeInference.setParamsAndInferTypes(f, exp"[$dt1_]", exp"[$dt2_]")
        f_.t match {
          case FunctionType(ExpType(t1), FunctionType(ExpType(t2), ExpType(t3))) =>
            if (dt1_ == t1 && dt2_ == t2 && dt2_ == t3) {
              makeReduce(n_, dt1_, dt2_, f_, init_, array_)
            } else {
              error(dt1_.toString + ", " + t1.toString + " as well as " +
                dt2_.toString + ", " + t2.toString + " and " + t3.toString,
                expected = "them to match")
            }
          case x => error(x.toString, "FunctionType")
        }
      case x => error(x.toString, "(ExpType, ArrayType)")
    }
  }

  override def visitAndRebuild(fun: VisitAndRebuild.Visitor): Phrase[ExpType] = {
    makeReduce(fun(n), fun(dt1), fun(dt2), VisitAndRebuild(f, fun), VisitAndRebuild(init, fun), VisitAndRebuild(array, fun))
  }

  override def eval(s: Store): Data = {
    val fE = OperationalSemantics.eval(s, f)(BinaryFunctionEvaluator)
    val initE = OperationalSemantics.eval(s, init)
    OperationalSemantics.eval(s, array) match {
      case ArrayData(xs) =>
        ArrayData(Vector(xs.fold(initE) {
          (x, y) => OperationalSemantics.eval(s,
            fE(Literal(x, x.dataType))(Literal(y, y.dataType)))
        }))
      case _ => throw new Exception("This should not happen")
    }
  }

  override def prettyPrint: String =
    s"(${this.getClass.getSimpleName} ${PrettyPhrasePrinter(f)} ${PrettyPhrasePrinter(init)} ${PrettyPhrasePrinter(array)})"

  override def rewriteToImperativeAcc(A: Phrase[AccType]): Phrase[CommandType] = {
    import RewriteToImperative._

    assert(n != null && dt1 != null && dt2 != null)

    con(array)(λ(exp"[$n.$dt1]")(x =>
      con(init)(λ(exp"[$dt2]")(y =>
        makeReduceI(n, dt1, dt2,
          λ(exp"[$dt1]")(x => λ(exp"[$dt2]")(y => λ(acc"[$dt2]")(o =>
            acc( f(x)(y) )( o )))),
          y, x, λ(exp"[$dt2]")(r => acc(r)(A)))))))
  }

  override def rewriteToImperativeCon(C: Phrase[ExpType -> CommandType]): Phrase[CommandType] = {
    import RewriteToImperative._

    assert(n != null && dt1 != null && dt2 != null)

    con(array)(λ(exp"[$n.$dt1]")(x =>
      con(init)(λ(exp"[$dt2]")(y =>
        makeReduceI(n, dt1, dt2,
          λ(exp"[$dt1]")(x => λ(exp"[$dt2]")(y => λ(acc"[$dt2]")(o =>
            acc( f(x)(y) )( o ) ))),
          y, x, C)))))
  }

  override def xmlPrinter: Elem =
    <reduce n={ToString(n)} dt1={ToString(dt1)} dt2={ToString(dt2)}>
      <f type={ToString(ExpType(dt1) -> (ExpType(dt2) -> ExpType(dt2)))}>
        {Core.xmlPrinter(f)}
      </f>
      <init type={ToString(ExpType(dt2))}>
        {Core.xmlPrinter(init)}
      </init>
      <input type={ToString(ExpType(ArrayType(n, dt1)))}>
        {Core.xmlPrinter(array)}
      </input>
    </reduce>.copy(label = {
      val name = this.getClass.getSimpleName
      Character.toLowerCase(name.charAt(0)) + name.substring(1)
    })
}

final case class Reduce(n: Nat,
                        dt1: DataType,
                        dt2: DataType,
                        f: Phrase[ExpType -> (ExpType -> ExpType)],
                        init: Phrase[ExpType],
                        array: Phrase[ExpType])
  extends AbstractReduce(n, dt1, dt2, f, init, array) {
  override def makeReduce = Reduce

  override def makeReduceI = ReduceI
}

