package LowLevelCombinators

import Core.OperationalSemantics._
import Core._

import scala.xml.Elem

case class SplitAcc(n: Nat,
                    m: Nat,
                    dt: DataType,
                    array: Phrase[AccType])
  extends LowLevelAccCombinator {

  override lazy val `type` = acc"[${n * m}.$dt]"

  override def typeCheck(): Unit = {
    import TypeChecker._
    (n: Nat) -> (m: Nat) -> (dt: DataType) ->
      (array `:` acc"[$m.$n.$dt]") -> `type`
  }

  override def visitAndRebuild(fun: VisitAndRebuild.fun): Phrase[AccType] = {
    SplitAcc(fun(n), fun(m), fun(dt), VisitAndRebuild(array, fun))
  }

  override def eval(s: Store): AccIdentifier = ???

  override def prettyPrint: String = s"(splitAcc ${PrettyPrinter(array)})"

  override def xmlPrinter: Elem =
    <splitAcc n={ToString(n)} m={ToString(m)} dt={ToString(dt)}>
      {Core.xmlPrinter(array)}
    </splitAcc>
}
