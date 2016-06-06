package AccPatterns

import Core.OperationalSemantics._
import Core._

case class ToLocalAcc(p: Phrase[AccType]) extends AccPattern{

  override def typeCheck(): AccType = {
    import TypeChecker._
    TypeChecker(p) match {
      case AccType(dt) => AccType(dt)
      case x => error(x.toString, "AccType")
    }
  }

  override def eval(s: Store): AccIdentifier = ???

  override def toC: String = ???

  override def substitute[T <: PhraseType](phrase: Phrase[T], `for`: Phrase[T]): AccPattern = {
    ToLocalAcc(OperationalSemantics.substitute(phrase, `for`, p))
  }

  override def prettyPrint: String = s"(toLocalAcc ${PrettyPrinter(p)})"
}